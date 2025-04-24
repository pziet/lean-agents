"""
All agent implementations in a single file with enhanced event bus visibility.
"""
import os
import re
import requests
import json
from abc import ABC, abstractmethod
from pydantic import BaseModel
import random
import time
from typing import Optional, List, Dict, Any, Set
import openai

from .event_bus import EventBus
from .lean_interface import LeanInterface

import logging

logger = logging.getLogger(__name__)

LEMMA_SELECTION_SYSTEM_PROMPT = """
    You are a theorem-proving assistant who gives proofs for lemmas in Lean 4. You job is to select the next lemma to work on.
"""

PROOF_SYSTEM_PROMPT = """
    You are a theorem-proving assistant who gives proofs for lemmas in Lean 4.

    - If the file is a definition, i.e. a `Prop`, then you can simply restate as it is given in the file since there is nothing to prove. For example, `def myDefinition`
    - You only return Lean 4 code which can be parsed by the Lean 4 parser, nothing else. Make sure to include all necessary imports.
    - This set of lemmas can be related, for example Lemma 1 might be used in the proof of Lemma 2. In this case you can simply import Lemma 1 even if it is not yet proven since we use Lean 4's "sorry" tactic to fill in the proof. This will allow you to build up a proof incrementally and not necessarily sequentially.
"""


class LemmaSelection(BaseModel):
    lemma_id: str

class ProofAttempt(BaseModel):
    proof: str

class ExtractLeanProof(BaseModel):
    proof: str

class BaseAgent(ABC):
    """Base abstract class for all agents."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface, strategy: str):
        self.agent_id = agent_id
        self.event_bus = event_bus
        self.lean_interface = lean_interface
        self.strategy = strategy
        self.proven_lemmas: Set[str] = set()
        self.current_lemma: Optional[str] = None
        
        # Subscribe to all relevant events
        self.event_bus.subscribe("LemmaProven", self.on_lemma_proven)
        self.event_bus.subscribe("LemmaAttemptFailed", self.on_lemma_attempt_failed)
        self.event_bus.subscribe("AgentWorking", self.on_agent_working)
    
    def get_event_bus_state(self) -> Dict[str, Any]:
        """
        Get a snapshot of the current event bus state, including:
        - What other agents are working on
        - Failed proof attempts
        - Successful proofs
        
        Returns:
            Dictionary with relevant event bus information
        """
        current_activities = self.event_bus.get_current_agent_activities()
        
        # Get recent failed attempts
        failed_attempts = []
        for event in self.event_bus.get_history("LemmaAttemptFailed").get("LemmaAttemptFailed", []):
            failed_attempts.append(event["data"])
        
        # Get proven lemmas
        proven_lemmas = []
        for event in self.event_bus.get_history("LemmaProven").get("LemmaProven", []):
            proven_lemmas.append(event["data"])
        
        return {
            "current_activities": current_activities,
            "failed_attempts": failed_attempts,
            "proven_lemmas": proven_lemmas
        }
    
    @abstractmethod
    def pick_lemma(self) -> Optional[str]:
        """Select a lemma to work on."""
        pass
    
    @abstractmethod
    def attempt_proof(self, lemma_id: str) -> bool:
        """Attempt to prove the given lemma. Return True if successful."""
        pass
    
    def _format_event_history(self, event_history: Dict) -> str:
        """Format the event history in a readable way."""
        history_str = ""
        for event_type, events in event_history.items():
            history_str += f"\n## {event_type} Events:\n"
            for event in events:
                timestamp = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(event["timestamp"]))
                data = event["data"]
                history_str += f"- {timestamp}: {str(data)}\n"
        return history_str
    
    def _format_proven_lemmas(self) -> str:
        """Format the proven lemmas in a readable way."""
        return "\n".join([
            f"{i+1}. {lemma}\n"
            f"-----------------------------\n"
            f"{self.lean_interface.get_file(lemma, 'proven')}"
            for i, lemma in enumerate(self.proven_lemmas)
        ])

    def _create_simple_lemma_selection_prompt(self, available_lemmas, current_activities, event_history):
        """Create a simple prompt with the raw event history."""
        # Format available lemmas
        available_lemmas_str = "\n".join([
            f"{i+1}. {lemma}\n"
            f"-----------------------------\n"
            f"{self.lean_interface.get_file(lemma, 'stubs')}"
            for i, lemma in enumerate(available_lemmas)
        ])
        
        prompt = f"""
        As a theorem-proving assistant, your task is to select the next lemma to work on. 
        # Available Lemmas
        {available_lemmas}

        <Available Lemmas and their stubs>
        {available_lemmas_str}
        </Available Lemmas and their stubs>
        """
        if self.strategy == "polanyi":
            # Format proven lemmas
            proven_lemmas_str = self._format_proven_lemmas()
            # Format current agent activities
            current_activities_str = "\n".join([
                f"- Agent {agent_id} is working on {lemma_id}" 
                for agent_id, lemma_id in current_activities.items()
                if agent_id != self.agent_id
            ]) or "No other agents are currently working on lemmas."
            
            # Format event history in a readable way
            history_str = self._format_event_history(event_history)

            prompt += f"""
            <Proven Lemmas and their proofs>
            {proven_lemmas_str if proven_lemmas_str else "No lemmas have been proven yet."}
            </Proven Lemmas and their proofs>

            <Current Agent Activities>
            {current_activities_str}
            </Current Agent Activities>

            <Complete Event History>
            {history_str if history_str else "No event history yet."}
            </Complete Event History>
            Based on this complete event history, please select the most strategic lemma for me (Agent {self.agent_id}) to work on next.
            Consider factors like:
            1. Avoid lemmas other agents are already working on
            2. Consider lemmas that had failed attempts but might benefit from your approach
            3. Look for lemmas that might build upon recently proven lemmas

            Respond with only the lemma name."
            """
        return prompt
    
    def _create_proof_attempt_prompt(self, lemma_id: str, stub_file: str, event_history: Dict) -> str:
        """Create a detailed prompt for proof generation using event history."""

        prompt = f"""
        Generate a proof for lemma {lemma_id} in Lean 4. If it is a definition, i.e. a `Prop`, then you can simply restate as it is given in the file since there is nothing to prove. For example, `def myDefinition`

        Here is a stub file of the lemma, make sure to use it as a starting point:

        {stub_file}
        """
        if self.strategy == "polanyi":
            history_str = self._format_event_history(event_history)
            proven_lemmas_str = self._format_proven_lemmas()
            prompt += f"""
            - You are an agent in a team of agents that are collectively proving a set of lemmas, so I will also show you a full event history of the team's progress so far including any failed proof attempts.
            - Avoid lemmas that other agents are already working on.

            Here is a complete event history of the team's progress so far which you can use to inform your proof:
            1. Review any failed attempts to avoid repeating unsuccessful approaches
            2. Analyze successful proofs of related lemmas for useful tactics
            3. Consider the current state of proven lemmas that might be helpful


            <Event History>
            {history_str}
            </Event History>

            Here are the lemmas that have been proven so far:
            <Proven Lemmas>
            {proven_lemmas_str}
            </Proven Lemmas>
            """
        logger.info("Generated proof attempt prompt:\n%s", prompt)
        return prompt

    def on_lemma_proven(self, data: dict) -> None:
        """Handle notification that a lemma has been proven."""
        lemma_id = data.get("lemma_id")
        agent_id = data.get("agent_id")
        
        if lemma_id and agent_id != self.agent_id:
            logger.info("Agent %s notified that %s was proven by %s", self.agent_id, lemma_id, agent_id)
            
            # If this was our current lemma, pick a new one
            if self.current_lemma == lemma_id:
                self.current_lemma = None
                self.pick_lemma()
    
    def on_lemma_attempt_failed(self, data: dict) -> None:
        """Handle notification that a lemma attempt failed."""
        # Optional: Handle failed attempts by other agents
        pass
    
    def on_agent_working(self, data: dict) -> None:
        """Handle notification that an agent is working on a lemma."""
        # Optional: Handle information about what other agents are working on
        pass
    
    def publish_proof(self, lemma_id: str, proof: str) -> None:
        """Publish a successful proof to the shared folder and notify others."""
        # Save the proof to the proven directory
        filepath = self.lean_interface.save_proven_lemma(lemma_id, proof)
        if filepath:
            logger.info("Agent %s proved lemma: %s", self.agent_id, lemma_id)
            # Notify other agents
            self.event_bus.publish("LemmaProven", {
                "lemma_id": lemma_id,
                "proof": proof,
                "agent_id": self.agent_id,
                "filepath": filepath
            })
        
            # Update our own record
            self.proven_lemmas.add(lemma_id)
        else:
            logger.info("Agent %s got a proof, but %s is already proven", self.agent_id, lemma_id)
    
    def publish_working_on(self, lemma_id: str) -> None:
        """Publish that this agent is working on a specific lemma."""
        self.event_bus.publish("AgentWorking", {
            "agent_id": self.agent_id,
            "lemma_id": lemma_id,
            "timestamp": time.time()
        })
    
    def publish_attempt_failed(self, lemma_id: str, proof: str = None, error_message: str = None) -> None:
        """Publish that an attempt to prove a lemma has failed."""
        self.event_bus.publish("LemmaAttemptFailed", {
            "agent_id": self.agent_id,
            "lemma_id": lemma_id,
            "proof": proof,
            "error_message": error_message,
            "timestamp": time.time()
        })

    def _handle_openai_error(self, error, context="operation"):
        """Handle OpenAI API errors, exiting on quota issues."""
        error_str = str(error)
        
        # Check for quota error
        if "429" in error_str and "insufficient_quota" in error_str:
            logger.error("CRITICAL ERROR: OpenAI API quota exceeded. Exiting program.")
            logger.error("Error details: %s", error_str)
            import sys
            sys.exit(1)  # Exit with non-zero code to indicate error
        elif "Connection error" in error_str:
            logger.error("Connection error in OpenAI %s: %s", context, error)
            import sys
            sys.exit(1)
        # Log the error but continue execution
        logger.error("Error in OpenAI %s: %s", context, error)
        return error


class OpenAIAgent(BaseAgent):
    """Agent that uses OpenAI models to generate proofs."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface, 
                 model: str = "gpt-4o", parameters: Dict[str, Any] = None, strategy: str = None):
        super().__init__(agent_id, event_bus, lean_interface, strategy)
        self.model = model
        self.parameters = parameters or {}
        self.openai_client = openai.OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        logger.info("Created OpenAI agent %s using model %s", agent_id, model)
        
    def pick_lemma(self) -> Optional[str]:
        """Pick a lemma to work on, show event history depending on strategy."""
        # Get all available lemmas that aren't already proven
        available_lemmas = self.lean_interface.get_available_lemmas() 
        logger.info("OpenAI Agent %s available lemmas: %s", self.agent_id, available_lemmas)
        if not available_lemmas:
            return None
        
        # Get the complete event bus history
        event_history = self.event_bus.get_history()
        
        # Get current activities of other agents
        current_activities = self.event_bus.get_current_agent_activities()
        
        # Create a simple prompt with the raw event history
        prompt = self._create_simple_lemma_selection_prompt(
            available_lemmas, 
            current_activities,
            event_history
        )
        
        try:
            # Ask the LLM to select a lemma
            response = self.openai_client.beta.chat.completions.parse(
                model=self.model,
                messages=[
                    {"role": "system", "content": LEMMA_SELECTION_SYSTEM_PROMPT},
                    {"role": "user", "content": prompt}
                ],
                response_format=LemmaSelection,
                **self.parameters
            )
        
            # Extract the lemma from the response
            selected_lemma = response.choices[0].message.parsed.lemma_id
            
            self.current_lemma = selected_lemma
            logger.info("OpenAI Agent %s picked lemma: %s", self.agent_id, selected_lemma)
            
            # Publish that we're working on this lemma
            self.publish_working_on(selected_lemma)
            return selected_lemma
            
        except Exception as e:
            self._handle_openai_error(e, "lemma selection")
            # Fallback to simple selection
            selected_lemma = random.choice(available_lemmas)
            self.current_lemma = selected_lemma
            self.publish_working_on(selected_lemma)
            return selected_lemma
    
    def attempt_proof(self, lemma_id: str) -> bool:
        """Generate and attempt a proof using OpenAI with event history depending on strategy."""
        logger.info("OpenAI Agent %s attempting to prove %s with %s", self.agent_id, lemma_id, self.model)
        
        # Get the complete event history
        event_history = self.event_bus.get_history()
        # Create a proof generation prompt
        stub_file = self.lean_interface.get_file(lemma_id, "stubs")
        prompt = self._create_proof_attempt_prompt(lemma_id, stub_file, event_history)
        
        try:
            # Ask the LLM to generate a proof
            response = self.openai_client.beta.chat.completions.parse(
                model=self.model,
                messages=[
                    {"role": "system", "content": PROOF_SYSTEM_PROMPT},
                    {"role": "user", "content": prompt}
                ],
                response_format=ProofAttempt,
                **self.parameters
            )
            # Extract the proof attempt from the response
            proof_attempt = response.choices[0].message.parsed.proof
            logger.info("OpenAI Agent %s generated proof:\n %s", self.agent_id, proof_attempt)
            review_proof = self.lean_interface.check_proof(proof_attempt, lemma_id, self.agent_id)
            logger.info("OpenAI Agent %s reviewed proof:\n%s", self.agent_id, json.dumps(review_proof, indent=2))
            if review_proof.get("success"):
                self.publish_proof(lemma_id, proof_attempt)
                return True
            else:
                # Add failed proof attempt to event bus
                self.publish_attempt_failed(
                    lemma_id, 
                    proof_attempt,
                    review_proof.get("output")
                )
                return False
                
        except Exception as e:
            self._handle_openai_error(e, "proof attempt")
            self.publish_attempt_failed(lemma_id, str(e))
            return False


class KiminaAgent(BaseAgent):
    """Agent that uses Kimina to generate proofs."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface, model: str = "AI-MO/Kimina-Prover-Preview-Distill-7B", parameters: Dict[str, Any] = None, strategy: str = None):
        super().__init__(agent_id, event_bus, lean_interface, strategy)
        self.model = model
        self.parameters = parameters or {}
        self.openai_client = openai.OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        self.API_URL = os.getenv("KIMINA_API_URL")
        self.headers = {
            "Accept": "application/json",
            "Authorization": f"Bearer {os.getenv('KIMINA_API_KEY')}",
            "Content-Type": "application/json"
        }
        logger.info("Created Kimina agent %s using model %s", agent_id, model)

    def _get_kimina_response(self, payload: dict) -> str:
        """Get a response from Kimina."""
        response = requests.post(self.API_URL, headers=self.headers, json=payload)
        return response.json()
    
    def pick_lemma(self) -> Optional[str]:
        """Pick a lemma to work on, show event history depending on strategy."""
              # Get all available lemmas that aren't already proven
        available_lemmas = self.lean_interface.get_available_lemmas() 
        logger.info("Kimina Agent %s available lemmas: %s", self.agent_id, available_lemmas)
        if not available_lemmas:
            return None
        
        # Get the complete event bus history
        event_history = self.event_bus.get_history()
        
        # Get current activities of other agents
        current_activities = self.event_bus.get_current_agent_activities()
        
        # Create a simple prompt with the raw event history
        prompt = self._create_simple_lemma_selection_prompt(
            available_lemmas, 
            current_activities,
            event_history
        )
       
        try:
            # Ask the LLM to select a lemma
            response = self.openai_client.beta.chat.completions.parse(
                model="gpt-4o-mini",
                messages=[
                    {"role": "system", "content": LEMMA_SELECTION_SYSTEM_PROMPT},
                    {"role": "user", "content": prompt}
                ],
                response_format=LemmaSelection,
                **self.parameters
            )
        
            # Extract the lemma from the response
            selected_lemma = response.choices[0].message.parsed.lemma_id
            
            self.current_lemma = selected_lemma
            logger.info("Kimina Agent %s picked lemma: %s", self.agent_id, selected_lemma)
            
            # Publish that we're working on this lemma
            self.publish_working_on(selected_lemma)
            return selected_lemma
            
        except Exception as e:
            self._handle_openai_error(e, "lemma selection")
            # Fallback to simple selection
            selected_lemma = random.choice(available_lemmas)
            self.current_lemma = selected_lemma
            self.publish_working_on(selected_lemma)
            return selected_lemma

    def attempt_proof(self, lemma_id: str) -> bool:
        """Generate and attempt a proof using Kimina."""
        logger.info("Kimina Agent %s attempting to prove %s with %s", self.agent_id, lemma_id, self.model)
        
        # Get the complete event history
        event_history = self.event_bus.get_history()
        # Create a proof generation prompt
        stub_file = self.lean_interface.get_file(lemma_id, "stubs")
        prompt = self._create_proof_attempt_prompt(lemma_id, stub_file, event_history)
        
        try:
            logger.info("Kimina Agent %s about to call Kimina API", self.agent_id)

            if "Prop" in stub_file:
                logger.info("Kimina Agent %s lemma %s is a definition, skipping proof attempt", self.agent_id, lemma_id)
                proof_attempt = stub_file
            else:
                # Ask the LLM to generate a proof
                response = self._get_kimina_response({
                    "inputs" : (
                        f"- Take this Lean 4 stub with 'sorry' and give a proof in place of the 'sorry'. Note, you must not return a 'sorry' in your proof."
                        f"- Only provide a proof for the given lemma"
                        f"Ensure to indicate the proof with ```lean4 and ``` at the beginning and end of the proof."
                        f"{prompt}"
                    ),
                    "parameters" : {
                        "max_new_tokens" : 10000,
                    }
                })
                logger.info("Kimina Agent %s response:\n %s", self.agent_id, response)
                # Extract the proof attempt from the response
                proof_attempt = self._extract_and_fix_lean_proof(response[0]["generated_text"])
            logger.info("Kimina Agent %s generated proof:\n %s", self.agent_id, proof_attempt)
            review_proof = self.lean_interface.check_proof(proof_attempt, lemma_id, self.agent_id)
            logger.info("Kimina Agent %s reviewed proof:\n%s", self.agent_id, json.dumps(review_proof, indent=2))
            if review_proof.get("success"):
                self.publish_proof(lemma_id, proof_attempt)
                return True
            else:
                # Add failed proof attempt to event bus
                self.publish_attempt_failed(
                    lemma_id, 
                    proof_attempt,
                    review_proof.get("output")
                )
                return False
                
        except Exception as e:
            import sys
            sys.exit(1)  # Exit with non-zero code to indicate error
        
    
    def _extract_and_fix_lean_proof(self, text: str) -> str:
        """Extract and fix a Lean proof from the response."""
        try:
            response = self.openai_client.beta.chat.completions.parse(
                model="gpt-4o-mini",
                messages=[
                    {"role": "system", "content": (
                        "You are a helpful assistant that looks at output from a language model and extracts the final proof that the language model wants to return." 
                        "Make sure to include the imports and correct them if necessary. A common mistake is to put spaces instead of dots in the import statements. For example, instead of `import EvensquarePlusEven stubs isEven` it should be `import EvensquarePlusEven.stubs.isEven`."
                        "You should return Lean 4 code, not Markdown code blocks, i.e. it should be able to be copied into a Lean 4 file and compiled."
                    )},
                    {"role": "user", "content": text}
                ],
                response_format=ExtractLeanProof,
                **self.parameters
            )
            return response.choices[0].message.parsed.proof
        except Exception as e:
            logger.error("Error in extracting and fixing Lean proof: %s", e)
            return None



# Factory function to create the right type of agent based on provider
def create_agent(config, event_bus, lean_interface, strategy):
    """Create an agent based on the provided configuration."""
    logger.info("Creating agent: %s with provider %s and strategy %s", config.id, config.provider, strategy)
    if config.provider.lower() == "openai":
        return OpenAIAgent(
            agent_id=config.id,
            event_bus=event_bus,
            lean_interface=lean_interface,
            model=config.model,
            parameters=config.parameters,
            strategy=strategy
        )
    elif config.provider.lower() == "kimina":
        return KiminaAgent(
            agent_id=config.id,
            event_bus=event_bus,
            lean_interface=lean_interface,
            model=config.model,
            parameters=config.parameters,
            strategy=strategy
        )
    else:
        logger.error("Unknown provider: %s", config.provider)
        raise ValueError(f"Unknown provider: {config.provider}") 