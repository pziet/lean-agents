"""
All agent implementations in a single file with enhanced event bus visibility.
"""
import os
import json
from abc import ABC, abstractmethod
from pydantic import BaseModel
import random
import time
from typing import Optional, List, Dict, Any, Set
import openai
import anthropic

from .event_bus import EventBus
from .lean_interface import LeanInterface

LEMMA_SELECTION_SYSTEM_PROMPT = """
    You are a theorem-proving assistant who gives proofs for lemmas in Lean 4.
"""

PROOF_SYSTEM_PROMPT = """
    You are a theorem-proving assistant who gives proofs for lemmas in Lean 4.
        
    - You are an agent in a team of agents that are collectively proving a set of lemmas, so I will also show you a full event history of the team's progress so far including any failed proof attempts.
    - These set of lemmas can be related, for example Lemma 1 might be used in the proof of Lemma 2. In this case you can simply import Lemma 1 even if it is not yet proven since we use Lean 4's "sorry" tactic to fill in the proof. This will allow you to build up a proof incrementally and not necessarily sequentially.
    - Avoid lemmas that other agents are already working on.
    - If the file is a definition, i.e. a `Prop`, then you can simply restate it since there is nothing to prove.
    - You only return Lean 4 code which can be parsed by the Lean 4 parser, nothing else. Make sure to include all necessary imports. 
"""

# TODO: Consider adding reasoning (str)
class LemmaSelection(BaseModel):
    lemma_id: str

# TODO: Consider adding confidence (float) and reasoning (str)
class ProofAttempt(BaseModel):
    proof: str


class BaseAgent(ABC):
    """Base abstract class for all agents."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface):
        self.agent_id = agent_id
        self.event_bus = event_bus
        self.lean_interface = lean_interface
        # self.available_lemmas = lean_interface.get_available_lemmas()
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
        
        prompt = f"""
        As a theorem-proving assistant, your task is to select the next lemma to work on. 
        # Available Lemmas
        {available_lemmas}

        <Available Lemmas and their stubs>
        {available_lemmas_str}
        </Available Lemmas and their stubs>

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
        print(f"[agents] Lemma selection prompt:\n{prompt}")
        return prompt
    
    def _create_proof_attempt_prompt(self, lemma_id: str, stub_file: str, event_history: Dict) -> str:
        """Create a detailed prompt for proof generation using event history."""
        history_str = self._format_event_history(event_history)
        proven_lemmas_str = self._format_proven_lemmas()

        prompt = f"""
        Generate a proof for lemma {lemma_id} in Lean 4. Here is a stub file of the lemma, make sure to use it as a starting point:

        {stub_file}

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
        return prompt

    def on_lemma_proven(self, data: dict) -> None:
        """Handle notification that a lemma has been proven."""
        lemma_id = data.get("lemma_id")
        agent_id = data.get("agent_id")
        
        if lemma_id and agent_id != self.agent_id:
            print(f"[agents] Agent {self.agent_id} notified that {lemma_id} was proven by {agent_id}")
            # self.proven_lemmas.add(lemma_id)
            
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
            print(f"[agents] Agent {self.agent_id} proved lemma: {lemma_id}")
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
            print(f"[agents] Agent {self.agent_id} got a proof, but {lemma_id} is already proven")
        

    
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


class OpenAIAgent(BaseAgent):
    """Agent that uses OpenAI models to generate proofs."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface, 
                 model: str = "gpt-4o", parameters: Dict[str, Any] = None):
        super().__init__(agent_id, event_bus, lean_interface)
        self.model = model
        self.parameters = parameters or {}
        self.openai_client = openai.OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        print(f"[agents] Created OpenAI agent {agent_id} using model {model}")
    
    def pick_lemma(self) -> Optional[str]:
        """Pick a lemma to work on by showing the full event bus history to the LLM."""
        # Get all available lemmas that aren't already proven
        available_lemmas = self.lean_interface.get_available_lemmas() 
        
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
            print(f"[agents] OpenAI Agent {self.agent_id} picked lemma: {selected_lemma}")
            
            # Publish that we're working on this lemma
            self.publish_working_on(selected_lemma)
            return selected_lemma
            
        except Exception as e:
            print(f"Error in OpenAI lemma selection: {e}")
            # Fallback to simple selection
            selected_lemma = random.choice(available_lemmas)
            self.current_lemma = selected_lemma
            self.publish_working_on(selected_lemma)
            return selected_lemma
    
    def attempt_proof(self, lemma_id: str) -> bool:
        """Generate and attempt a proof using OpenAI with event bus awareness."""
        print(f"[agents] OpenAI Agent {self.agent_id} attempting to prove {lemma_id} with {self.model}")
        
        # Get the complete event history
        event_history = self.event_bus.get_history()
        print(f"[agents] OpenAI Agent {self.agent_id} event history:\n{json.dumps(event_history, indent=2)}")
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
            print(f"[agents] OpenAI Agent {self.agent_id} generated proof:\n {proof_attempt}")
            review_proof = self.lean_interface.check_proof(proof_attempt, lemma_id, self.agent_id)
            print(f"[agents] OpenAI Agent {self.agent_id} reviewed proof:\n{json.dumps(review_proof, indent=2)}")
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
            print(f"[agents] Error in OpenAI proof attempt: {e}")
            self.publish_attempt_failed(lemma_id, str(e))
            return False


class AnthropicAgent(BaseAgent):
    """Agent that uses Anthropic models to generate proofs."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface, 
                 model: str = "claude-3", parameters: Dict[str, Any] = None):
        super().__init__(agent_id, event_bus, lean_interface)
        self.model = model
        self.parameters = parameters or {}
        self.anthropic_client = anthropic.Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))
        print(f"[agents] Created Anthropic agent {agent_id} using model {model}")
    
    def pick_lemma(self) -> Optional[str]:
        """Pick a lemma to work on that hasn't been proven yet, with event bus awareness."""
        # Similar approach to OpenAIAgent, with potential for different strategies
        event_state = self.get_event_bus_state()
        current_activities = event_state["current_activities"]
        
        available_lemmas = self.lean_interface.get_available_lemmas()        
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
            response = self.anthropic_client.messages.create(
                model=self.model,
                tools=[
                    {
                        "name": "lemma_selection",
                        "description": "Select a lemma to work on",
                        "input_schema": {
                            "type": "object",
                            "properties": {
                                "lemma_id": {
                                    "type": "string",
                                    "description": "The ID of the lemma to work on"
                                }
                            }
                        },
                        "required": ["lemma_id"]
                    }
                ],
                tool_choice={"type": "tool", "name": "lemma_selection"},
                system=LEMMA_SELECTION_SYSTEM_PROMPT,
                messages=[
                    {"role": "user", "content": prompt}
                    ],
                **self.parameters
            )

            # Extract the lemma from the response
            selected_lemma = response.content[0].input.get("lemma_id")
            self.current_lemma = selected_lemma

            # Publish that we're working on this lemma
            print(f"[agents] Anthropic Agent {self.agent_id} picked lemma: {selected_lemma}")
            self.publish_working_on(selected_lemma)
            return selected_lemma
        
        except Exception as e:
            print(f"[agents] Error in Anthropic lemma selection: {e}")
            # Fallback to simple selection
            selected_lemma = random.choice(available_lemmas)
            self.current_lemma = selected_lemma
            self.publish_working_on(selected_lemma)
            return selected_lemma
    
    def attempt_proof(self, lemma_id: str) -> bool:
        """Generate and attempt a proof using Anthropic with event bus awareness."""
        print(f"[agents] Anthropic Agent {self.agent_id} attempting to prove {lemma_id} with {self.model}")
        
        # Get the complete event history
        event_history = self.event_bus.get_history()
        print(f"[agents] Anthropic Agent {self.agent_id} event history:\n{json.dumps(event_history, indent=2)}")

        # Create a proof generation prompt
        stub_file = self.lean_interface.get_file(lemma_id, "stubs")
        prompt = self._create_proof_attempt_prompt(lemma_id, stub_file, event_history)

        try: 
            # Ask the LLM to generate a proof
            response = self.anthropic_client.messages.create(
                model=self.model,
                tools=[
                    {
                        "name": "proof_attempt",
                        "description": "Attempt to prove a lemma in Lean 4",
                        "input_schema": {
                            "type": "object",
                            "properties": {
                                "proof": {"type": "string", "description": "The proof to attempt which must be valid Lean 4 code"}
                            },
                            "required": ["proof"]
                        }
                    }
                ],
                tool_choice={"type": "tool", "name": "proof_attempt"},
                system=PROOF_SYSTEM_PROMPT,
                messages=[
                    {"role": "user", "content": prompt}
                ],
                **self.parameters
            )

            # Extract the proof attempt from the response
            proof_attempt = response.content[0].input.get("proof")
            print(f"[agents] Anthropic Agent {self.agent_id} generated proof:\n {proof_attempt}")
            review_proof = self.lean_interface.check_proof(proof_attempt, lemma_id, self.agent_id)
            print(f"[agents] Anthropic Agent {self.agent_id} reviewed proof:\n{json.dumps(review_proof, indent=2)}")
            if review_proof.get("success"):
                self.publish_proof(lemma_id, proof_attempt)
                return True
            else:
                self.publish_attempt_failed(lemma_id, proof_attempt, review_proof.get("output"))
                return False

        except Exception as e:
            print(f"[agents] Error in Anthropic proof attempt: {e}")
            self.publish_attempt_failed(lemma_id, str(e))
            return False

# Factory function to create the right type of agent based on provider
def create_agent(config, event_bus, lean_interface):
    """Create an agent based on the provided configuration."""
    if config.provider.lower() == "openai":
        return OpenAIAgent(
            agent_id=config.id,
            event_bus=event_bus,
            lean_interface=lean_interface,
            model=config.model,
            parameters=config.parameters
        )
    elif config.provider.lower() == "anthropic":
        return AnthropicAgent(
            agent_id=config.id,
            event_bus=event_bus,
            lean_interface=lean_interface,
            model=config.model,
            parameters=config.parameters
        )
    else:
        raise ValueError(f"Unknown provider: {config.provider}") 