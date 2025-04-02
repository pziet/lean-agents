"""
All agent implementations in a single file.
"""
from abc import ABC, abstractmethod
import random
import time
from typing import Optional, List, Dict, Any, Set
from .event_bus import EventBus
from .lean_interface import LeanInterface

class BaseAgent(ABC):
    """Base abstract class for all agents."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface):
        self.agent_id = agent_id
        self.event_bus = event_bus
        self.lean_interface = lean_interface
        self.available_lemmas = lean_interface.get_available_lemmas()
        self.proven_lemmas: Set[str] = set()
        self.current_lemma: Optional[str] = None
        
        # Subscribe to LemmaProven events
        self.event_bus.subscribe("LemmaProven", self.on_lemma_proven)
    
    @abstractmethod
    def pick_lemma(self) -> Optional[str]:
        """Select a lemma to work on."""
        pass
    
    @abstractmethod
    def attempt_proof(self, lemma_id: str) -> bool:
        """Attempt to prove the given lemma. Return True if successful."""
        pass
    
    def on_lemma_proven(self, data: dict) -> None:
        """Handle notification that a lemma has been proven."""
        lemma_id = data.get("lemma_id")
        agent_id = data.get("agent_id")
        
        if lemma_id and agent_id != self.agent_id:
            print(f"Agent {self.agent_id} notified that {lemma_id} was proven by {agent_id}")
            self.proven_lemmas.add(lemma_id)
            
            # If this was our current lemma, pick a new one
            if self.current_lemma == lemma_id:
                self.current_lemma = None
                self.pick_lemma()
    
    def publish_proof(self, lemma_id: str, proof: str) -> None:
        """Publish a successful proof to the shared folder and notify others."""
        # Save the proof to the proven directory
        filepath = self.lean_interface.save_proven_lemma(lemma_id, proof)
        print(f"Agent {self.agent_id} proved lemma: {lemma_id}")
        
        # Notify other agents
        self.event_bus.publish("LemmaProven", {
            "lemma_id": lemma_id,
            "proof": proof,
            "agent_id": self.agent_id,
            "filepath": filepath
        })
        
        # Update our own record
        self.proven_lemmas.add(lemma_id)


class OpenAIAgent(BaseAgent):
    """Agent that uses OpenAI models to generate proofs."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface, 
                 model: str = "gpt-4", parameters: Dict[str, Any] = None):
        super().__init__(agent_id, event_bus, lean_interface)
        self.model = model
        self.parameters = parameters or {}
        print(f"Created OpenAI agent {agent_id} using model {model}")
    
    def pick_lemma(self) -> Optional[str]:
        """Pick a lemma to work on that hasn't been proven yet."""
        for lemma in self.available_lemmas:
            if lemma not in self.proven_lemmas:
                self.current_lemma = lemma
                print(f"OpenAI Agent {self.agent_id} picked lemma: {lemma}")
                return lemma
        return None
    
    def attempt_proof(self, lemma_id: str) -> bool:
        """Generate and attempt a proof using OpenAI."""
        print(f"OpenAI Agent {self.agent_id} attempting to prove {lemma_id} with {self.model}")
        
        # Simulated proof attempt - in a real scenario, this would call the OpenAI API
        # Simulate success/failure (this is where real API calls would go)
        success = random.random() > 0.7  # 30% chance of success
        
        if success:
            proof = f"by {self.model}\n  -- simulated proof for {lemma_id} from OpenAI"
            self.publish_proof(lemma_id, proof)
        
        # In a real system, we would sleep to avoid rate limiting
        time.sleep(1)
        return success


class AnthropicAgent(BaseAgent):
    """Agent that uses Anthropic models to generate proofs."""
    def __init__(self, agent_id: str, event_bus: EventBus, lean_interface: LeanInterface, 
                 model: str = "claude-3", parameters: Dict[str, Any] = None):
        super().__init__(agent_id, event_bus, lean_interface)
        self.model = model
        self.parameters = parameters or {}
        print(f"Created Anthropic agent {agent_id} using model {model}")
    
    def pick_lemma(self) -> Optional[str]:
        """Pick a lemma to work on that hasn't been proven yet."""
        for lemma in self.available_lemmas:
            if lemma not in self.proven_lemmas:
                self.current_lemma = lemma
                print(f"Anthropic Agent {self.agent_id} picked lemma: {lemma}")
                return lemma
        return None
    
    def attempt_proof(self, lemma_id: str) -> bool:
        """Generate and attempt a proof using Anthropic."""
        print(f"Anthropic Agent {self.agent_id} attempting to prove {lemma_id} with {self.model}")
        
        # Simulated proof attempt - in a real scenario, this would call the Anthropic API
        # Simulate success/failure
        success = random.random() > 0.6  # 40% chance of success
        
        if success:
            proof = f"by {self.model}\n  -- simulated proof for {lemma_id} from Anthropic"
            self.publish_proof(lemma_id, proof)
        
        # In a real system, we would sleep to avoid rate limiting
        time.sleep(1)
        return success


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