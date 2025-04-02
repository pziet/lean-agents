"""
Main coordinator for managing multiple agents working on Lean theorems.
"""
import time
import os
import threading
from typing import List, Dict, Any

from .event_bus import EventBus
from .lean_interface import LeanInterface
from .agents import BaseAgent, create_agent
from .config import RunConfig

class MainCoordinator:
    def __init__(self, config: RunConfig):
        self.config = config
        self.event_bus = EventBus()
        self.lean_interface = LeanInterface(config.lean_path, config.theorem_file)
        self.agents: List[BaseAgent] = []
        self.agent_threads: Dict[str, threading.Thread] = {}
        self.running = False
        
        # Create log directory if it doesn't exist
        os.makedirs(config.log_dir, exist_ok=True)
        
        # Initialize agents based on config
        self._initialize_agents()
    
    def _initialize_agents(self) -> None:
        """Initialize agents based on the configuration."""
        for agent_config in self.config.agent_configs:
            agent = create_agent(agent_config, self.event_bus, self.lean_interface)
            self.agents.append(agent)
    
    def _agent_worker(self, agent: BaseAgent) -> None:
        """Worker function for each agent thread."""
        while self.running:
            # Try to pick a lemma if the agent doesn't have one
            lemma = agent.pick_lemma()
            if lemma:
                # Attempt to prove it
                success = agent.attempt_proof(lemma)
                if not success:
                    # If failed, sleep briefly before trying again or picking a new lemma
                    time.sleep(1)
            else:
                # No lemmas available, sleep for a bit
                time.sleep(2)
    
    def start(self) -> None:
        """Start all agents working on proofs."""
        self.running = True
        
        # Create and start a thread for each agent
        for agent in self.agents:
            thread = threading.Thread(
                target=self._agent_worker,
                args=(agent,),
                name=f"Agent-{agent.agent_id}"
            )
            self.agent_threads[agent.agent_id] = thread
            thread.start()
            print(f"Started agent: {agent.agent_id}")
    
    def stop(self) -> None:
        """Stop all agents."""
        self.running = False
        
        # Wait for all threads to finish
        for agent_id, thread in self.agent_threads.items():
            thread.join()
            print(f"Stopped agent: {agent_id}")
    
    def run_for_duration(self) -> None:
        """Run the system for the configured duration then stop."""
        duration = self.config.max_runtime_seconds
        print(f"Running for {duration} seconds...")
        self.start()
        time.sleep(duration)
        self.stop()
        
        # Print summary
        print("\n--- Summary ---")
        all_proven = set()
        for agent in self.agents:
            print(f"Agent {agent.agent_id} proved: {agent.proven_lemmas}")
            all_proven.update(agent.proven_lemmas)
        
        print(f"\nTotal lemmas proven: {len(all_proven)}")
        print(f"Proven lemmas: {all_proven}")
