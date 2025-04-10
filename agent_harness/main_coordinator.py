"""
Main coordinator for managing multiple agents working on Lean theorems.
"""
import time
import os
import threading
import json
from typing import List, Dict, Any

from .event_bus import EventBus
from .lean_interface import LeanInterface
from .agents import BaseAgent, create_agent
from .config import RunConfig

class MainCoordinator:
    def __init__(self, config: RunConfig):
        self.config = config
        self.event_bus = EventBus()
        self.lean_interface = LeanInterface(config.lean_path, config.file_dir)
        self.agents: List[BaseAgent] = []
        self.agent_threads: Dict[str, threading.Thread] = {}
        self.running = False
        self.log_file = os.path.join(config.log_dir, f"run_{int(time.time())}.log")
        
        # Create log directory if it doesn't exist
        os.makedirs(config.log_dir, exist_ok=True)
        
        # Initialize agents based on config
        self._initialize_agents()
        
        # Subscribe to all events for logging
        self.event_bus.subscribe("LemmaProven", lambda data: self._log_event(data, "LemmaProven"))
        self.event_bus.subscribe("LemmaAttemptFailed", lambda data: self._log_event(data, "LemmaAttemptFailed"))
        self.event_bus.subscribe("AgentWorking", lambda data: self._log_event(data, "AgentWorking"))
    
    def _initialize_agents(self) -> None:
        """Initialize agents based on the configuration."""
        print(f"[MainCoordinator] Initializing {len(self.config.agent_configs)} agents")
        for agent_config in self.config.agent_configs:
            agent = create_agent(agent_config, self.event_bus, self.lean_interface)
            self.agents.append(agent)
            print(f"[MainCoordinator] Created agent: {agent.agent_id}")
    
    def _log_event(self, data: Dict, event_type: str = None) -> None:
        """Log an event to the log file.
        
        Args:
            data: The event data
            event_type: The type of event being logged
        """
        # Use the provided event_type rather than thread name
        print(f"[MainCoordinator] Event: {event_type} - {data}")
        
        log_entry = {
            "timestamp": time.time(),
            "event_type": event_type,
            "data": data
        }
        
        with open(self.log_file, 'a') as f:
            f.write(json.dumps(log_entry) + '\n')
    
    def _agent_worker(self, agent: BaseAgent) -> None:
        """Worker function for each agent thread."""
        print(f"[Agent-{agent.agent_id}] Worker thread started")
        while self.running:
            # Try to pick a lemma if the agent doesn't have one
            print(f"[Agent-{agent.agent_id}] Attempting to pick a lemma")
            lemma = agent.pick_lemma()
            if lemma:
                print(f"[Agent-{agent.agent_id}] Picked lemma: {lemma}")
                # Attempt to prove it
                print(f"[Agent-{agent.agent_id}] Attempting to prove lemma")
                success = agent.attempt_proof(lemma)
                if success:
                    print(f"[Agent-{agent.agent_id}] Successfully proved lemma: {lemma}")
                else:
                    print(f"[Agent-{agent.agent_id}] Failed to prove lemma: {lemma}")
                    # If failed, sleep briefly before trying again or picking a new lemma
                    print(f"[Agent-{agent.agent_id}] Sleeping for 1 second before next attempt")
                    time.sleep(1)
            else:
                # No lemmas available
                print("[MainCoordinator] All lemmas have been proven. Stopping simulation.")
                self.running = False
        print(f"[Agent-{agent.agent_id}] Worker thread terminated")
    
    def start(self) -> None:
        """Start all agents working on proofs."""
        print(f"[MainCoordinator] Starting {len(self.agents)} agents")
        self.running = True
        
        # Create and start a thread for each agent
        for agent in self.agents:
            print(f"[MainCoordinator] Creating thread for agent: {agent.agent_id}")
            thread = threading.Thread(
                target=self._agent_worker,
                args=(agent,),
                name=f"Agent-{agent.agent_id}"
            )
            self.agent_threads[agent.agent_id] = thread
            thread.start()
            print(f"[MainCoordinator] Started agent: {agent.agent_id}")
    
    def stop(self) -> None:
        """Stop all agents."""
        print(f"[MainCoordinator] Stopping all agents")
        self.running = False
        
        # Wait for all threads to finish
        for agent_id, thread in self.agent_threads.items():
            print(f"[MainCoordinator] Waiting for agent {agent_id} to terminate")
            thread.join()
            print(f"[MainCoordinator] Stopped agent: {agent_id}")
    
    def run_for_duration(self) -> None:
        """Run the system for the configured duration then stop."""
        duration = self.config.max_runtime_seconds
        print(f"[MainCoordinator] Running for {duration} seconds...")
        self.start()
        end_time = time.time() + duration
        print(f"[MainCoordinator] All agents started, sleeping for {duration} seconds")

        while time.time() < end_time and self.running:
            #  Do nothing, just wait for the duration to pass
            time.sleep(1)

        print(f"[MainCoordinator] Simulation complete, stopping all agents")
        self.stop()
        
        # Print summary
        print("\n[MainCoordinator] --- Summary ---")
        all_proven = set()
        for agent in self.agents:
            print(f"[MainCoordinator] Agent {agent.agent_id} proved: {agent.proven_lemmas}")
            all_proven.update(agent.proven_lemmas)
        
        print(f"\n[MainCoordinator] Total lemmas proven: {len(all_proven)}")
        print(f"[MainCoordinator] Proven lemmas: {all_proven}")
        
        # Print event bus statistics
        self._print_event_bus_statistics()

        # Delete all proven lemmas
        self.lean_interface.delete_proven_lemmas()
    
    def _print_event_bus_statistics(self) -> None:
        """Print statistics from the event bus."""
        print("\n[MainCoordinator] --- Event Bus Statistics ---")
        
        # Count events by type
        history = self.event_bus.get_history()
        for event_type, events in history.items():
            print(f"[MainCoordinator] {event_type}: {len(events)} events")
        
        # Print collaboration metrics
        lemma_proven_events = history.get("LemmaProven", [])
        lemma_attempt_failed_events = history.get("LemmaAttemptFailed", [])
        
        print(f"\n[MainCoordinator] Total successful proofs: {len(lemma_proven_events)}")
        print(f"[MainCoordinator] Total failed attempts: {len(lemma_attempt_failed_events)}")
        
        # Calculate average attempts before success
        lemma_attempts = {}
        for event in lemma_attempt_failed_events:
            lemma_id = event["data"]["lemma_id"]
            if lemma_id not in lemma_attempts:
                lemma_attempts[lemma_id] = 0
            lemma_attempts[lemma_id] += 1
        
        proven_lemmas = [event["data"]["lemma_id"] for event in lemma_proven_events]
        if proven_lemmas:
            avg_attempts = sum(lemma_attempts.get(lemma_id, 0) for lemma_id in proven_lemmas) / len(proven_lemmas)
            print(f"[MainCoordinator] Average failed attempts before success: {avg_attempts:.2f}")
        else:
            print(f"[MainCoordinator] No lemmas were successfully proven")
