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

import logging

logger = logging.getLogger(__name__)

class MainCoordinator:
    def __init__(self, config: RunConfig):
        self.config = config
        self.event_bus = EventBus()
        self.lean_interface = LeanInterface(config.lean_path, config.file_dir)
        self.strategy = config.strategy
        self.agents: List[BaseAgent] = []
        self.agent_threads: Dict[str, threading.Thread] = {}
        self.running = False
        self.run_log_dir = config.log_dir
        log_file_name = getattr(config, 'log_file_name', f"run_{int(time.time())}.log")
        self.log_file = os.path.join(self.run_log_dir, log_file_name)
        
        # Create the specific log directory if it doesn't exist
        os.makedirs(self.run_log_dir, exist_ok=True)
        
        # Initialize agents based on config
        self._initialize_agents()
        
        # Subscribe to all events for logging
        self.event_bus.subscribe("LemmaProven", lambda data: self._log_event(data, "LemmaProven"))
        self.event_bus.subscribe("LemmaAttemptFailed", lambda data: self._log_event(data, "LemmaAttemptFailed"))
        self.event_bus.subscribe("AgentWorking", lambda data: self._log_event(data, "AgentWorking"))
    
    def _initialize_agents(self) -> None:
        """Initialize agents based on the configuration."""
        logger.info("Initializing %s agents", len(self.config.agent_configs))
        for agent_config in self.config.agent_configs:
            logger.info("Creating agent: %s", agent_config)
            agent = create_agent(agent_config, self.event_bus, self.lean_interface, self.strategy)
            self.agents.append(agent)
            logger.info("Created agent: %s", agent.agent_id)
    
    def _log_event(self, data: Dict, event_type: str = None) -> None:
        """Log an event to the log file.
        
        Args:
            data: The event data
            event_type: The type of event being logged
        """
        # Use the provided event_type rather than thread name
        logger.info("Event: %s - %s", event_type, data)
        
        log_entry = {
            "timestamp": time.time(),
            "event_type": event_type,
            "data": data
        }
        
        with open(self.log_file, 'a') as f:
            f.write(json.dumps(log_entry) + '\n')
    
    def _agent_worker(self, agent: BaseAgent) -> None:
        """Worker function for each agent thread."""
        logger.info("Agent-%s worker thread started", agent.agent_id)
        while self.running:
            # Try to pick a lemma if the agent doesn't have one
            logger.info("Agent-%s attempting to pick a lemma", agent.agent_id)
            lemma = agent.pick_lemma()
            if lemma:
                logger.info("Agent-%s picked lemma: %s", agent.agent_id, lemma)
                # Attempt to prove it
                logger.info("Agent-%s attempting to prove lemma", agent.agent_id)
                success = agent.attempt_proof(lemma)
                if success:
                    logger.info("Agent-%s successfully proved lemma: %s", agent.agent_id, lemma)
                else:
                    logger.info("Agent-%s failed to prove lemma: %s", agent.agent_id, lemma)
                    # If failed, sleep briefly before trying again or picking a new lemma
                    logger.info("Agent-%s sleeping for 1 second before next attempt", agent.agent_id)
                    time.sleep(1)
            else:
                # No lemmas available
                print("[MainCoordinator] All lemmas have been proven. Stopping simulation.")
                self.running = False
        logger.info("Agent-%s worker thread terminated", agent.agent_id)
    
    def start(self) -> None:
        """Start all agents working on proofs."""
        logger.info("Starting %s agents", len(self.agents))
        self.running = True
        
        # Create and start a thread for each agent
        for agent in self.agents:
            logger.info("Creating thread for agent: %s", agent.agent_id)
            thread = threading.Thread(
                target=self._agent_worker,
                args=(agent,),
                name=f"Agent-{agent.agent_id}"
            )
            self.agent_threads[agent.agent_id] = thread
            thread.start()
            logger.info("Started agent: %s", agent.agent_id)
    
    def stop(self) -> None:
        """Stop all agents."""
        logger.info("Stopping all agents")
        self.running = False
        
        # Wait for all threads to finish
        for agent_id, thread in self.agent_threads.items():
            logger.info("Waiting for agent %s to terminate", agent_id)
            thread.join()
            logger.info("Stopped agent: %s", agent_id)
    
    def run_for_duration(self) -> None:
        """Run the system for the configured duration then stop."""
        duration = self.config.max_runtime_seconds
        logger.info("Running for %s seconds...", duration)
        self.start()
        end_time = time.time() + duration
        logger.info("All agents started, sleeping for %s seconds", duration)

        while time.time() < end_time and self.running:
            #  Do nothing, just wait for the duration to pass
            time.sleep(1)

        logger.info("Simulation complete, stopping all agents")
        self.stop()
        
        # Print summary
        logger.info("\n--- Summary ---")
        all_proven = set()
        for agent in self.agents:
            logger.info("Agent %s proved: %s", agent.agent_id, agent.proven_lemmas)
            all_proven.update(agent.proven_lemmas)
        
        logger.info("Total lemmas proven: %s", len(all_proven))
        logger.info("Proven lemmas: %s", all_proven)
        
        # Print event bus statistics
        self._print_event_bus_statistics()
        # Save event bus history to logs
        self._log_event(self.event_bus.get_history(), "EventBusHistory")
        # Delete all proven lemmas
        self.lean_interface.delete_proven_lemmas()    
                
    def _print_event_bus_statistics(self) -> None:
        """Print statistics from the event bus."""
        logger.info("\n--- Event Bus Statistics ---")
        
        # Count events by type
        history = self.event_bus.get_history()
        for event_type, events in history.items():
            logger.info("%s: %s events", event_type, len(events))
        
        # Print collaboration metrics
        lemma_proven_events = history.get("LemmaProven", [])
        lemma_attempt_failed_events = history.get("LemmaAttemptFailed", [])
        
        logger.info("Total successful proofs: %s", len(lemma_proven_events))
        logger.info("Total failed attempts: %s", len(lemma_attempt_failed_events))
        
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
            logger.info("Average failed attempts before success: %.2f", avg_attempts)
        else:
            logger.info("No lemmas were successfully proven")
