"""
Event bus implementation for agent communication with history tracking.
Implements a publish-subscribe pattern for sharing events between agents.
"""
from typing import Dict, List, Callable, Any
from collections import defaultdict
import time

class EventBus:
    def __init__(self, max_history: int = 1000):
        self._subscribers: Dict[str, List[Callable]] = {}
        self._history: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        self.max_history = max_history
    
    def subscribe(self, event_type: str, callback: Callable) -> None:
        """Subscribe a callback to a specific event type."""
        if event_type not in self._subscribers:
            self._subscribers[event_type] = []
        self._subscribers[event_type].append(callback)
    
    def publish(self, event_type: str, data: Any = None) -> None:
        """Publish an event to all subscribers of the given event type and store in history."""
        # Add timestamp to the event data
        event_record = {
            "timestamp": time.time(),
            "data": data
        }
        
        # Store in history
        self._history[event_type].append(event_record)
        # Trim history if needed
        # TODO: Uncomment this when we have a way to trim history
        # if len(self._history[event_type]) > self.max_history:
        #     self._history[event_type] = self._history[event_type][-self.max_history:]
        
        # Notify subscribers
        if event_type in self._subscribers:
            for callback in self._subscribers[event_type]:
                callback(data)
    
    def unsubscribe(self, event_type: str, callback: Callable) -> None:
        """Unsubscribe a callback from a specific event type."""
        if event_type in self._subscribers and callback in self._subscribers[event_type]:
            self._subscribers[event_type].remove(callback)
    
    def get_history(self, event_type: str = None, limit: int = 30) -> Dict[str, List[Dict[str, Any]]]:
        """
        Get event history, optionally filtered by event type.
        
        Args:
            event_type: If provided, only return history for this event type
            limit: If provided, limit the number of events returned per type
            
        Returns:
            Dictionary mapping event types to lists of event records
        """
        if event_type:
            events = {event_type: self._history.get(event_type, [])[-limit:] if limit else self._history.get(event_type, [])}
            return events
        
        if limit:
            return {k: v[-limit:] for k, v in self._history.items()}
        
        return dict(self._history)
    
    def get_current_agent_activities(self) -> Dict[str, str]:
        """
        Get what each agent is currently working on.
        Returns a dictionary mapping agent_id to current_lemma.
        """
        activities = {}
        
        # Get the most recent AgentWorking events for each agent
        for event in reversed(self._history.get("AgentWorking", [])):
            agent_id = event["data"]["agent_id"]
            if agent_id not in activities:
                activities[agent_id] = event["data"]["lemma_id"]
        
        return activities
