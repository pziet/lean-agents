"""
Simple event bus implementation for agent communication.
Implements a publish-subscribe pattern for sharing events between agents.
"""
from typing import Dict, List, Callable, Any

class EventBus:
    def __init__(self):
        self._subscribers: Dict[str, List[Callable]] = {}
    
    def subscribe(self, event_type: str, callback: Callable) -> None:
        """Subscribe a callback to a specific event type."""
        if event_type not in self._subscribers:
            self._subscribers[event_type] = []
        self._subscribers[event_type].append(callback)
    
    def publish(self, event_type: str, data: Any = None) -> None:
        """Publish an event to all subscribers of the given event type."""
        if event_type in self._subscribers:
            for callback in self._subscribers[event_type]:
                callback(data)
    
    def unsubscribe(self, event_type: str, callback: Callable) -> None:
        """Unsubscribe a callback from a specific event type."""
        if event_type in self._subscribers and callback in self._subscribers[event_type]:
            self._subscribers[event_type].remove(callback)
