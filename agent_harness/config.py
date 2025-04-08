"""
Configuration for the agent harness system.
"""
import os
import json
from dataclasses import dataclass
from typing import List, Dict, Any, Optional

@dataclass
class AgentConfig:
    """Configuration for a single agent."""
    id: str
    provider: str  # "openai", "anthropic", etc.
    model: str  # "gpt-4", "claude-3", etc.
    parameters: Dict[str, Any] = None  # Additional parameters like temperature
    
    def __post_init__(self):
        if self.parameters is None:
            self.parameters = {}

@dataclass
class RunConfig:
    """Configuration for a complete agent run."""
    theorem_file: str
    num_agents: int
    agent_configs: List[AgentConfig]
    lean_path: str
    file_dir: str
    max_runtime_seconds: int = 300
    log_dir: str = "data/logs"

def load_config(config_path: str) -> RunConfig:
    """Load a configuration from a JSON file."""
    with open(config_path, 'r') as f:
        config_data = json.load(f)
    
    agent_configs = []
    for agent_data in config_data.get("agents", []):
        agent_configs.append(AgentConfig(
            id=agent_data.get("id"),
            provider=agent_data.get("provider"),
            model=agent_data.get("model"),
            parameters=agent_data.get("parameters", {})
        ))
    
    return RunConfig(
        theorem_file=config_data.get("theorem_file"),
        num_agents=config_data.get("num_agents", len(agent_configs)),
        agent_configs=agent_configs,
        lean_path=config_data.get("lean_path", "lean"),
        file_dir=config_data.get("file_dir", ""),
        max_runtime_seconds=config_data.get("max_runtime_seconds", 300),
        log_dir=config_data.get("log_dir", "data/logs")
    )

def save_config(config: RunConfig, config_path: str) -> None:
    """Save a configuration to a JSON file."""
    config_data = {
        "theorem_file": config.theorem_file,
        "num_agents": config.num_agents,
        "lean_path": config.lean_path,
        "file_dir": config.file_dir,
        "max_runtime_seconds": config.max_runtime_seconds,
        "log_dir": config.log_dir,
        "agents": []
    }
    
    for agent_config in config.agent_configs:
        agent_data = {
            "id": agent_config.id,
            "provider": agent_config.provider,
            "model": agent_config.model,
            "parameters": agent_config.parameters
        }
        config_data["agents"].append(agent_data)
    
    with open(config_path, 'w') as f:
        json.dump(config_data, f, indent=2)
