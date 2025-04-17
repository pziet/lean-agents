import json
import pytest

from agent_harness.config import load_config, save_config, RunConfig
from agent_harness.event_bus import EventBus

def test_config_load_and_save(tmp_path):
    # Create sample config data
    config_data = {
        "theorem_file": "test.lean",
        "num_agents": 1,
        "lean_path": "/fake/lean",
        "file_dir": "dir",
        "strategy": "demo",
        "max_runtime_seconds": 100,
        "log_dir": "logs",
        "agents": [
            {"id": "agent1", "provider": "openai", "model": "gpt-3", "parameters": {"temperature": 0.5}}
        ]
    }
    config_file = tmp_path / "config.json"
    config_file.write_text(json.dumps(config_data))

    # Load config
    cfg = load_config(str(config_file))
    assert isinstance(cfg, RunConfig)
    assert cfg.theorem_file == "test.lean"
    assert cfg.num_agents == 1
    assert cfg.lean_path == "/fake/lean"
    assert cfg.file_dir == "dir"
    assert cfg.max_runtime_seconds == 100
    assert cfg.log_dir == "logs"
    # strategy is not loaded from file (default None)
    assert cfg.strategy is None
    assert len(cfg.agent_configs) == 1
    agent_cfg = cfg.agent_configs[0]
    assert agent_cfg.id == "agent1"
    assert agent_cfg.provider == "openai"
    assert agent_cfg.model == "gpt-3"
    assert agent_cfg.parameters == {"temperature": 0.5}

    # Save config and verify contents
    out_file = tmp_path / "out_config.json"
    save_config(cfg, str(out_file))
    saved = json.loads(out_file.read_text())
    assert saved["theorem_file"] == "test.lean"
    assert saved["num_agents"] == 1
    assert saved["lean_path"] == "/fake/lean"
    assert saved["file_dir"] == "dir"
    assert saved["strategy"] is None
    assert "agents" in saved and isinstance(saved["agents"], list)
    assert saved["agents"][0]["id"] == "agent1"

def test_event_bus_basic():
    bus = EventBus()
    results = []

    def callback(data):
        results.append(data)

    # Subscribe and publish
    bus.subscribe("event1", callback)
    bus.publish("event1", {"key": "value"})
    assert results == [{"key": "value"}]

    # History should record the event
    history = bus.get_history("event1")
    assert "event1" in history
    assert history["event1"][0]["data"] == {"key": "value"}

    # Unsubscribe and ensure callback is not called again
    bus.unsubscribe("event1", callback)
    results.clear()
    bus.publish("event1", {"key": "other"})
    assert results == []

def test_get_current_agent_activities():
    bus = EventBus()
    # Publish multiple AgentWorking events
    bus.publish("AgentWorking", {"agent_id": "A", "lemma_id": "L1"})
    bus.publish("AgentWorking", {"agent_id": "B", "lemma_id": "L2"})
    bus.publish("AgentWorking", {"agent_id": "A", "lemma_id": "L3"})
    activities = bus.get_current_agent_activities()
    assert activities == {"A": "L3", "B": "L2"}
