import os
import pytest

from agent_harness.config import AgentConfig
from agent_harness.event_bus import EventBus
from agent_harness.lean_interface import LeanInterface
from agent_harness.agents import create_agent, OpenAIAgent, KiminaAgent

@pytest.fixture
def event_bus():
    return EventBus()

@pytest.fixture
def lean_interface(tmp_path):
    # Use file_dir="" so directories are under lean_path directly
    return LeanInterface(str(tmp_path), "")

def test_create_openai_agent(event_bus, lean_interface, monkeypatch):
    # Set dummy OPENAI_API_KEY
    monkeypatch.setenv("OPENAI_API_KEY", "testkey")
    config = AgentConfig(id="agent1", provider="openai", model="gpt-3", parameters={"p": 1})
    agent = create_agent(config, event_bus, lean_interface, strategy="test")
    assert isinstance(agent, OpenAIAgent)
    assert agent.agent_id == "agent1"
    assert agent.model == "gpt-3"
    assert agent.strategy == "test"


def test_create_kimina_agent(event_bus, lean_interface, monkeypatch):
    # Set dummy Kimina env vars
    monkeypatch.setenv("KIMINA_API_URL", "http://test")
    monkeypatch.setenv("KIMINA_API_KEY", "key")
    config = AgentConfig(id="agent3", provider="kimina", model="kimina-model", parameters={})
    agent = create_agent(config, event_bus, lean_interface, strategy="s")
    assert isinstance(agent, KiminaAgent)
    assert agent.agent_id == "agent3"
    assert agent.model == "kimina-model"

def test_create_agent_unknown_provider(event_bus, lean_interface):
    config = AgentConfig(id="x", provider="unknown", model="m", parameters={})
    with pytest.raises(ValueError):
        create_agent(config, event_bus, lean_interface, strategy=None)
