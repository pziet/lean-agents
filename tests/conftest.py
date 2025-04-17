import sys
import os

# Add project root to sys.path to allow direct imports of agent_harness
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# Stub out external dependencies if not installed
import types
for _mod in ("anthropic", "openai", "requests"):  # modules required by agents
    if _mod not in sys.modules:
        try:
            __import__(_mod)
        except ImportError:
            sys.modules[_mod] = types.ModuleType(_mod)