# Test Harness

This directory contains unit tests for the `agent_harness` package, including configuration loading/saving, event bus functionality, Lean interface operations, and agent creation.

## Prerequisites

- Python 3.8 or higher
- Install required packages in your environment. From the project root, run:
  ```bash
  pip install -r requirements.txt
  ```

## Running Tests

Run all tests using [pytest]:

```bash
pytest
```

To run a single test file, specify its path. For example:

```bash
pytest tests/test_harness.py
```

For a concise test run with minimal output and fast failure on first error, use:

```bash
pytest --maxfail=1 --disable-warnings -q
```

## Test Files

- `test_harness.py`: Tests for config loading/saving and `EventBus` behavior.
- `test_lean_integration.py`: Tests for `LeanInterface` directory setup and file operations.
- `test_agents.py`: Tests for agent factory function and agent class instantiation.

[pytest]: https://docs.pytest.org/en/latest/