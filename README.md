**Animation**: [pziet.com/lean](https://pziet.com/lean) **Demo**: [video](https://youtu.be/0SbunyqpFvQ)<br>
**Updates**: Added [tests](https://github.com/pziet/lean-agents/blob/main/tests/README.md), Docker, and logging
# Polanyi’s Republic of Science in Lean: A Multi-Agent Proof Collaboration Harness

This project implements a small multi-agent system where each “agent” works on sub-lemmas of a theorem in [Lean 4](https://lean-lang.org/). Inspired by Michael Polanyi’s notion of a spontaneous, decentralized [*Republic of Science*](https://www.polanyisociety.org/mp-repsc.htm), the agents collaborate implicitly: whenever one solves a lemma, it publishes the result so others can build on it.

We test the strategies of sharing context and information, called `polanyi`, versus keeping agents siloed, called `anti-polanyi`.

## Quick Start

Prerequisites:
- Docker (20.10+)
- Docker Compose plugin (optional, but recommended)
- Copy and configure environment variables:
  ```bash
  cp .env.example .env
  # Edit .env to add your OPENAI_API_KEY and optional LOG_LEVEL
  ```

1. **Build image** (only when dependencies change):
   ```bash
   docker compose build simulation
   ```
2. **Launch simulation** with hot‑reload and logging:
   ```bash
   docker compose up simulation
   ```
   - Automatically restarts `run.py` on edits to `*.py`, `*.json`, `*.yaml`, `*.toml` files.
   - Stops when all simulations complete (no restart on normal exit).
   - Logs to console and `data/logs/app.log` (rotated daily).
3. **View logs** in another terminal:
   ```bash
   tail -f data/logs/app.log
   ```
4. **Shutdown** the service:
   ```bash
   docker compose down
   ```

## Local Development (Without Docker)

If you prefer to run locally, ensure you have Lean 4 (via elan) and Python >=3.10 installed:
```bash
# Install Lean 4 via elan
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# Install Python dependencies
pip install -r requirements.txt

# Pre-build Lean packages
for pkg in math/*; do
  if [ -f "$pkg/lakefile.toml" ]; then
    cd "$pkg" && lake build && cd -;
  fi
done

# Run the multi-agent simulation
python run.py --config_dir configs --math_dir math --log_dir data/logs --nsim 5
```

### Results

Not suprisingly sharing information about other agent's attempts results in significant performance boost, however the agents do quite poorly considering how simple the theorems are. We used OpenAI's `gpt-4o-mini`.
| Number of Agents | `polanyi` | `anti-polanyi` |
|:-----------------:|:---------:|:--------------:|
|        1        |   1.9%    |       --      |
|        2        |   4.0%    |      0%       |
|        4        |   32.8%   |     4.1%      |

### Core Ideas
- **Lean Theorem Prover**: Offers a concrete, formal environment for stating and proving theorems.
- **Multi-Agent Harness**: Manages concurrency and communication. Each agent can have a distinct “personality” (e.g., a tactic-based solver or an LLM-based solver).
- **Shared Knowledge Base**: When an agent proves a sub-lemma, it’s stored in the `proven/` directory. Other agents detect it and integrate it into their own proofs.

An example, break down the simple statement that "If n, m are even then n^2 + m is even" into stubs using Lean's `sorry`: 
```
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

-- Prove that is n, m are even then n^2 + m is even
theorem even_square_plus_even (n m : ℕ) (hn : isEven n) (hm : isEven m) : isEven (n * n + m) := by
  sorry

def isEven (n: ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k

lemma even_square (n : ℕ) (hn : isEven n) : isEven (n * n) := by
  sorry

lemma even_plus_even (n m : ℕ) (hn : isEven n) (hm : isEven m) : isEven (n + m) := by
  sorry
```

Each of these would be selected by agent's and then assembled to prove the final theorem. 

### Repo overview

```bash
├── agent_harness
│   ├── agents.py
│   ├── config.py
│   ├── event_bus.py
│   ├── __init__.py
│   ├── lean_interface.py
│   ├── main_coordinator.py
│   └── shell
├── configs/
├── data
│   └── logs
├── theorems/
├── README.md
├── requirements.txt
└── run.py
```

- `agent_harness/`: Contains the Python code implementing the multi-agent harness.
   - `agents.py`: Defines the structure and logic for individual agents.
   - `config.py`: Loads and manages configuration parameters for the system.
   - `event_bus.py`: Implements a system for agents to communicate events (e.g., lemma proved).
   - `lean_interface.py`: Handles calls to the Lean prover to check proofs or get theorem states.
   - `main_coordinator.py`: Manages the lifecycle of agents and the overall proof process.
- `configs/`: Holds JSON configuration files, defining experiment parameters or agent settings.
- `data`: Used for storing output data generated during runs, most notably logs.
- `theorems/`: Contains the various Lean theorem statements being worked on, each structured with stubs, attempts, and proven lemmas.
- `run.py`: The entry point script used to launch the agent harness simulation.

### Extensions

- [x] Docker
- [ ] Test [Kimina-Prover](https://github.com/MoonshotAI/Kimina-Prover-Preview/tree/master) model. ([more](https://x.com/haimingw97/status/1912351985917128790?s=51) resources)
 - [X] Restructure `math/` Lean directories into a single Lean package
 - [X] Use `import logging`