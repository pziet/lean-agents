# Polanyi’s Republic of Science in Lean: A Multi-Agent Proof Collaboration Harness

## Project Task Checklist

- [ ] **Set up Lean Project**  
  - Create and configure `theorems.lean` with a main theorem plus sub-lemmas.
  - Verify that Lean can compile your initial theorem structure.

- [ ] **Implement Agent Harness**  
  - Build the `main_coordinator.py` or equivalent entry point.
  - Create a `base_agent.py` class and specialized agent classes (`specialized_agent.py`, `llm_agent.py`, etc.).
  - Define and document the agent–Lean interface.

- [ ] **Establish Coordination Mechanism**  
  - Implement a shared folder (`proven/`) or event bus to broadcast new proofs.
  - Ensure agents can detect and utilize newly proven lemmas.

- [ ] **Add Logging & Evaluation**  
  - Create a logging system to record agent decisions, proof attempts, and successes.
  - Design a simple evaluation script to measure proof times, success rates, and duplication.

- [ ] **Optional: LLM Integration**  
  - Plug in an LLM agent that uses prompt engineering to propose Lean tactics or proof steps.
  - Create a prompt template structure for consistent and reproducible results.

- [ ] **Testing & QA**  
  - Write unit tests for agent logic, Lean interface, and event bus.
  - Perform end-to-end tests to ensure the system can prove basic theorems collaboratively.

- [ ] **Containerization (Optional)**  
  - Add a Dockerfile or docker-compose setup to run multiple agents in separate containers.
  - Document how to deploy or scale the system.

---

## Project Overview

This project implements a small multi-agent system where each “agent” works on sub-lemmas of a theorem in **Lean**. Inspired by Michael Polanyi’s notion of a spontaneous, decentralized “Republic of Science,” the agents collaborate implicitly: whenever one solves a lemma, it publishes the result so others can build on it.

### Core Ideas
- **Lean Theorem Prover**: Offers a concrete, formal environment for stating and proving theorems.
- **Multi-Agent Harness**: Manages concurrency and communication. Each agent can have a distinct “personality” (e.g., a tactic-based solver or an LLM-based solver).
- **Shared Knowledge Base**: When an agent proves a sub-lemma, it’s stored in the `proven/` directory. Other agents detect it and integrate it into their own proofs.
- **Emergent Coordination**: Agents pivot to new tasks or share intermediate results upon discovering that a related lemma is already solved by another agent.

### Repository Structure
```bash
lean-agents/ 
├── README.md 
├── docs/ 
│ └── design_overview.md 
├── lean/ 
│ ├── theorems.lean 
│ ├── proven/ 
│ └── LeanProject.toml 
├── agent_harness/ 
│ ├── main_coordinator.py 
│ ├── base_agent.py 
│ ├── specialized_agent.py 
│ ├── llm_agent.py 
│ ├── lean_interface.py 
│ └── event_bus.py 
├── scripts/ 
│ ├── run_agents.sh 
│ ├── run_evaluation.sh 
│ └── docker-compose.yml 
├── Dockerfile 
├── requirements.txt 
├── tests/ 
│ ├── test_harness.py 
│ ├── test_agents.py 
│ └── test_lean_integration.py 
├── data/ 
│ ├── logs/ 
│ └── db/ 
└── .gitignore
```


### Getting Started

1. **Install Dependencies**  
   - Ensure you have Lean (≥ version 3.x or 4.x depending on your setup).  
   - Install Python packages (if using Python) with `pip install -r requirements.txt` or set up a virtual environment.  
   - If using an LLM-based agent, ensure you have access to an appropriate API key or local model.

2. **Initialize Lean**  
   - In the `lean/` directory, run `leanpkg configure` or the relevant commands for your Lean version.

3. **Run Agents**  
   - Use `scripts/run_agents.sh` (or `python agent_harness/main_coordinator.py`) to start the multi-agent process.  
   - Agents will attempt to prove sub-lemmas and log progress in `data/logs/`.

4. **Evaluate Results**  
   - Use `scripts/run_evaluation.sh` or a Python script to analyze logs and generate a summary of proof success and agent behaviors.

5. **Contribute**  
   - Submit issues or feature requests.  
   - PRs are welcome to improve agent strategies, logging systems, or expand the theorem library.
