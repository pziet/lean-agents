# Design Overview: Polanyi’s Republic of Science in Lean

## 1. Introduction

This document provides a deeper look into the architecture, rationale, and implementation details of the **multi-agent theorem-proving harness** inspired by Michael Polanyi’s “Republic of Science.” The goal is to demonstrate emergent coordination among agents working on Lean theorems.

---

## 2. Inspiration: Polanyi’s Republic of Science

Michael Polanyi likened science to a decentralized, spontaneous order of researchers—each pursuing their own interests, yet collectively driving progress by publishing and using each other’s results. In our system:

- **Scientists** → **Agents**  
- **New discoveries** → **Proven sub-lemmas**  
- **Publication** → **Writing lemma proofs to the `proven/` folder**  
- **Usage / Citation** → **Incorporating discovered lemmas in further proofs**  

Progress emerges organically as agents “notice” that a sub-lemma they need has been published.

---

## 3. System Architecture

### 3.1 High-Level Diagram

+---------------------+ +-------------------------+ | Lean Environment | <------>| Agent Harness (Python) | | (theorems.lean) | | | | | | - main_coordinator.py | | - Lean CLI/server | | - base_agent.py | | - proven/ folder | | - specialized_agent.py | +---------------------+ | - llm_agent.py | | - lean_interface.py | | - event_bus.py | +-------------------------+


- **Lean Environment**: Contains your statement of the main theorem plus sub-lemmas. Compiling new proofs updates the “shared knowledge base.”  
- **Agent Harness**: Python modules that spawn and coordinate multiple agent processes/threads, each with distinct solving strategies.

---

### 3.2 Agents

- **BaseAgent**  
  - An abstract class/interface that outlines methods for picking sub-lemmas, attempting proofs, and responding to newly proven lemmas.

- **SpecializedAgent**  
  - Uses a particular proof strategy or set of Lean tactics (e.g., rewriting tactics, known lemma applications, etc.).

- **LLMAgent** (Optional)  
  - Integrates a Large Language Model to generate proof ideas or full Lean tactic scripts.  
  - Uses carefully crafted prompt templates to guide the LLM output.

---

### 3.3 Coordination

- **Shared Folder**:  
  - Agents periodically check `proven/` for newly proven lemmas.  
  - Whenever a lemma is proven, the successful agent writes the proof into `proven/`, notifies the harness, and other agents can incorporate it.

- **Event Bus (Optional)**:  
  - A pub/sub mechanism where each agent subscribes to “LemmaProven” events, ensuring near-real-time updates.

---

### 3.4 Logging and Observability

- **Logging**  
  - Each agent logs major events (started lemma X, proved lemma Y, failed attempt, etc.).  
  - The main coordinator aggregates logs in `data/logs/`.

- **Evaluation**  
  - A separate script or process reads the logs to generate statistics such as:
    - Time to solve each sub-lemma.
    - Number of attempts made.
    - Collaboration metrics (e.g., how often agents used another’s lemma).

---

## 4. Implementation Details

### 4.1 Lean Integration

- **`lean_interface.py`**  
  - Wraps calls to the Lean CLI or language server.  
  - Allows agents to compile partial proofs, check if a lemma is proven, etc.

- **Proof Publication**  
  - Once a lemma is successfully proven, the harness commits it to the `proven/` folder (or updates a single aggregated file).  
  - Other agents see the updated environment on the next cycle.

---

### 4.2 Multi-Agent Orchestration

- **`main_coordinator.py`**  
  - Spawns multiple agent instances as threads or processes.  
  - Maintains a global list or DB of sub-lemmas to assign.  
  - Monitors the system’s overall progress (i.e., how many lemmas remain unproven).

- **Scheduling**  
  - Agents can “bid” on sub-lemmas or be assigned them in round-robin fashion.  
  - Agents that find themselves blocked can check if other lemmas are newly proven.

---

### 4.3 LLM Integration

- **`llm_agent.py`**  
  - Manages prompt engineering. For instance:
    ```
    System Prompt: You are a Lean theorem-proving assistant.
    Assistant: ...
    ```
  - Interprets the LLM output, injects it as tactics in Lean, tests for success/failure, and logs the result.

---

## 5. Deployment & Scaling

- **Docker**  
  - Each agent can be containerized. A shared volume or small database (Redis, SQLite) can store proven lemmas.

- **Resource Constraints**  
  - CPU/memory for each agent can be limited if you want to simulate large-scale concurrency in an enterprise setting.

---

## 6. Future Extensions

1. **Reinforcement Learning**  
   - Agents learn a policy for selecting sub-lemmas or proof tactics.
2. **Automated Lemma Discovery**  
   - LLM suggests potential mid-level lemmas that are not explicitly stated.
3. **Visualization**  
   - Create a real-time dashboard showing which agent is working on which lemma and the status (unproven, proven, or in progress).

---

## 7. Conclusion

This project illustrates how multi-agent collaboration, inspired by Polanyi’s decentralized “Republic of Science,” can be reproduced in a theorem-proving environment like Lean. By giving each agent independence yet providing a shared space for proven lemmas, collective progress emerges—demonstrating the benefits of spontaneous coordination without a single global controller.
