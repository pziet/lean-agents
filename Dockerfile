# Use an official Python image as the base (Debian-based slim image for small size)
FROM python:3.10-slim-buster

# Install system dependencies needed for Lean 4 and its build tool (Lake).
# - curl and git: to download Lean installer and math libraries
# - clang and libgmp-dev: compilers/libraries Lean might need when building mathlib or proofs
RUN apt-get update && apt-get install -y \
    curl git clang libgmp-dev \
  && rm -rf /var/lib/apt/lists/*

# Install Lean 4 using the official Lean installer (elan).
# This will install the latest stable Lean 4 and the `lake` build tool.
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | bash -s -- -y

# Add Lean (elan) to PATH for subsequent commands and container runtime
ENV PATH="/root/.elan/bin:${PATH}"

# Set the working directory in the container
WORKDIR /lean-agents

# Copy Python dependency specification first (for caching)
COPY requirements.txt ./

# Install Python dependencies
RUN pip install --no-cache-dir -r requirements.txt

# Copy the rest of the project files into the container
COPY . /lean-agents

# Pre-build your consolidated `theorems` Lean package
RUN cd theorems && lake build

# The default command to run when the container starts:
# here we run the Python multi-agent simulation.
CMD ["python", "run.py"]
