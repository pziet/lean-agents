#!/bin/bash

# This script verifies a Lean proof by running lake lean on the specified file
# Usage: ./check_proof.sh <lean_project_path> <proof_file>

LEAN_PATH=$1
PROOF_FILE=$2

if [ -z "$LEAN_PATH" ] || [ -z "$PROOF_FILE" ]; then
  echo "Error: Missing required arguments"
  echo "Usage: ./check_proof.sh <lean_project_path> <proof_file>"
  exit 1
fi

# Change to the Lean project directory
cd "$LEAN_PATH" || { echo "Error: Failed to change to directory $LEAN_PATH"; exit 1; }
# Print the current directory
echo "Current directory: $(pwd)"

# Run lake lean on the proof file
echo "Checking proof: $PROOF_FILE"
lake lean "$PROOF_FILE"

# Capture the exit status
EXIT_STATUS=$?

if [ $EXIT_STATUS -eq 0 ]; then
  echo "PROOF_SUCCESS: Verification successful"
  exit 0
else
  echo "PROOF_FAILURE: Verification failed with exit code $EXIT_STATUS"
  exit $EXIT_STATUS
fi
