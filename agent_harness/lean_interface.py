"""
Interface for interaction with the Lean theorem prover.
Provides methods to check and compile proofs.
"""
import os
import time
import subprocess
from typing import Tuple, Optional, List


class LeanInterface:
    def __init__(self, lean_path: str, file_dir: str):
        self.lean_path = lean_path
        self.file_dir = file_dir
        self.stubs_dir = os.path.join(self.lean_path, self.file_dir, "stubs")
        self.attempts_dir = os.path.join(self.lean_path, self.file_dir, "attempts")
        self.proven_dir = os.path.join(self.lean_path, self.file_dir, "proven")

        # Create directories if they don't exist
        if not os.path.exists(self.attempts_dir):
            os.makedirs(self.attempts_dir)
        if not os.path.exists(self.proven_dir):
            os.makedirs(self.proven_dir)
        if not os.path.exists(self.stubs_dir):
            os.makedirs(self.stubs_dir)
    
    def create_attempt_file(self, proof_script: str, lemma_id: str, agent_id: str) -> str:
        # Copy stub file to attempts/ with unique name
        # Return the path to the new attempt file

        fname = f"{lemma_id}_{agent_id}_{round(time.time())}.lean"
        attempt_file = os.path.join(self.attempts_dir, fname)
        with open(attempt_file, "w") as f:
            f.write(proof_script)
        return attempt_file

    def delete_attempt_file(self, attempt_file: str) -> None:
        """Delete a proof attempt file.
        
        Args:
            attempt_file: Path to the attempt file to delete
        """
        try:
            os.remove(attempt_file)
        except OSError as e:
            print(f"[lean_interface] Error deleting attempt file {attempt_file}: {e}")
    
    def check_proof(self, proof_script: str, lemma_id: str, agent_id: str) -> Tuple[bool, Optional[str]]:
        """
        Check if a proof script is valid using Lean.
        
        Args:
            proof_script: The Lean proof script to check
            lemma_id: Optional identifier for the lemma
            agent_id: Optional identifier for the agent
            
        Returns:
            A dictionary with the check results:
            {
                'success': bool,  # Whether the proof is valid
                'output': str,    # The output from lake lean
                'error': str      # Any error message
            }
        """
        try:
            attempt_file = self.create_attempt_file(proof_script, lemma_id, agent_id)
            
            # Get the path to the check_proof.sh script
            script_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            check_script = os.path.join(script_dir, "agent_harness", "shell", "check_proof.sh")
            
            # Make sure the script is executable
            os.chmod(check_script, 0o755)
            
            # Run the check_proof.sh script
            result = subprocess.run(
                [check_script, self.lean_path, attempt_file],
                capture_output=True,
                text=True
            )
            
            # Check if the proof is valid
            success = result.returncode == 0
    
            # Check for the special markers in the output
            output = result.stdout + result.stderr

            return {
                'success': success,
                'output': output,
                'error': result.stderr if not success else "",
                'file_path': attempt_file
            }
            
        except Exception as e:
            return {
                'success': False,
                'output': "",
                'error': str(e),
                'file_path': None
            }
        
        finally:
            self.delete_attempt_file(attempt_file)

    
    def save_proven_lemma(self, lemma_id: str, proof_script: str) -> str:
        """Save a proven lemma to the proven directory."""
        filename = f"{lemma_id}.lean"
        filepath = os.path.join(self.proven_dir, filename)
        print("================================================")
        print(f"[lean_interface] Saving proof for {lemma_id} to {filepath}")
        print("================================================")
        if os.path.exists(filepath):
            print(f"[lean_interface] Proof for {lemma_id} already exists at {filepath}")
            return None
        with open(filepath, 'w') as f:
            f.write(proof_script)
        
        print(f"[lean_interface] Saved proof for {lemma_id} to {filepath}")
        return filepath
    
    def get_available_lemmas(self) -> List[str]:
        """Get a list of lemmas from the theorem file that need to be proven."""
        stubs = {f.replace('.lean', '') for f in os.listdir(self.stubs_dir)}
        proven = {f.replace('.lean', '') for f in os.listdir(self.proven_dir)}
        return sorted(list(stubs - proven))

    def get_proven_lemmas(self) -> List[str]:
        """Get a list of proven lemmas."""
        return sorted(list(os.listdir(self.proven_dir)))

    def get_file(self, lemma_name: str, file_type: str = "stubs") -> str:
        """Get a lemma file from either stubs or proven directory.
        
        Args:
            lemma_id: The ID of the lemma
            file_type: Either "stubs" or "proven"
        """
        file_path = os.path.join(self.lean_path, self.file_dir, file_type, f"{lemma_name}.lean")
        print(f"[lean_interface] Getting {file_type} file: {file_path}")
        with open(file_path, "r") as f:
            return f.read()

    def delete_proven_lemmas(self) -> None:
        """Delete all proven lemmas."""
        for file in os.listdir(self.proven_dir):
            os.remove(os.path.join(self.proven_dir, file))
