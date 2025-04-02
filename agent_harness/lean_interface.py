"""
Interface for interaction with the Lean theorem prover.
Provides methods to check and compile proofs.
"""
import os
import subprocess
from typing import Tuple, Optional, List


# Requirements:
# - Overwrite lean files 
# - Attempt to build the proofs
# - View which statements have been proven or are still open


class LeanInterface:
    def __init__(self, lean_path: str, theorem_file: str):
        self.lean_path = lean_path
        self.theorem_file = theorem_file
        self.proven_dir = os.path.join(os.path.dirname(theorem_file), "proven")
        
        # Create proven directory if it doesn't exist
        if not os.path.exists(self.proven_dir):
            os.makedirs(self.proven_dir)
    
    def check_proof(self, proof_script: str) -> Tuple[bool, Optional[str]]:
        """Check if a proof script is valid using Lean."""
        # This is a placeholder - real implementation would use Lean CLI
        # Return (success, error_message)
        print(f"Checking proof: {proof_script[:50]}...")
        return True, None
    
    def save_proven_lemma(self, lemma_id: str, proof: str) -> str:
        """Save a proven lemma to the proven directory."""
        filename = f"{lemma_id}.lean"
        filepath = os.path.join(self.proven_dir, filename)
        
        with open(filepath, 'w') as f:
            f.write(proof)
        
        print(f"Saved proof for {lemma_id} to {filepath}")
        return filepath
    
    def get_available_lemmas(self) -> List[str]:
        """Get a list of lemmas from the theorem file that need to be proven."""
        # This is a placeholder - real implementation would parse the theorem file
        return ["lemma1", "lemma2", "lemma3", "lemma4"]


