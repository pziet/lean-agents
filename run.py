import sys
import os
from agent_harness import load_config, MainCoordinator

def main():
    if len(sys.argv) < 2:
        print("[run] Usage: python run.py <config_file>")
        return
    
    config_file = sys.argv[1]
    if not os.path.exists(config_file):
        print(f"[run] Config file not found: {config_file}")
        return
    
    # Load configuration
    config = load_config(config_file)
    
    # Create and run the coordinator
    coordinator = MainCoordinator(config)
    coordinator.run_for_duration()

if __name__ == "__main__":
    main()
