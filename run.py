# run_experiments.py
import os
import glob
import argparse
import time
from itertools import product

from agent_harness.config import load_config
from agent_harness.main_coordinator import MainCoordinator

# --- Configuration ---
DEFAULT_CONFIG_DIR = "configs"
DEFAULT_MATH_DIR_BASE = "/home/ztkpat001/repos/lean-agents/math" # Adjust if needed
DEFAULT_LOG_DIR = "data/logs"
DEFAULT_NSIM = 5
# TODO: consider adding "partial-polanyi"
STRATEGIES = ["polanyi", "anti-polanyi"]
# --- End Configuration ---

def discover_configs(config_dir: str) -> list[str]:
    """Find all JSON config files."""
    return glob.glob(os.path.join(config_dir, "*.json"))

def discover_theorem_sets(math_dir_base: str) -> list[str]:
    """Find theorem set directories (e.g., 'Mock') within the base math directory."""
    return [d for d in os.listdir(math_dir_base)
            if os.path.isdir(os.path.join(math_dir_base, d))]

def run_single_experiment(config_path: str, theorem_set: str, strategy: str, run_number: int, math_dir_base: str, base_log_dir: str):
    """Loads config, sets up logging, and runs one simulation."""
    config_name = os.path.splitext(os.path.basename(config_path))[0]

    # Define the specific log directory and file for this run
    run_log_dir = os.path.join(base_log_dir, config_name, theorem_set, strategy)
    run_log_file = os.path.join(run_log_dir, f"run_{run_number}.log")

    # --- Skip Logic ---
    if os.path.exists(run_log_file):
        print(f"[ExperimentRunner] Skipping: Config={config_name}, TheoremSet={theorem_set}, Run={run_number} (Log exists: {run_log_file})")
        return

    print(f"[ExperimentRunner] Starting: Config={config_name}, TheoremSet={theorem_set}, Run={run_number}")

    # Ensure the specific log directory exists
    os.makedirs(run_log_dir, exist_ok=True)

    # Load the base configuration
    config = load_config(config_path)
    print(f"Config strategy: {config.strategy}")
    config.strategy = strategy
    # Override relevant fields for this specific run
    config.lean_path = math_dir_base  # Point to the base math directory
    config.file_dir = os.path.join(theorem_set, ''.join(word.capitalize() for word in theorem_set.split('_')))    # Set the specific theorem directory (e.g., "Mock")
    print(f"Config file dir: {config.file_dir}")
    config.log_dir = run_log_dir     # Pass the specific directory for this run's logs
    # Pass the specific log *file* name (optional, depends on MainCoordinator modification)
    # Add custom attribute for log file naming in coordinator if needed
    setattr(config, 'log_file_name', f"run_{run_number}.log")

    # Initialize and run the coordinator
    try:
        coordinator = MainCoordinator(config)
        # You might want run_for_duration or another method depending on desired behavior
        coordinator.run_for_duration()
        print(f"[ExperimentRunner] Finished: Config={config_name}, TheoremSet={theorem_set}, Run={run_number}")
    except Exception as e:
        print(f"[ExperimentRunner] Error during run: Config={config_name}, TheoremSet={theorem_set}, Run={run_number}")
        print(f"Error details: {e}")
        # Optionally log the error to a separate file or handle it
    finally:
        # Potential cleanup if needed
        pass


def main():
    parser = argparse.ArgumentParser(description="Run agent harness experiments.")
    parser.add_argument("--config_dir", default=DEFAULT_CONFIG_DIR, help="Directory containing configuration files.")
    parser.add_argument("--math_dir", default=DEFAULT_MATH_DIR_BASE, help="Base directory containing theorem sets (e.g., math/).")
    parser.add_argument("--log_dir", default=DEFAULT_LOG_DIR, help="Base directory for saving logs.")
    parser.add_argument("--nsim", type=int, default=DEFAULT_NSIM, help="Number of simulations per config/theorem set.")
    args = parser.parse_args()

    start_time = time.time()
    print(f"[ExperimentRunner] Starting experiment runs at {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"[ExperimentRunner] Config Dir: {args.config_dir}")
    print(f"[ExperimentRunner] Math Dir: {args.math_dir}")
    print(f"[ExperimentRunner] Log Dir: {args.log_dir}")
    print(f"[ExperimentRunner] Simulations per combination (NSIM): {args.nsim}")

    config_files = discover_configs(args.config_dir)
    theorem_sets = discover_theorem_sets(args.math_dir)
    # remove mock
    theorem_sets = [t for t in theorem_sets if t != "mock"]
    print(f"Theorem sets: {theorem_sets}") 
    if not config_files:
        print(f"[ExperimentRunner] No config files found in {args.config_dir}")
        return
    if not theorem_sets:
        print(f"[ExperimentRunner] No theorem sets (subdirectories) found in {args.math_dir}")
        return

    print(f"[ExperimentRunner] Found {len(config_files)} configs and {len(theorem_sets)} theorem sets.")

    total_runs = len(config_files) * len(theorem_sets) * len(STRATEGIES) * args.nsim
    current_run = 0

    for config_path, theorem_set, strategy in product(config_files, theorem_sets, STRATEGIES):
        for run_number in range(1, args.nsim + 1):
            current_run += 1
            print(f"\n[ExperimentRunner] --- Progress: Run {current_run}/{total_runs} ---")
            run_single_experiment(
                config_path=config_path,
                theorem_set=theorem_set,
                strategy=strategy,
                run_number=run_number,
                math_dir_base=args.math_dir,
                base_log_dir=args.log_dir
            )

    end_time = time.time()
    print(f"\n[ExperimentRunner] All experiments finished in {end_time - start_time:.2f} seconds.")


if __name__ == "__main__":
    main()