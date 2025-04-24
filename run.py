# run_experiments.py
import os
import glob
import argparse
import time
from itertools import product

import logging
import logging.config
import json

from agent_harness.config import load_config
from agent_harness.main_coordinator import MainCoordinator

logger = logging.getLogger(__name__)

# --- Configuration ---
DEFAULT_CONFIG_DIR = "configs"
DEFAULT_MATH_DIR_BASE = "theorems/Theorems"  # Base directory containing theorem sets (relative to project root)
DEFAULT_LOG_DIR = "data/logs/run_logs"
DEFAULT_NSIM = 5
# TODO: consider adding "partial-polanyi"
STRATEGIES = ["polanyi", "anti-polanyi"]
with open("/lean-agents/data/logs/logging.json", "r") as f:
    logging_config = json.load(f)
logging.config.dictConfig(logging_config)

# --- End Configuration ---

def discover_configs(config_dir: str) -> list[str]:
    """Find all JSON config files."""
    return glob.glob(os.path.join(config_dir, "*.json"))

def discover_theorem_sets(math_dir_base: str) -> list[str]:
    """Find theorem set directories (e.g., 'Mock') within the base math directory."""
    return [d for d in os.listdir(math_dir_base)
            if os.path.isdir(os.path.join(math_dir_base, d)) and d != 'Definitions']

def run_single_experiment(config_path: str, theorem_set: str, strategy: str, run_number: int, math_dir_base: str, base_log_dir: str):
    """Loads config, sets up logging, and runs one simulation."""
    config_name = os.path.splitext(os.path.basename(config_path))[0]

    # Define the specific log directory and file for this run
    run_log_dir = os.path.join(base_log_dir, config_name, theorem_set, strategy)
    run_log_file = os.path.join(run_log_dir, f"run_{run_number}.log")
    # --- Skip Logic ---
    if os.path.exists(run_log_file):
        logger.info("Skipping: Config= %s, TheoremSet= %s, Run= %s (Log exists: %s)", config_name, theorem_set, run_number, run_log_file)
        return

    logger.info("Starting: Config= %s, TheoremSet= %s, Run= %s", config_name, theorem_set, run_number)

    # Ensure the specific log directory exists
    os.makedirs(run_log_dir, exist_ok=True)

    # Load the base configuration
    config = load_config(config_path)
    config.strategy = strategy
    logger.info("Config strategy: %s", config.strategy)
    # Override relevant fields for this specific run
    config.lean_path = math_dir_base  # Point to the base math directory
    config.file_dir = theorem_set
    logger.info("Config file dir: %s", config.file_dir)
    config.log_dir = run_log_dir     # Pass the specific directory for this run's logs
    # Pass the specific log *file* name (optional, depends on MainCoordinator modification)
    # Add custom attribute for log file naming in coordinator if needed
    setattr(config, 'log_file_name', f"run_{run_number}.log")

    # Initialize and run the coordinator
    try:
        coordinator = MainCoordinator(config)
        # You might want run_for_duration or another method depending on desired behavior
        coordinator.run_for_duration()
        logger.info("Finished: Config= %s, TheoremSet= %s, Run= %s", config_name, theorem_set, run_number)
    except Exception as e:
        logger.error("Error during run: Config= %s, TheoremSet= %s, Run= %s", config_name, theorem_set, run_number)
        logger.error("Error details: %s", e)
        # Optionally log the error to a separate file or handle it
    finally:
        # Potential cleanup if needed
        pass


def main():
    parser = argparse.ArgumentParser(description="Run agent harness experiments.")
    parser.add_argument("--config_dir", default=DEFAULT_CONFIG_DIR, help="Directory containing configuration files.")
    parser.add_argument("--math_dir", default=DEFAULT_MATH_DIR_BASE, help="Base directory containing theorem sets (e.g., theorems/Theorems/).")
    parser.add_argument("--log_dir", default=DEFAULT_LOG_DIR, help="Base directory for saving logs.")
    parser.add_argument("--nsim", type=int, default=DEFAULT_NSIM, help="Number of simulations per config/theorem set.")
    args = parser.parse_args()

    start_time = time.time()
    logger.info("Starting experiment runs at %s", time.strftime('%Y-%m-%d %H:%M:%S'))
    logger.info("Config Dir: %s", args.config_dir)
    logger.info("Math Dir: %s", args.math_dir)
    logger.info("Log Dir: %s", args.log_dir)
    logger.info("Simulations per combination (NSIM): %s", args.nsim)

    config_files = discover_configs(args.config_dir)
    theorem_sets = discover_theorem_sets(args.math_dir)
    # remove mock
    theorem_sets = [t for t in theorem_sets if t != "mock"]
    logger.info("Theorem sets: %s", theorem_sets) 
    if not config_files:
        logger.error("No config files found in %s", args.config_dir)
        return
    if not theorem_sets:
        logger.error("No theorem sets (subdirectories) found in %s", args.math_dir)
        return

    logger.info("Found %s configs and %s theorem sets.", len(config_files), len(theorem_sets))

    total_runs = len(config_files) * len(theorem_sets) * len(STRATEGIES) * args.nsim
    current_run = 0

    for config_path, theorem_set, strategy in product(config_files, theorem_sets, STRATEGIES):
        for run_number in range(1, args.nsim + 1):
            current_run += 1
            logger.info("\n--- Progress: Run %s/%s ---", current_run, total_runs)
            run_single_experiment(
                config_path=config_path,
                theorem_set=theorem_set,
                strategy=strategy,
                run_number=run_number,
                math_dir_base=args.math_dir,
                base_log_dir=args.log_dir
            )

    end_time = time.time()
    logger.info("All experiments finished in %s seconds.", end_time - start_time)


if __name__ == "__main__":
    main()