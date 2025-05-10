#!/usr/bin/env python3
"""
Benchmark script for SAT solvers - This script runs a complete experiment and generates
tables for the experimental results section of the paper.
"""

import os
import subprocess
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# Directory for saving results
RESULTS_DIR = "benchmark_results"
os.makedirs(RESULTS_DIR, exist_ok=True)

# Directory for saving generated instances
INSTANCES_DIR = "instances"
os.makedirs(INSTANCES_DIR, exist_ok=True)

# Configuration
VAR_SIZES = [110, 120, 130, 140, 150]
INSTANCES_PER_SIZE = 5
CLAUSE_RATIO = 4.2  # Near the phase transition for random 3-SAT


def generate_instances():
    """Generate random SAT instances for benchmarking"""
    print("Generating random 3-SAT instances...")

    for n in VAR_SIZES:
        size_dir = os.path.join(INSTANCES_DIR, f"vars_{n}")
        os.makedirs(size_dir, exist_ok=True)

        for i in range(INSTANCES_PER_SIZE):
            output_file = os.path.join(size_dir, f"random_{n}_{CLAUSE_RATIO}_{i + 1}.cnf")

            if os.path.exists(output_file):
                print(f"Instance already exists: {output_file}")
                continue

            print(f"Generating instance with {n} variables ({i + 1}/{INSTANCES_PER_SIZE})")
            cmd = [
                "python", "sat_solvers.py", output_file,
                "--generate", str(n),
                "--ratio", str(CLAUSE_RATIO),
                "--output", output_file
            ]
            subprocess.run(cmd, check=True)

    print("Instance generation complete.")


def run_benchmarks():
    """Run benchmarks on all instances"""
    print("Running benchmarks on all instances...")

    # CSV file for full results
    csv_file = os.path.join(RESULTS_DIR, "benchmark_results.csv")

    for n in VAR_SIZES:
        size_dir = os.path.join(INSTANCES_DIR, f"vars_{n}")

        # Skip if directory doesn't exist
        if not os.path.exists(size_dir):
            print(f"Warning: Directory {size_dir} not found. Skipping.")
            continue

        print(f"\nBenchmarking instances with {n} variables...")

        # Run benchmark on all instances in this directory
        cmd = [
            "python", "sat_solvers.py", size_dir,
            "--solver", "both",
            "--benchmark", csv_file
        ]
        subprocess.run(cmd, check=True)

    print(f"Benchmarks complete. Full results saved to {csv_file}")
    return csv_file


def generate_tables(csv_file):
    """Generate tables for the paper from benchmark results"""
    print("Generating tables for paper...")

    # Load benchmark results
    df = pd.read_csv(csv_file)

    # Group by number of variables
    grouped = df.groupby('n_vars')

    # Prepare summary dataframe
    summary = pd.DataFrame(index=VAR_SIZES, columns=[
        'm_clauses',
        'dpll_decisions', 'dpll_conflicts', 'dpll_time', 'dpll_memory',
        'probsat_flips', 'probsat_time', 'probsat_memory',
        'sat_instances'
    ])

    # Compute averages
    for n, group in grouped:
        if n not in summary.index:
            continue

        # collect stats into summary
        summary.loc[n, 'm_clauses'] = group['n_clauses'].mean()
        summary.loc[n, 'dpll_decisions'] = group['dpll_decisions'].mean()
        summary.loc[n, 'dpll_conflicts'] = group['dpll_conflicts'].mean()
        summary.loc[n, 'dpll_time'] = group['dpll_time'].mean()
        summary.loc[n, 'probsat_flips'] = group['probsat_flips'].mean()
        summary.loc[n, 'probsat_time'] = group['probsat_time'].mean()
        summary.loc[n, 'sat_instances'] = group['dpll_sat'].sum()
        summary.loc[n, 'dpll_memory'] = group['dpll_memory'].mean()
        summary.loc[n, 'probsat_memory'] = group['probsat_memory'].mean()
    # ensure memory columns are numeric
    summary[['dpll_memory', 'probsat_memory']] = summary[['dpll_memory', 'probsat_memory']].apply(pd.to_numeric)

    plt.figure(figsize=(8, 4))
    plt.plot(summary.index, summary['dpll_memory'],
             marker='o', linestyle='-', label='DPLL Memory (KB)')
    plt.plot(summary.index, summary['probsat_memory'],
             marker='s', linestyle='--', label='ProbSAT Memory (KB)')
    plt.xlabel('Number of Variables')
    plt.ylabel('Memory Usage (KB)')
    plt.title('Memory Usage vs Problem Size')

    # choose one:
    # plt.yscale('linear')  # if DPLL line is getting flattened by log scale
    plt.yscale('log')  # default log

    plt.grid(True, alpha=0.3)
    plt.legend()
    plt.tight_layout()

    plt.savefig(os.path.join(RESULTS_DIR, 'memory_usage.png'), dpi=300)
    plt.close()

    # optional sanity check
    print("Memory summary:\n", summary[['dpll_memory', 'probsat_memory']])

    # Save summary table
    summary.to_csv(os.path.join(RESULTS_DIR, "summary_table.csv"))

    # Generate LaTeX table for random SAT instances (Table 1)
    with open(os.path.join(RESULTS_DIR, "table1_random_sat.tex"), 'w') as f:
        f.write("\\begin{table}[h!]\n")
        f.write("\\centering\n")
        f.write("\\resizebox{\\textwidth}{!}{%\n")
        f.write("\\begin{tabular}{c|cccccccc}\n")  # 9 columns now
        f.write("\\hline\n")
        f.write(
            "$n$ (vars) & $m$ (clauses) & DPLL dec. & DPLL conf. & DPLL mem (KB) & ProbSAT flips & ProbSAT mem (KB) & DPLL time (s) & ProbSAT time (s) \\\\\n")
        f.write("\\hline\n")

        for n in VAR_SIZES:
            if n in summary.index:
                row = summary.loc[n]
                f.write(
                    f"{n} & {row['m_clauses']:.1f} & {row['dpll_decisions']:.1f} & {row['dpll_conflicts']:.1f} & "
                    f"{row['dpll_memory']:.1f} & {row['probsat_flips']:.1f} & {row['probsat_memory']:.1f} & "
                    f"{row['dpll_time']:.6f} & {row['probsat_time']:.6f} \\\\\n")

        f.write("\\hline\n")
        f.write("\\end{tabular}%\n")
        f.write("}\n")

        f.write(
            "\\caption{Performance comparison on random 3-SAT instances with approximately $4.2n$ clauses. "
            "Each value is averaged over 5 instances. Memory is measured as peak resident set size in KB.}\n")
        f.write("\\label{tab:random_sat}\n")
        f.write("\\end{table}\n")

    print(f"LaTeX table for random SAT instances saved to {os.path.join(RESULTS_DIR, 'table1_random_sat.tex')}")

    # Create a figure showing scaling behavior
    plt.figure(figsize=(10, 6))

    # DPLL decisions
    plt.subplot(2, 2, 1)
    plt.plot(summary.index, summary['dpll_decisions'], 'o-', label='DPLL Decisions')
    plt.yscale('log')
    plt.xlabel('Number of Variables')
    plt.ylabel('Average Decisions (log scale)')
    plt.title('DPLL Decisions vs Problem Size')
    plt.grid(True, alpha=0.3)

    # ProbSAT flips
    plt.subplot(2, 2, 2)
    plt.plot(summary.index, summary['probsat_flips'], 'o-', color='orange', label='ProbSAT Flips')
    plt.yscale('log')
    plt.xlabel('Number of Variables')
    plt.ylabel('Average Flips (log scale)')
    plt.title('ProbSAT Flips vs Problem Size')
    plt.grid(True, alpha=0.3)


    # Runtime comparison
    plt.subplot(2, 1, 2)
    plt.plot(summary.index, summary['dpll_time'], 'o-', label='DPLL')
    plt.plot(summary.index, summary['probsat_time'], 'o-', color='orange', label='ProbSAT')
    plt.yscale('log')
    plt.xlabel('Number of Variables')
    plt.ylabel('Average Runtime (seconds, log scale)')
    plt.title('Runtime Comparison')
    plt.legend()
    plt.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(RESULTS_DIR, 'scaling_figure.png'), dpi=300)
    print(f"Scaling figure saved to {os.path.join(RESULTS_DIR, 'scaling_figure.png')}")


def main():
    """Main function to run the complete benchmark"""
    print("=== SAT Solver Benchmark Suite ===")

    # Step 1: Generate random instances
    generate_instances()

    # Step 2: Run benchmarks
    csv_file = run_benchmarks()

    # Step 3: Generate tables and figures
    generate_tables(csv_file)

    print("\nBenchmark complete!")
    print(f"Results saved to {RESULTS_DIR}")


if __name__ == "__main__":
    main()