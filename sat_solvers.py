import random
import time
import resource
import platform
import math
import psutil
import argparse
import sys
import os
from collections import defaultdict, Counter


class CNF:
    def __init__(self):
        self.clauses = []
        self.n_vars = 0
        self.n_clauses = 0
        self.var_to_clauses = defaultdict(list)  # Maps variable to clauses containing it

    def add_clause(self, clause):
        """Add a clause and update variable-to-clause mapping"""
        self.clauses.append(clause)
        for lit in clause:
            var = abs(lit)
            self.var_to_clauses[var].append(len(self.clauses) - 1)
            self.n_vars = max(self.n_vars, var)
        self.n_clauses = len(self.clauses)

    def from_dimacs(self, filename):
        """Parse a DIMACS CNF file"""
        with open(filename, 'r') as f:
            for line in f:
                line = line.strip()
                # Skip empty lines and comment lines (both 'c' and '%' are treated as comments)
                if not line or line.startswith('c') or line.startswith('%'):
                    continue
                if line.startswith('p cnf'):
                    parts = line.split()
                    self.n_vars = int(parts[2])
                    # Note: n_clauses will be counted as we read
                else:
                    try:
                        # Parse a clause: e.g., "1 -2 3 0" -> [1, -2, 3]
                        literals = [int(x) for x in line.split()]
                        if literals[-1] == 0:
                            literals.pop()  # Remove the trailing 0
                        if literals:  # Only add non-empty clauses
                            self.add_clause(literals)
                    except ValueError as e:
                        print(f"Warning: Could not parse line: '{line}' - {e}")

    def __str__(self):
        return f"CNF with {self.n_vars} variables and {self.n_clauses} clauses"


class DPLL:
    def __init__(self, cnf):
        self.cnf = cnf
        self.assignment = {}  # Current partial assignment
        self.decisions = 0  # Number of decision variables
        self.conflicts = 0  # Number of conflicts encountered
        self.start_time = 0

    def solve(self, verbose=False):
        """Run the DPLL algorithm and return (is_sat, assignment)"""
        self.decisions = 0
        self.conflicts = 0
        self.start_time = time.time()
        self.assignment = {}

        result = self._dpll({})
        elapsed = time.time() - self.start_time

        if verbose:
            if result:
                print(f"SAT: Found solution in {elapsed:.3f}s")
                print(f"Decisions: {self.decisions}, Conflicts: {self.conflicts}")
            else:
                print(f"UNSAT proven in {elapsed:.3f}s")
                print(f"Decisions: {self.decisions}, Conflicts: {self.conflicts}")

        return result, self.assignment

    def _dpll(self, assignment):
        """Recursive DPLL procedure"""
        # Unit propagation
        result, assignment, conflict = self._unit_propagation(assignment)
        if conflict:
            self.conflicts += 1
            return False

        # Check if all clauses are satisfied
        all_satisfied, unsatisfied_clause = self._all_clauses_satisfied(assignment)
        if not all_satisfied:
            self.conflicts += 1
            return False

        # If all variables are assigned, we have a solution
        if len(assignment) == self.cnf.n_vars:
            # Copy the assignment
            self.assignment = assignment.copy()
            return True

        # Choose a variable to branch on
        var = self._choose_variable(assignment)
        if var is None:  # No variables left, formula is UNSAT
            return False

        self.decisions += 1

        # Try assigning var = True
        assignment_true = assignment.copy()
        assignment_true[var] = True
        if self._dpll(assignment_true):
            return True

        # Try assigning var = False
        assignment_false = assignment.copy()
        assignment_false[var] = False
        if self._dpll(assignment_false):
            return True

        return False

    def _unit_propagation(self, assignment):
        """Perform unit propagation on the formula"""
        changed = True
        conflict = False
        working_assignment = assignment.copy()  # Create a copy to modify

        while changed and not conflict:
            changed = False

            for i, clause in enumerate(self.cnf.clauses):
                unassigned = []
                satisfied = False

                for lit in clause:
                    var = abs(lit)
                    sign = lit > 0

                    if var in working_assignment:
                        if working_assignment[var] == sign:  # Literal is true
                            satisfied = True
                            break
                    else:
                        unassigned.append(lit)

                if satisfied:
                    continue

                if len(unassigned) == 0:  # Empty clause - conflict
                    conflict = True
                    break

                if len(unassigned) == 1:  # Unit clause
                    lit = unassigned[0]
                    var = abs(lit)
                    sign = lit > 0

                    if var in working_assignment and working_assignment[var] != sign:
                        conflict = True
                        break

                    working_assignment[var] = sign
                    changed = True

        return not conflict, working_assignment, conflict

    def _all_clauses_satisfied(self, assignment):
        """Check if all clauses are satisfied or can be satisfied by the current assignment"""
        for i, clause in enumerate(self.cnf.clauses):
            # Check if clause is satisfied by current assignment
            satisfied = False
            has_unassigned = False

            for lit in clause:
                var = abs(lit)
                sign = lit > 0

                if var in assignment:
                    if assignment[var] == sign:  # Literal is true
                        satisfied = True
                        break
                else:
                    has_unassigned = True  # There's an unassigned variable

            # If not satisfied and no unassigned variables, clause cannot be satisfied
            if not satisfied and not has_unassigned:
                return False, i  # Return False and the index of the unsatisfied clause

        return True, -1  # All clauses are satisfied or can be satisfied

    def _choose_variable(self, assignment):
        """Choose an unassigned variable using a simple heuristic"""
        # Create list of unassigned variables
        unassigned = [var for var in range(1, self.cnf.n_vars + 1) if var not in assignment]

        if not unassigned:  # All variables are assigned
            return None

        # Count occurrences of each unassigned variable
        counts = Counter()
        for clause in self.cnf.clauses:
            # Check if clause is already satisfied
            satisfied = False
            for lit in clause:
                var = abs(lit)
                sign = lit > 0
                if var in assignment and assignment[var] == sign:
                    satisfied = True
                    break

            # If not satisfied, count unassigned variables
            if not satisfied:
                for lit in clause:
                    var = abs(lit)
                    if var in unassigned:
                        counts[var] += 1

        if not counts:  # No variables appear in unsatisfied clauses
            return unassigned[0]  # Return any unassigned variable

        # Return the variable that appears most frequently in unsatisfied clauses
        return counts.most_common(1)[0][0]


class ProbSAT:
    def __init__(self, cnf):
        self.cnf = cnf
        self.flips = 0
        self.restart_count = 0
        self.start_time = 0
        self.cb = 2.3  # ProbSAT parameter for 3-SAT

    def solve(self, max_flips=100000, max_restarts=10, verbose=False):
        """Run the ProbSAT algorithm and return (is_sat, assignment)"""
        self.start_time = time.time()
        self.flips = 0
        self.restart_count = 0

        for _ in range(max_restarts):
            self.restart_count += 1

            # Initialize with random assignment
            assignment = {var: random.choice([True, False]) for var in range(1, self.cnf.n_vars + 1)}

            # Check if random assignment satisfies formula
            if self._is_satisfied(assignment):
                elapsed = time.time() - self.start_time
                if verbose:
                    print(f"SAT: Found solution in {elapsed:.3f}s")
                    print(f"Flips: {self.flips}, Restarts: {self.restart_count}")
                return True, assignment

            # Local search phase
            current_assignment = assignment.copy()
            for _ in range(max_flips):
                # Find unsatisfied clauses
                unsat_clauses = self._get_unsatisfied_clauses(current_assignment)

                if not unsat_clauses:  # All clauses satisfied
                    # Double-check the solution
                    if not self._is_satisfied(current_assignment):
                        if verbose:
                            print("Warning: Solution verification failed")
                        continue

                    elapsed = time.time() - self.start_time
                    if verbose:
                        print(f"SAT: Found solution in {elapsed:.3f}s")
                        print(f"Flips: {self.flips}, Restarts: {self.restart_count}")
                    return True, current_assignment

                # Select a random unsatisfied clause
                clause_idx = random.choice(unsat_clauses)
                clause = self.cnf.clauses[clause_idx]

                # Use ProbSAT heuristic to choose variable to flip
                var = self._select_variable_probsat(current_assignment, clause)

                # Flip the selected variable
                current_assignment[var] = not current_assignment[var]
                self.flips += 1

        elapsed = time.time() - self.start_time
        if verbose:
            print(f"Timeout after {elapsed:.3f}s")
            print(f"Flips: {self.flips}, Restarts: {self.restart_count}")

        return False, {}

    def _is_satisfied(self, assignment):
        """Check if all clauses are satisfied by the current assignment"""
        for clause in self.cnf.clauses:
            satisfied = False
            for lit in clause:
                var = abs(lit)
                sign = lit > 0
                if assignment[var] == sign:
                    satisfied = True
                    break
            if not satisfied:
                return False
        return True

    def _get_unsatisfied_clauses(self, assignment):
        """Return indices of unsatisfied clauses"""
        unsatisfied = []
        for i, clause in enumerate(self.cnf.clauses):
            satisfied = False
            for lit in clause:
                var = abs(lit)
                sign = lit > 0
                if assignment[var] == sign:
                    satisfied = True
                    break
            if not satisfied:
                unsatisfied.append(i)
        return unsatisfied

    def _select_variable_probsat(self, assignment, clause):
        """
        ProbSAT variable selection heuristic
        Based on: "Balint & Schöning (2012). Choosing probability distributions for stochastic local search"
        """
        # Calculate score for each variable in the clause
        scores = {}

        for lit in clause:
            var = abs(lit)

            # Calculate make and break counts
            make = 0  # How many clauses would be satisfied by flipping
            break_count = 0  # How many satisfied clauses would be falsified by flipping

            # Current truth value of the literal
            lit_value = (assignment[var] == (lit > 0))

            # Check affected clauses
            for clause_idx in self.cnf.var_to_clauses[var]:
                c = self.cnf.clauses[clause_idx]

                # Current state of the clause
                is_sat = any((assignment[abs(l)] == (l > 0)) for l in c)

                # If we flip var, would this clause become satisfied?
                would_be_sat = False
                var_critical = False

                for l in c:
                    l_var = abs(l)
                    l_sign = l > 0

                    if l_var == var:
                        # This is the variable we're considering flipping
                        would_be_sat = would_be_sat or (not assignment[l_var] == l_sign)
                    else:
                        # Other variables remain the same
                        would_be_sat = would_be_sat or (assignment[l_var] == l_sign)

                # Is var the only satisfied literal in this clause?
                if is_sat:
                    var_critical = True
                    for l in c:
                        l_var = abs(l)
                        l_sign = l > 0
                        if l_var != var and assignment[l_var] == l_sign:
                            var_critical = False
                            break

                if not is_sat and would_be_sat:
                    make += 1
                if is_sat and var_critical and not would_be_sat:
                    break_count += 1

            # ProbSAT score function
            if break_count == 0:
                scores[var] = float('inf')  # Strongly prefer variables that don't break any clauses
            else:
                scores[var] = (make + 1) / pow(self.cb, break_count)

        # Choose variable based on score
        if any(score == float('inf') for score in scores.values()):
            # If any variable has infinite score, choose among those
            candidates = [var for var, score in scores.items() if score == float('inf')]
            return random.choice(candidates)
        else:
            # Weighted random choice
            total = sum(scores.values())
            r = random.uniform(0, total)
            upto = 0
            for var, score in scores.items():
                upto += score
                if upto >= r:
                    return var

        # Fallback: choose random variable from the clause
        return abs(random.choice(clause))


def run_experiment(formula_file, solver_type='both', verbose=True, output_csv=None, benchmark_csv=None):
    """Run specified solver(s) on the given formula file"""
    # Parse the CNF formula
    cnf = CNF()
    cnf.from_dimacs(formula_file)

    if verbose:
        print(f"Formula: {cnf}")

    results = {
        'file': formula_file,
        'n_vars': cnf.n_vars,
        'n_clauses': cnf.n_clauses,
        'clause_ratio': cnf.n_clauses / cnf.n_vars if cnf.n_vars > 0 else 0
    }
    from sat_solvers import DPLL, ProbSAT

    dpll_solver = DPLL(cnf)
    probsat_solver = ProbSAT(cnf)

    # Run DPLL solver
    if solver_type in ['dpll', 'both']:
        # snapshot memory just before DPLL
        proc = psutil.Process(os.getpid())
        mem_before = proc.memory_info().rss

        # run DPLL
        start_time = time.time()
        sat_dpll, assignment_dpll = dpll_solver.solve(verbose=verbose)
        dpll_time = time.time() - start_time
        results['dpll_sat'] = sat_dpll
        # snapshot memory immediately after DPLL
        mem_after = proc.memory_info().rss
        # record *incremental* memory usage in KB
        results['dpll_memory'] = (mem_after - mem_before) / 1024

        results['dpll_time'] = dpll_time
        results['dpll_decisions'] = dpll_solver.decisions
        results['dpll_conflicts'] = dpll_solver.conflicts

        if sat_dpll:
            is_verified = verify_assignment(cnf, assignment_dpll, verbose)
            results['dpll_verified'] = is_verified
            if not is_verified and verbose:
                print("WARNING: DPLL solution verification failed!")

    # Run ProbSAT solver

    if solver_type in ['probsat', 'both']:
        # snapshot memory just before ProbSAT
        proc = psutil.Process(os.getpid())
        mem_before = proc.memory_info().rss

        # run ProbSAT (returns only is_sat, assignment)
        start_time = time.time()
        sat_probsat, assignment_probsat = probsat_solver.solve(
            max_flips=100000,  # or your desired limit
            max_restarts=10,  # or your desired restarts
            verbose=verbose
        )
        probsat_time = time.time() - start_time
        results['probsat_sat'] = sat_probsat

        # grab flips / restarts from the solver instance
        results['probsat_flips'] = probsat_solver.flips
        results['probsat_restarts'] = probsat_solver.restart_count
        results['probsat_time'] = probsat_time

        # snapshot memory immediately after ProbSAT
        mem_after = proc.memory_info().rss
        results['probsat_memory'] = (mem_after - mem_before) / 1024

        # Verify solution
        if sat_probsat:
            is_verified = verify_assignment(cnf, assignment_probsat, verbose)
            results['probsat_verified'] = is_verified
            if not is_verified and verbose:
                print("WARNING: ProbSAT solution verification failed!")

    # Generate pretty table output for benchmarking
    if verbose:
        print("\n=== Benchmark Results ===")
        print(f"Formula: {formula_file}")
        print(f"Variables: {cnf.n_vars}, Clauses: {cnf.n_clauses}, Ratio: {results['clause_ratio']:.2f}")
        print("-" * 80)

        headers = ["Solver", "Result", "Verified", "Time (s)"]
        rows = []

        if 'dpll_sat' in results:
            dpll_verified = results.get('dpll_verified', 'N/A')
            dpll_row = ["DPLL",
                        "SAT" if results['dpll_sat'] else "UNSAT",
                        "Yes" if dpll_verified else "No" if results['dpll_sat'] else "N/A",
                        f"{results['dpll_time']:.6f}"]
            if 'dpll_decisions' in results:
                headers.append("Decisions")
                dpll_row.append(str(results['dpll_decisions']))
            if 'dpll_conflicts' in results:
                headers.append("Conflicts")
                dpll_row.append(str(results['dpll_conflicts']))
            rows.append(dpll_row)

        if 'probsat_sat' in results:
            probsat_verified = results.get('probsat_verified', 'N/A')
            probsat_row = ["ProbSAT",
                           "SAT" if results['probsat_sat'] else "Unknown",
                           "Yes" if probsat_verified else "No" if results['probsat_sat'] else "N/A",
                           f"{results['probsat_time']:.6f}"]
            if 'probsat_flips' in results:
                headers.append("Flips")
                probsat_row.append(str(results['probsat_flips']))
            if 'probsat_restarts' in results:
                headers.append("Restarts")
                probsat_row.append(str(results['probsat_restarts']))
            rows.append(probsat_row)

        # Print table
        print(" | ".join(headers))
        print("-" * 80)
        for row in rows:
            while len(row) < len(headers):
                row.append("N/A")
            print(" | ".join(row))

    # Save results to CSV if requested
    csv_output = output_csv or benchmark_csv
    if csv_output:
        import csv

        # Create directory if it doesn't exist
        os.makedirs(os.path.dirname(os.path.abspath(csv_output)), exist_ok=True)

        # Check if file exists to decide whether to write header
        file_exists = os.path.isfile(csv_output)

        with open(csv_output, 'a', newline='') as f:
            writer = csv.writer(f)

            # Write header if file doesn't exist
            if not file_exists:
                headers = ['file', 'n_vars', 'n_clauses', 'clause_ratio',
                           'dpll_sat', 'dpll_verified', 'dpll_time', 'dpll_decisions', 'dpll_conflicts', 'dpll_memory',
                           'probsat_sat', 'probsat_verified', 'probsat_time', 'probsat_flips', 'probsat_restarts',
                           'probsat_memory']
                writer.writerow(headers)

            # Write results row
            row = [
                results.get('file', ''),
                results.get('n_vars', ''),
                results.get('n_clauses', ''),
                results.get('clause_ratio', ''),
                results.get('dpll_sat', ''),
                results.get('dpll_verified', ''),
                results.get('dpll_time', ''),
                results.get('dpll_decisions', ''),
                results.get('dpll_conflicts', ''),
                results.get('dpll_memory', ''),
                results.get('probsat_sat', ''),
                results.get('probsat_verified', ''),
                results.get('probsat_time', ''),
                results.get('probsat_flips', ''),
                results.get('probsat_restarts', ''),
                results.get('probsat_memory', '')
            ]

            writer.writerow(row)

    return results


def verify_assignment(cnf, assignment, verbose=True):
    """Verify that an assignment satisfies all clauses"""
    # Ensure we have assignments for all variables
    for var in range(1, cnf.n_vars + 1):
        if var not in assignment:
            if verbose:
                print(f"Warning: Missing assignment for variable {var}")
            return False

    # Check all clauses
    for i, clause in enumerate(cnf.clauses):
        satisfied = False
        for lit in clause:
            var = abs(lit)
            sign = lit > 0
            if var in assignment and assignment[var] == sign:
                satisfied = True
                break

        if not satisfied:
            if verbose:
                print(f"Warning: Clause {i + 1} is not satisfied by the assignment")
                print(f"Clause: {clause}")
                print(f"Relevant assignments: {[(var, assignment.get(var)) for var in map(abs, clause)]}")
            return False

    if verbose:
        print("Verified: Assignment satisfies all clauses")
    return True


def generate_random_3cnf(n_vars, clause_ratio=4.2, output_file=None):
    """Generate a random 3-CNF formula"""
    n_clauses = int(n_vars * clause_ratio)
    clauses = []

    for _ in range(n_clauses):
        # Generate a random clause with 3 distinct literals
        vars_in_clause = random.sample(range(1, n_vars + 1), 3)
        clause = [v * random.choice([-1, 1]) for v in vars_in_clause]
        clauses.append(clause)

    if output_file:
        if not output_file.endswith('.cnf'):
            raise ValueError(f"Output file must be .cnf, got: {output_file}")
        if os.path.exists(output_file):
            raise FileExistsError(f"Refusing to overwrite existing CNF: {output_file}")
        with open(output_file, 'w') as f:
            f.write(f"p cnf {n_vars} {n_clauses}\n")
            for clause in clauses:
                f.write(' '.join(map(str, clause)) + " 0\n")

    return clauses


def main():
    parser = argparse.ArgumentParser(description='Run SAT Solvers')
    parser.add_argument('formula', help='DIMACS CNF file to solve')
    parser.add_argument('--solver', choices=['dpll', 'probsat', 'both'], default='both',
                        help='Solver to use (default: both)')
    parser.add_argument('--verbose', action='store_true', help='Enable verbose output')
    parser.add_argument('--generate', type=int, help='Generate random 3-CNF with N variables')
    parser.add_argument('--ratio', type=float, default=4.2, help='Clause to variable ratio for generation')
    parser.add_argument('--output', help='Output file for generated formula')
    parser.add_argument('--benchmark', help='Save benchmark results to CSV file')
    parser.add_argument('--batch', action='store_true', help='Generate a batch of instances for benchmarking')
    parser.add_argument('--instances', type=int, default=5, help='Number of instances to generate for each size')
    parser.add_argument('--sizes', type=str, default='10,20,30,40,50', help='Comma-separated list of variable counts')
    parser.add_argument('--sat_only', action='store_true', help='Output only SAT/UNSAT result')

    args = parser.parse_args()

    # Handle batch generation
    if args.batch:
        sizes = [int(n) for n in args.sizes.split(',')]
        instances_per_size = args.instances
        ratio = args.ratio

        print(f"Generating batches of {instances_per_size} instances for each size: {sizes}")
        print(f"Using clause ratio: {ratio}")

        for n in sizes:
            for i in range(instances_per_size):
                output_file = f"random_{n}_{ratio}_{i + 1}.cnf"
                print(f"Generating random 3-CNF with {n} variables, instance {i + 1}")
                generate_random_3cnf(n, ratio, output_file)
                print(f"Saved to {output_file}")

        print("Batch generation complete")
        return

    # Handle single instance generation
    # Handle single-instance generation (and then exit)
    if args.generate:
        if not args.output:
            args.output = f"random_{args.generate}_{args.ratio}.cnf"
        print(f"Generating random 3-CNF with {args.generate} variables and ratio {args.ratio}")
        generate_random_3cnf(args.generate, args.ratio, args.output)
        print(f"Saved to {args.output}")
        sys.exit(0)


    # Handle SAT-only mode
    if args.sat_only:
        cnf = CNF()
        cnf.from_dimacs(args.formula)

        if args.solver in ['dpll', 'both']:
            dpll_solver = DPLL(cnf)
            sat, assignment = dpll_solver.solve(verbose=False)

            # Verify if SAT
            if sat:
                is_valid = verify_assignment(cnf, assignment, verbose=False)
                if not is_valid:
                    print("UNSAT (Assignment verification failed)")
                else:
                    print("SAT")
            else:
                print("UNSAT")

        elif args.solver == 'probsat':
            probsat_solver = ProbSAT(cnf)
            sat, assignment = probsat_solver.solve(verbose=False)

            # Verify if SAT
            if sat:
                is_valid = verify_assignment(cnf, assignment, verbose=False)
                if not is_valid:
                    print("Unknown (Assignment verification failed)")
                else:
                    print("SAT")
            else:
                print("Unknown")  # ProbSAT can't prove UNSAT
        return

    # Handle benchmark mode
    if args.benchmark:
        import glob

        # Determine files to benchmark
        if os.path.isdir(args.formula):
            benchmark_files = glob.glob(os.path.join(args.formula, "*.cnf"))
        else:
            benchmark_files = [args.formula]

        print(f"Running benchmark on {len(benchmark_files)} files")
        print(f"Results will be saved to {args.benchmark}")

        # Ensure the directory exists
        os.makedirs(os.path.dirname(os.path.abspath(args.benchmark)), exist_ok=True)

        # Run benchmark on each file
        for i, file in enumerate(sorted(benchmark_files)):
            print(f"\nProcessing file {i + 1}/{len(benchmark_files)}: {file}")
            run_experiment(file, args.solver, args.verbose, benchmark_csv=args.benchmark)

        print(f"\nBenchmark complete. Results saved to {args.benchmark}")
        return

    # Normal single-file mode
    results = run_experiment(args.formula, args.solver, args.verbose, output_csv=args.output)

    # Generate LaTeX table for paper
    if 'dpll_sat' in results and 'probsat_sat' in results:
        formula_name = os.path.basename(args.formula).replace('.cnf', '')
        latex_row = (
            f"{formula_name} & {results['n_vars']} & {results['n_clauses']} & "
            f"{results['dpll_sat']} & {results['dpll_decisions']} & {results['dpll_conflicts']} & "
            f"{results['dpll_time']:.4f} & {results['probsat_sat']} & {results['probsat_flips']} & "
            f"{results['probsat_time']:.4f} \\\\"
        )
        print("\n=== LaTeX Row for Paper ===")
        print(latex_row)


if __name__ == "__main__":
    main()