#!/usr/bin/env python3
import os
import time
import pandas as pd
from sat_solvers import CNF, DPLL
from cdcl_solver import CDCLSolver


def generate_pigeonhole(h):
    """
    Generate the UNSAT pigeonhole principle CNF for h holes and p=h+1 pigeons.
    Returns (num_vars, clauses).
    """
    p = h + 1
    num_vars = p * h
    clauses = []
    # each pigeon must go to at least one hole
    for i in range(1, p + 1):
        clauses.append([(i - 1) * h + j for j in range(1, h + 1)])
    # no hole may contain two pigeons
    for j in range(1, h + 1):
        for i1 in range(1, p + 1):
            for i2 in range(i1 + 1, p + 1):
                lit1 = -((i1 - 1) * h + j)
                lit2 = -((i2 - 1) * h + j)
                clauses.append([lit1, lit2])
    return num_vars, clauses


def run_dpll(num_vars, clauses):
    cnf = CNF()
    for clause in clauses:
        cnf.add_clause(clause)
    solver = DPLL(cnf)
    solver.decisions = 0
    solver.conflicts = 0
    start = time.time()
    sat, _ = solver.solve()
    elapsed = time.time() - start
    return sat, solver.decisions, solver.conflicts, elapsed


def run_cdcl(num_vars, clauses):
    solver = CDCLSolver(num_vars, clauses)
    solver.decisions = 0
    solver.conflicts = 0
    orig_enqueue = solver.enqueue
    def enqueue_count(lit, level, reason):
        if reason is None:
            solver.decisions += 1
        return orig_enqueue(lit, level, reason)
    solver.enqueue = enqueue_count
    orig_propagate = solver.propagate
    def propagate_count():
        conflict = orig_propagate()
        if conflict is not None:
            solver.conflicts += 1
        return conflict
    solver.propagate = propagate_count
    start = time.time()
    sat = solver.solve()
    elapsed = time.time() - start
    return sat, solver.decisions, solver.conflicts, elapsed


def main():
    results = []
    for h in range(2, 8):
        ratio = f"{h+1}/{h}"
        num_vars, clauses = generate_pigeonhole(h)
        n_clauses = len(clauses)

        _, d_dec, d_conf, _ = run_dpll(num_vars, clauses)
        _, c_dec, c_conf, _ = run_cdcl(num_vars, clauses)

        results.append({
            'ratio': ratio,
            'n_vars': num_vars,
            'n_clauses': n_clauses,
            'dpll_decisions': d_dec,
            'dpll_conflicts': d_conf,
            'cdcl_decisions': c_dec,
            'cdcl_conflicts': c_conf
        })

    df = pd.DataFrame(results)
    print(df.to_string(index=False))

    out_dir = 'pigeonhole_bench'
    os.makedirs(out_dir, exist_ok=True)
    tex_path = os.path.join(out_dir, 'pigeonhole_results.tex')
    with open(tex_path, 'w') as f:
        f.write("\\begin{table}[h!]\n")
        f.write("\\centering\n")
        f.write("\\begin{tabular}{c|cccccc}\n")
        f.write("\\hline\n")
        # Header with correct LaTeX linebreak
        f.write("Pigeons/Holes & Vars & Clauses & \\textbf{DPLL} decisions & DPLL conflicts & \\textbf{CDCL} decisions & CDCL conflicts \\\\\n")
        f.write("\\hline\n")
        # Rows with proper line endings
        for r in results:
            f.write(f"{r['ratio']} & {r['n_vars']} & {r['n_clauses']} & {r['dpll_decisions']} & {r['dpll_conflicts']} & {r['cdcl_decisions']} & {r['cdcl_conflicts']} \\\\\n")
        f.write("\\hline\n")
        f.write("\\end{tabular}\n")
        f.write("\\caption{Performance of DPLL vs. CDCL on unsatisfiable pigeonhole principle formulas $PHP_{p}^{h}$ ($p=h+1$).}\n")
        f.write("\\label{tab:pigeonhole}\n")
        f.write("\\end{table}\n")

    print(f"LaTeX table written to {tex_path}")

if __name__ == '__main__':
    main()
