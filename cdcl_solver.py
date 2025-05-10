import os
import time
import psutil
import pycosat
import pandas as pd
from collections import defaultdict, deque

class CDCLSolver:
    """
    Basic Conflict-Driven Clause Learning (CDCL) solver with watched literals.
    Suitable for small to medium SAT instances.
    """
    def __init__(self, num_vars, clauses):
        self.num_vars = num_vars
        self.clauses = clauses
        self.assign = [0] * (num_vars + 1)  # 0=unassigned, 1=true, -1=false
        self.level = [0] * (num_vars + 1)
        self.reason = [None] * (num_vars + 1)
        self.decision_level = 0
        self.trail = []
        self.watchers = defaultdict(list)
        for ci, cl in enumerate(clauses):
            if cl:
                self.watchers[cl[0]].append(ci)
                if len(cl) > 1:
                    self.watchers[cl[1]].append(ci)

    def neg(self, lit):
        return -lit

    def value(self, lit):
        v = self.assign[abs(lit)]
        return v if lit > 0 else -v

    def enqueue(self, lit, level, reason):
        var = abs(lit)
        self.assign[var] = 1 if lit > 0 else -1
        self.level[var] = level
        self.reason[var] = reason
        self.trail.append(lit)

    def propagate(self):
        queue = deque(self.trail)
        while queue:
            lit = queue.popleft()
            for ci in list(self.watchers[self.neg(lit)]):
                clause = self.clauses[ci]
                found = False
                for l in clause:
                    if l != self.neg(lit) and self.value(l) != -1:
                        self.watchers[l].append(ci)
                        self.watchers[self.neg(lit)].remove(ci)
                        found = True
                        break
                if not found:
                    unassigned = [l for l in clause if self.value(l) == 0]
                    if not unassigned:
                        return ci
                    ulit = unassigned[0]
                    self.enqueue(ulit, self.decision_level, ci)
                    queue.append(ulit)
        return None

    def backtrack(self, level):
        while self.trail and self.level[abs(self.trail[-1])] > level:
            lit = self.trail.pop()
            var = abs(lit)
            self.assign[var] = 0
            self.level[var] = 0
            self.reason[var] = None
        self.decision_level = level

    def solve(self):
        # initial propagation
        self.decision_level = 0
        conflict = self.propagate()
        if conflict is not None:
            return False
        while True:
            unassigned = next((i for i in range(1, self.num_vars+1) if self.assign[i] == 0), None)
            if unassigned is None:
                return True
            self.decision_level += 1
            self.enqueue(unassigned, self.decision_level, None)
            conflict = self.propagate()
            if conflict is not None:
                self.backtrack(0)
                if self.decision_level == 0:
                    return False

# DIMACS parser
def parse_dimacs(path):
    clauses = []
    num_vars = 0
    with open(path) as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith('c'):
                continue
            if s.startswith('p cnf'):
                parts = s.split()
                num_vars = int(parts[2])
                continue
            lits = list(map(int, s.split()))
            clause = [l for l in lits if l != 0]
            if clause:
                clauses.append(clause)
    return num_vars, clauses

# Main runner
def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--instances_dir', default='instances', help='Root directory of DIMACS CNF files')
    args = parser.parse_args()

    # Gather all .cnf under instances_dir recursively
    cnf_paths = []
    for root, _, files in os.walk(args.instances_dir):
        for fname in files:
            if fname.lower().endswith('.cnf'):
                cnf_paths.append(os.path.join(root, fname))
    if not cnf_paths:
        print(f"No .cnf files found under '{args.instances_dir}'")
        return

    # Prepare results
    rows = []
    for path in sorted(cnf_paths):
        rel = os.path.relpath(path, args.instances_dir)
        file_id = os.path.join(args.instances_dir, rel)
        num_vars, clauses = parse_dimacs(path)
        # CDCL solve
        proc = psutil.Process(os.getpid())
        mem_before = proc.memory_info().rss
        start = time.time()
        sat = CDCLSolver(num_vars, clauses).solve()
        elapsed = time.time() - start
        mem_after = proc.memory_info().rss
        mem_kb = (mem_after - mem_before) / 1024
        rows.append({'file': file_id, 'cdcl_sat': sat, 'cdcl_time': elapsed, 'cdcl_memory': mem_kb})
        print(f"{file_id}: {'SAT' if sat else 'UNSAT'} in {elapsed:.4f}s, Δmem={mem_kb:.1f}KB")

    # Save to CSV
    df = pd.DataFrame(rows)
    os.makedirs('cdcl_comparison', exist_ok=True)
    out_csv = os.path.join('cdcl_comparison', 'cdcl_results.csv')
    df.to_csv(out_csv, index=False)
    print(f"Results saved to {out_csv}")

if __name__ == '__main__':
    main()