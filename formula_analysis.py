from sympy import symbols, to_cnf
from pysat.solvers import Solver
from pysat.formula import CNF
import time
import os
import csv

def analyze_solve_formula(path):
    formula = CNF(from_file=path)
    num_vars = formula.nv
    num_clauses = len(formula.clauses)
    print("--- Formula Statistics ---")
    print(f"File Loaded : {path}")
    print(f"Variables   : {num_vars}")
    print(f"Clauses     : {num_clauses}")
    print("--------------------------\n")
    with Solver(name='Cadical195', bootstrap_with=formula, use_timer=True) as solver:
        print("Solving...")
        # Optional: Track total wall-clock time in Python as an alternative reference
        python_start = time.perf_counter() 
        
        result = solver.solve()
        
        python_end = time.perf_counter()
        
        # 4. Extract Timing Data
        # solver.time() retrieves the time spent *specifically* during the last solve call
        internal_solve_time = solver.time()
        python_total_time = python_end - python_start

        print("\n--- Results & Performance ---")
        print(f"Result              : {'SATISFIABLE' if result else 'UNSATISFIABLE'}")
        print(f"Solver Internal Time: {internal_solve_time:.4f} seconds")
        print(f"Python Wrapper Time : {python_total_time:.4f} seconds")
        print("-----------------------------")
        return path, internal_solve_time, num_vars, num_clauses

results = ["file", "solve_time", "num_vars", "num_clauses"]
for f in os.scandir("bv_decide_queries"):
    results.append(analyze_solve_formula(f.path))
with open('formulas.csv', 'w', newline='') as f:
    writer = csv.writer(f)
    writer.writerows(results)