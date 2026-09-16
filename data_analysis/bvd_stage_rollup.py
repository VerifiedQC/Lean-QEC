"""Roll the per-stage `bv_decidet` log up into the five coarse bv_decide phases.

Usage:  python data_analysis/bvd_stage_rollup.py [bvd_times_v2.csv]

The CSV is written by the `bv_decidet` tactic in LeanQEC/timedbv.lean, one row per
invocation. Stage times are in ms.
"""

import csv
import sys

# The five phases the project reasons about, and the fine-grained stages that make them up.
PHASES = {
    "normalization": ["normalize"],
    "aig": ["reflect", "bitblast"],
    "cnf": ["cnf", "dimacs"],
    "solving": ["solve"],
    "checking": ["lrat_read", "expr_def", "cert_def", "verify", "assign"],
}

STATS = ["aig_nodes", "cnf_clauses", "lrat_file_bytes", "lrat_steps", "cert_bytes"]


def load(path):
    with open(path, newline="") as f:
        rows = [r for r in csv.DictReader(f) if r.get("label")]
    # Rows written by an older build of the tactic have no label and are skipped above.
    return rows


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "bvd_times_v2.csv"
    rows = load(path)
    if not rows:
        sys.exit(f"no labelled rows in {path}")

    width = max(len(r["label"]) for r in rows)
    head = f"{'label':<{width}}  {'status':<10}" + "".join(f"{p:>15}" for p in PHASES)
    head += f"{'total':>12}" + "".join(f"{s:>12}" for s in STATS)
    print(head)
    print("-" * len(head))

    for r in rows:
        line = f"{r['label']:<{width}}  {r['status']:<10}"
        total = float(r["total"]) if r["total"] else 0.0
        for stages in PHASES.values():
            ms = sum(float(r[s]) for s in stages if r.get(s))
            pct = (100.0 * ms / total) if total else 0.0
            line += f"{ms:>9.1f}({pct:>3.0f}%)"
        line += f"{total:>12.1f}"
        line += "".join(f"{r.get(s) or '':>12}" for s in STATS)
        print(line)


if __name__ == "__main__":
    main()
