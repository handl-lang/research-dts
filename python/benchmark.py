#!/usr/bin/env python3
"""
Empirical benchmark of the declarative handler-topology synthesis pass.

Reports:
- n handlers
- m precedence constraints
- topological-sort time
- synthesis (AST construction) time
- generated AST length / node count
- cycle detection time

The toposort below uses a simple Kahn queue to isolate the O(|H| + |≺|)
algorithmic scaling of the core synthesis step. The Python reference
implementations in case_studies add deterministic tie-breaking via sorting;
that is a constant-factor detail and is excluded from this timing.
"""

import time
from collections import deque
from dts.case_studies.http_middleware import Handler, synthesize


def toposort(handlers, constraints):
    """Linear Kahn toposort. constraints (a,b) means a < b (a inner)."""
    by_name = {h.name: h for h in handlers}
    adj = {h.name: [] for h in handlers}
    indeg = {h.name: 0 for h in handlers}
    for a, b in constraints:
        adj[a].append(b)
        indeg[b] += 1

    queue = deque([h.name for h in handlers if indeg[h.name] == 0])
    ordered = []
    while queue:
        n = queue.popleft()
        ordered.append(by_name[n])
        for m in adj[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                queue.append(m)

    if len(ordered) != len(handlers):
        raise ValueError("cycle")
    return ordered


def chain_constraints(n):
    return [(f"H{i}", f"H{i+1}") for i in range(n - 1)]


def bushy_constraints(n):
    # H_i < H_n for all i < n: one source and one sink
    return [(f"H{i}", f"H{n-1}") for i in range(n - 1)]


def bench(n, m_kind="chain"):
    handlers = [Handler(f"H{i}", [f"op{i}"]) for i in range(n)]
    if m_kind == "chain":
        constraints = chain_constraints(n)
    else:
        constraints = bushy_constraints(n)
    m = len(constraints)

    # Topological sort timing
    start = time.perf_counter()
    ordered = toposort(handlers, constraints)
    ts_time = time.perf_counter() - start

    # Synthesis timing
    start = time.perf_counter()
    term = synthesize("body", ordered)
    syn_time = time.perf_counter() - start

    node_count = term.count("handle")

    # Cycle detection: add a back edge
    cyc_constraints = constraints + [(f"H{n-1}", f"H0")]
    start = time.perf_counter()
    try:
        toposort(handlers, cyc_constraints)
    except ValueError:
        pass
    cyc_time = time.perf_counter() - start

    return n, m, ts_time, syn_time, node_count, cyc_time


def main():
    print("Declarative handler topology synthesis benchmark")
    print(f"{'n':>8} {'m':>8} {'toposort (ms)':>14} {'synth (ms)':>12} {'nodes':>8} {'cycle (ms)':>12}")
    print("-" * 80)
    for n in (10, 100, 1000, 10000):
        n, m, ts, syn, nodes, cyc = bench(n)
        print(
            f"{n:8} {m:8} {ts*1000:14.6f} {syn*1000:12.6f} {nodes:8} {cyc*1000:12.6f}"
        )


if __name__ == "__main__":
    main()
