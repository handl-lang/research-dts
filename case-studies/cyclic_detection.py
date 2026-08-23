#!/usr/bin/env python3
"""
Case Study 3: Cyclic precedence detection.

Demonstrates that the synthesis pipeline rejects cyclic precedence
constraints with clear, user-friendly diagnostics. Shows three scenarios:

  1. Simple cycle: A < B < A
  2. Longer cycle: A < B < C < A
  3. Valid (acyclic) spec for contrast

The cycle detection happens during topological sort: if the sorted output
is shorter than the input, a cycle exists. We then identify the cycle
members and print a readable error.
"""

from dataclasses import dataclass, field
from collections import deque
from typing import Dict, List, Tuple, Set


@dataclass
class Handler:
    name: str
    clauses: List[str] = field(default_factory=list)


def toposort_or_cycle(
    handlers: List[Handler],
    constraints: List[Tuple[str, str]]
) -> Tuple[List[Handler], List[str]]:
    """
    Topological sort with cycle detection.
    Returns (ordered, cycle_members).
    If cycle_members is non-empty, ordered is partial (incomplete).
    """
    by_name: Dict[str, Handler] = {h.name: h for h in handlers}
    adj: Dict[str, List[str]] = {h.name: [] for h in handlers}
    indeg: Dict[str, int] = {h.name: 0 for h in handlers}

    for a, b in constraints:
        adj[a].append(b)
        indeg[b] += 1

    queue = deque(sorted(h.name for h in handlers if indeg[h.name] == 0))
    ordered: List[Handler] = []

    while queue:
        n = queue.popleft()
        ordered.append(by_name[n])
        for m in sorted(adj[n]):
            indeg[m] -= 1
            if indeg[m] == 0:
                queue.append(m)
        queue = deque(sorted(queue))

    if len(ordered) == len(handlers):
        return ordered, []

    # Cycle detected — find nodes still with indeg > 0
    cycle_nodes = [h.name for h in handlers if indeg[h.name] > 0]
    return ordered, cycle_nodes


def find_cycle_path(
    handlers: List[Handler],
    constraints: List[Tuple[str, str]],
    cycle_nodes: List[str]
) -> List[str]:
    """
    Attempt to find an actual cycle path among the cycle nodes using DFS.
    Returns a list of handler names forming a cycle, or the raw node list
    if no simple cycle path is found.
    """
    adj: Dict[str, List[str]] = {h.name: [] for h in handlers}
    for a, b in constraints:
        if a in cycle_nodes and b in cycle_nodes:
            adj[a].append(b)

    cycle_set: Set[str] = set(cycle_nodes)

    def dfs(start: str, current: str, path: List[str], visited: Set[str]) -> List[str]:
        for neighbor in adj[current]:
            if neighbor == start and len(path) >= 2:
                return path + [start]
            if neighbor not in visited and neighbor in cycle_set:
                result = dfs(start, neighbor, path + [neighbor], visited | {neighbor})
                if result:
                    return result
        return []

    for start in sorted(cycle_nodes):
        path = dfs(start, start, [start], {start})
        if path:
            return path

    return cycle_nodes


def report_cycle(
    handlers: List[Handler],
    constraints: List[Tuple[str, str]],
    cycle_nodes: List[str]
) -> None:
    """Print a user-friendly cycle diagnostic."""
    cycle_path = find_cycle_path(handlers, constraints, cycle_nodes)

    print("  ERROR: Precedence relation contains a cycle!")
    print()
    print("  Cycle detected among handlers:")
    if len(cycle_path) > 1 and cycle_path[0] == cycle_path[-1]:
        chain = " -> ".join(cycle_path)
        print(f"    {chain}")
    else:
        print(f"    Nodes with remaining dependencies: {cycle_path}")
    print()
    print("  Involved constraints:")
    constraint_set = set(constraints)
    cycle_set = set(cycle_nodes)
    for a, b in constraints:
        if a in cycle_set and b in cycle_set:
            print(f"    {a} < {b}")
    print()
    print("  Fix: Remove or reverse one constraint in the cycle to break it.")


def synthesize(body: str, ordered: List[Handler]) -> str:
    if not ordered:
        return body
    prefix = "handle (" * (len(ordered) - 1)
    inner = f"handle {body} with {ordered[0].name}"
    suffix = "".join(f") with {h.name}" for h in ordered[1:])
    return prefix + inner + suffix


def run_scenario(name: str,
                 handlers: List[Handler],
                 constraints: List[Tuple[str, str]]) -> None:
    print(f"\n{'=' * 60}")
    print(f"Scenario: {name}")
    print(f"{'=' * 60}")

    print(f"\n  Handlers: {[h.name for h in handlers]}")
    print(f"  Constraints: {constraints}")

    ordered, cycle_nodes = toposort_or_cycle(handlers, constraints)

    if cycle_nodes:
        print()
        report_cycle(handlers, constraints, cycle_nodes)
    else:
        print(f"\n  Linear extension: {' < '.join(h.name for h in ordered)}")
        term = synthesize("body", ordered)
        print(f"  Synthesized: {term}")
        print("  Status: OK (acyclic)")


def main() -> None:
    # Scenario 1: Simple cycle A < B < A
    h1 = [Handler("A", ["op1"]), Handler("B", ["op2"])]
    c1 = [("A", "B"), ("B", "A")]

    # Scenario 2: Longer cycle A < B < C < A
    h2 = [
        Handler("A", ["op1"]),
        Handler("B", ["op2"]),
        Handler("C", ["op3"]),
    ]
    c2 = [("A", "B"), ("B", "C"), ("C", "A")]

    # Scenario 3: Valid acyclic spec (contrast)
    h3 = [
        Handler("Validator", ["validate"]),
        Handler("Auth", ["authenticate"]),
        Handler("Logger", ["log"]),
    ]
    c3 = [("Validator", "Auth"), ("Auth", "Logger")]

    run_scenario("Simple cycle (A < B < A)", h1, c1)
    run_scenario("Longer cycle (A < B < C < A)", h2, c2)
    run_scenario("Valid acyclic spec (Validator < Auth < Logger)", h3, c3)

    print(f"\n{'=' * 60}")
    print("Summary: Cyclic specs are rejected with diagnostics.")
    print("         Acyclic specs synthesize correctly.")
    print(f"{'=' * 60}")


if __name__ == "__main__":
    main()
