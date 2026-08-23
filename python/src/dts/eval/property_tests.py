#!/usr/bin/env python3
"""
Evaluation infrastructure: property-based test harness for DTS synthesis.

Three test suites:

  1. Random acyclic graphs → verify synthesis respects all precedence constraints
  2. Random cyclic graphs → verify rejection with cycle detection
  3. Property-based: for any acyclic spec, synthesized nesting respects all constraints

The harness generates random precedence graphs, runs synthesis, and checks
invariants. Uses a simple random seed for reproducibility.

Run:
    python3 eval/property_tests.py
    python3 eval/property_tests.py --trials 500 --max-handlers 20
"""

import argparse
import random
import sys
from dataclasses import dataclass, field
from collections import deque
from typing import Dict, List, Tuple, Optional


# ---------------------------------------------------------------------------
# Core types (mirrors Dts/Basic.lean + case studies)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Handler:
    name: str
    clauses: Tuple[str, ...] = ("op",)

    def __repr__(self) -> str:
        return f"Handler({self.name})"


@dataclass
class Spec:
    handlers: List[Handler]
    constraints: List[Tuple[str, str]]  # (a, b) means a < b (a is inner)


# ---------------------------------------------------------------------------
# Topological sort with cycle detection
# ---------------------------------------------------------------------------

def toposort(spec: Spec) -> Tuple[List[Handler], List[str]]:
    """
    Returns (ordered, cycle_nodes).
    If cycle_nodes is non-empty, ordered is incomplete.
    """
    by_name = {h.name: h for h in spec.handlers}
    adj: Dict[str, List[str]] = {h.name: [] for h in spec.handlers}
    indeg: Dict[str, int] = {h.name: 0 for h in spec.handlers}

    for a, b in spec.constraints:
        adj[a].append(b)
        indeg[b] += 1

    queue = deque(sorted(h.name for h in spec.handlers if indeg[h.name] == 0))
    ordered: List[Handler] = []

    while queue:
        n = queue.popleft()
        ordered.append(by_name[n])
        for m in sorted(adj[n]):
            indeg[m] -= 1
            if indeg[m] == 0:
                queue.append(m)
        queue = deque(sorted(queue))

    if len(ordered) == len(spec.handlers):
        return ordered, []
    cycle_nodes = [h.name for h in spec.handlers if indeg[h.name] > 0]
    return ordered, cycle_nodes


# ---------------------------------------------------------------------------
# Synthesis
# ---------------------------------------------------------------------------

def synthesize(body: str, ordered: List[Handler]) -> str:
    if not ordered:
        return body
    prefix = "handle (" * (len(ordered) - 1)
    inner = f"handle {body} with {ordered[0].name}"
    suffix = "".join(f") with {h.name}" for h in ordered[1:])
    return prefix + inner + suffix


# ---------------------------------------------------------------------------
# Nesting verification
# ---------------------------------------------------------------------------

def appears_before(a: str, b: str, ordered: List[Handler]) -> bool:
    """Check that a appears before b in the ordered list."""
    idx = {h.name: i for i, h in enumerate(ordered)}
    return idx[a] < idx[b]


def verify_nesting(spec: Spec, ordered: List[Handler]) -> List[str]:
    """
    Verify that for every constraint (a, b), a appears before b in the ordered
    list (which means a is nested inside b in the synthesized term).

    Returns a list of violation messages (empty if all constraints satisfied).
    """
    violations = []
    for a, b in spec.constraints:
        if not appears_before(a, b, ordered):
            violations.append(
                f"Constraint {a} < {b} violated: {a} does not appear before {b}"
            )
    return violations


def verify_containment(spec: Spec, ordered: List[Handler]) -> List[str]:
    """
    Verify that every handler in spec.handlers appears in the ordered list
    exactly once.
    """
    violations = []
    ordered_names = [h.name for h in ordered]
    spec_names = [h.name for h in spec.handlers]

    if len(ordered_names) != len(set(ordered_names)):
        violations.append("Duplicate handlers in ordered list")

    for h in spec_names:
        if h not in ordered_names:
            violations.append(f"Handler {h} missing from ordered list")

    if len(ordered_names) != len(spec_names):
        violations.append(
            f"Length mismatch: ordered has {len(ordered_names)}, "
            f"spec has {len(spec_names)}"
        )

    return violations


# ---------------------------------------------------------------------------
# Random graph generation
# ---------------------------------------------------------------------------

def random_acyclic_spec(
    n_handlers: int,
    n_constraints: int,
    rng: random.Random
) -> Spec:
    """
    Generate a random acyclic precedence graph.

    Strategy: assign handlers indices 0..n-1. Only add constraints from
    lower-indexed to higher-indexed handlers. This guarantees acyclicity
    because the constraint graph respects the total order 0 < 1 < ... < n-1.
    """
    handlers = [Handler(name=f"H{i}") for i in range(n_handlers)]
    possible_edges = [
        (f"H{i}", f"H{j}")
        for i in range(n_handlers)
        for j in range(i + 1, n_handlers)
    ]
    n_constraints = min(n_constraints, len(possible_edges))
    constraints = rng.sample(possible_edges, n_constraints)
    return Spec(handlers=handlers, constraints=constraints)


def random_cyclic_spec(
    n_handlers: int,
    n_constraints: int,
    rng: random.Random
) -> Spec:
    """
    Generate a random spec that is guaranteed to contain at least one cycle.

    Strategy: generate an acyclic spec with at least one constraint,
    pick an existing constraint (a, b), and add the reverse (b, a).
    This creates a guaranteed 2-cycle.
    """
    # Ensure at least 1 acyclic constraint to create a cycle with
    acyclic_constraints = max(1, n_constraints - 1)
    max_edges = n_handlers * (n_handlers - 1) // 2
    acyclic_constraints = min(acyclic_constraints, max_edges)
    spec = random_acyclic_spec(n_handlers, acyclic_constraints, rng)

    # Pick a random existing constraint and reverse it to create a 2-cycle
    if spec.constraints:
        edge = rng.choice(spec.constraints)
        back_edge = (edge[1], edge[0])
        spec.constraints.append(back_edge)

    return spec


# ---------------------------------------------------------------------------
# Test suites
# ---------------------------------------------------------------------------

class TestResult:
    def __init__(self, name: str):
        self.name = name
        self.passed = 0
        self.failed = 0
        self.failures: List[str] = []

    def ok(self):
        self.passed += 1

    def fail(self, msg: str):
        self.failed += 1
        self.failures.append(msg)

    @property
    def total(self) -> int:
        return self.passed + self.failed

    def summary(self) -> str:
        status = "PASS" if self.failed == 0 else "FAIL"
        return f"[{status}] {self.name}: {self.passed}/{self.total} passed"


def test_acyclic_synthesis(trials: int, max_handlers: int, rng: random.Random) -> TestResult:
    """
    Suite 1: Random acyclic graphs → verify synthesis respects constraints.

    For each trial:
      - Generate a random acyclic spec
      - Run topological sort
      - Verify no cycle detected
      - Verify all handlers present in output
      - Verify every constraint (a, b) has a before b in the ordered list
    """
    result = TestResult("Acyclic synthesis correctness")

    for t in range(trials):
        n = rng.randint(2, max_handlers)
        max_edges = n * (n - 1) // 2
        m = rng.randint(0, max_edges)
        spec = random_acyclic_spec(n, m, rng)

        ordered, cycle_nodes = toposort(spec)

        if cycle_nodes:
            result.fail(
                f"Trial {t}: acyclic spec flagged as cyclic "
                f"(n={n}, m={m}, cycle={cycle_nodes})"
            )
            continue

        violations = verify_containment(spec, ordered)
        if violations:
            result.fail(f"Trial {t}: containment — {violations[0]}")
            continue

        violations = verify_nesting(spec, ordered)
        if violations:
            result.fail(f"Trial {t}: nesting — {violations[0]}")
            continue

        result.ok()

    return result


def test_cyclic_rejection(trials: int, max_handlers: int, rng: random.Random) -> TestResult:
    """
    Suite 2: Random cyclic graphs → verify rejection.

    For each trial:
      - Generate a random spec guaranteed to have a cycle
      - Run topological sort
      - Verify cycle is detected (cycle_nodes non-empty)
    """
    result = TestResult("Cyclic rejection")

    for t in range(trials):
        n = rng.randint(2, max_handlers)
        max_edges = n * (n - 1) // 2
        m = rng.randint(1, max_edges)
        spec = random_cyclic_spec(n, m, rng)

        ordered, cycle_nodes = toposort(spec)

        if not cycle_nodes:
            result.fail(
                f"Trial {t}: cyclic spec not detected "
                f"(n={n}, m={len(spec.constraints)})"
            )
            continue

        result.ok()

    return result


def test_property_nesting_respects_constraints(
    trials: int, max_handlers: int, rng: random.Random
) -> TestResult:
    """
    Suite 3: Property-based — for any acyclic spec, synthesized nesting
    respects all precedence constraints.

    This is the key correctness property: ∀ acyclic spec S,
    ∀ constraint (a, b) ∈ S, a appears before b in the linear extension
    produced by topological sort (equivalently, a is nested inside b
    in the synthesized term).

    We verify this by checking the ordered list directly, and also
    by verifying the synthesized string structure.
    """
    result = TestResult("Property: nesting respects constraints")

    for t in range(trials):
        n = rng.randint(2, max_handlers)
        max_edges = n * (n - 1) // 2
        m = rng.randint(1, max_edges)
        spec = random_acyclic_spec(n, m, rng)

        ordered, cycle_nodes = toposort(spec)

        if cycle_nodes:
            result.fail(f"Trial {t}: unexpected cycle in acyclic spec")
            continue

        # Check every constraint
        all_ok = True
        for a, b in spec.constraints:
            if not appears_before(a, b, ordered):
                result.fail(
                    f"Trial {t}: constraint {a} < {b} not respected "
                    f"in ordered list {[h.name for h in ordered]}"
                )
                all_ok = False
                break

        if not all_ok:
            continue

        # Also verify the synthesized term contains all handler names
        term = synthesize("body", ordered)
        for h in spec.handlers:
            if f"with {h.name}" not in term:
                result.fail(f"Trial {t}: handler {h.name} missing from synthesized term")
                all_ok = False
                break

        if all_ok:
            result.ok()

    return result


def test_edge_cases(rng: random.Random) -> TestResult:
    """
    Suite 4: Edge cases — empty spec, single handler, no constraints,
    complete graph (total order), maximum constraints.
    """
    result = TestResult("Edge cases")

    # Empty spec
    spec = Spec(handlers=[], constraints=[])
    ordered, cycle = toposort(spec)
    if ordered == [] and not cycle:
        result.ok()
    else:
        result.fail(f"Empty spec: expected ([], []), got ({ordered}, {cycle})")

    # Single handler, no constraints
    spec = Spec(handlers=[Handler("H0")], constraints=[])
    ordered, cycle = toposort(spec)
    if len(ordered) == 1 and not cycle:
        result.ok()
    else:
        result.fail(f"Single handler: expected 1 ordered, no cycle")

    # Two handlers, no constraints (partial order — both are minimal)
    spec = Spec(
        handlers=[Handler("H0"), Handler("H1")],
        constraints=[]
    )
    ordered, cycle = toposort(spec)
    if len(ordered) == 2 and not cycle:
        result.ok()
    else:
        result.fail(f"Two handlers no constraints: expected 2 ordered, no cycle")

    # Complete graph (total order): H0 < H1 < H2 < ... < Hn
    n = 5
    handlers = [Handler(f"H{i}") for i in range(n)]
    constraints = [(f"H{i}", f"H{i+1}") for i in range(n - 1)]
    spec = Spec(handlers=handlers, constraints=constraints)
    ordered, cycle = toposort(spec)
    expected = [f"H{i}" for i in range(n)]
    actual = [h.name for h in ordered]
    if actual == expected and not cycle:
        result.ok()
    else:
        result.fail(f"Total order: expected {expected}, got {actual}")

    # Self-loop (should be detected as cyclic)
    spec = Spec(
        handlers=[Handler("H0"), Handler("H1")],
        constraints=[("H0", "H1"), ("H1", "H0")]
    )
    ordered, cycle = toposort(spec)
    if cycle:
        result.ok()
    else:
        result.fail(f"Self-loop: expected cycle detection")

    # All pairs constrained (maximum acyclic edges for n=4)
    n = 4
    handlers = [Handler(f"H{i}") for i in range(n)]
    constraints = [
        (f"H{i}", f"H{j}")
        for i in range(n)
        for j in range(i + 1, n)
    ]
    spec = Spec(handlers=handlers, constraints=constraints)
    ordered, cycle = toposort(spec)
    violations = verify_nesting(spec, ordered)
    if not cycle and not violations:
        result.ok()
    else:
        result.fail(f"Max edges n=4: cycle={cycle}, violations={violations}")

    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description="DTS property-based test harness")
    parser.add_argument("--trials", type=int, default=200,
                        help="Number of random trials per suite (default: 200)")
    parser.add_argument("--max-handlers", type=int, default=15,
                        help="Maximum number of handlers per spec (default: 15)")
    parser.add_argument("--seed", type=int, default=42,
                        help="Random seed for reproducibility (default: 42)")
    args = parser.parse_args()

    rng = random.Random(args.seed)

    print(f"DTS Property-Based Test Harness")
    print(f"  trials={args.trials}, max_handlers={args.max_handlers}, seed={args.seed}")
    print(f"  {'=' * 60}")

    suites = [
        test_acyclic_synthesis(args.trials, args.max_handlers, rng),
        test_cyclic_rejection(args.trials, args.max_handlers, rng),
        test_property_nesting_respects_constraints(args.trials, args.max_handlers, rng),
        test_edge_cases(rng),
    ]

    print()
    total_pass = 0
    total_fail = 0
    for s in suites:
        print(f"  {s.summary()}")
        total_pass += s.passed
        total_fail += s.failed
        for f in s.failures[:5]:
            print(f"    FAIL: {f}")
        if len(s.failures) > 5:
            print(f"    ... and {len(s.failures) - 5} more failures")

    print(f"\n  {'=' * 60}")
    print(f"  Total: {total_pass} passed, {total_fail} failed")
    print(f"  Result: {'ALL PASS' if total_fail == 0 else 'FAILURES'}")

    return 1 if total_fail > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
