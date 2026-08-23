#!/usr/bin/env python3
"""
Synthesis and case-study tests.

Covers:
- HTTP middleware total-order synthesis
- Event-driven partial-order synthesis
- Cyclic precedence detection
- Property-based eval harness

Run:
    uv run python tests/test_synthesis.py
"""

import random

from dts.case_studies.http_middleware import (
    Handler as HTTPHandler,
    toposort as http_toposort,
    synthesize as http_synthesize,
)
from dts.case_studies.event_driven_partial_order import (
    Handler as EventHandler,
    toposort as event_toposort,
    find_incomparable_pairs,
    creates_cycle,
    synthesize as event_synthesize,
)
from dts.case_studies.cyclic_detection import (
    Handler as CycleHandler,
    toposort_or_cycle,
    find_cycle_path,
)
from dts.eval.property_tests import (
    test_acyclic_synthesis,
    test_cyclic_rejection,
    test_property_nesting_respects_constraints,
    test_edge_cases,
)


def test_http_middleware_synthesis() -> None:
    auth = HTTPHandler("Auth", ["authenticate"])
    cache = HTTPHandler("Cache", ["lookup", "store"])
    logger = HTTPHandler("Logger", ["log"])
    handlers = [auth, cache, logger]
    constraints = [("Auth", "Cache"), ("Cache", "Logger")]

    ordered = http_toposort(handlers, constraints)
    assert [h.name for h in ordered] == ["Auth", "Cache", "Logger"]

    term = http_synthesize("http_body", ordered)
    assert "handle http_body with Auth" in term
    assert term == "handle (handle (handle http_body with Auth) with Cache) with Logger"


def test_event_driven_partial_order() -> None:
    validator = EventHandler("Validator", ["validate"])
    auth = EventHandler("Auth", ["authenticate"])
    logger = EventHandler("Logger", ["log"])
    metrics = EventHandler("Metrics", ["timing", "count"])
    handlers = [validator, auth, logger, metrics]
    constraints = [
        ("Validator", "Auth"),
        ("Validator", "Logger"),
        ("Auth", "Metrics"),
        ("Logger", "Metrics"),
    ]

    ordered = event_toposort(handlers, constraints)
    ordered_names = [h.name for h in ordered]

    # Validator must be innermost; Metrics outermost
    assert ordered_names.index("Validator") < ordered_names.index("Auth")
    assert ordered_names.index("Validator") < ordered_names.index("Logger")
    assert ordered_names.index("Auth") < ordered_names.index("Metrics")
    assert ordered_names.index("Logger") < ordered_names.index("Metrics")

    # Auth and Logger are incomparable under the partial order
    incomparable = find_incomparable_pairs(handlers, constraints)
    assert ("Auth", "Logger") in incomparable

    # Swapping either does not create a cycle
    assert creates_cycle(handlers, constraints, "Auth", "Logger") is False
    assert creates_cycle(handlers, constraints, "Logger", "Auth") is False

    term = event_synthesize("event_body", ordered)
    assert "handle event_body with" in term


def test_cyclic_detection() -> None:
    # Simple two-cycle
    h1 = [CycleHandler("A", ["op1"]), CycleHandler("B", ["op2"])]
    c1 = [("A", "B"), ("B", "A")]
    ordered, cycle = toposort_or_cycle(h1, c1)
    assert cycle != []
    path = find_cycle_path(h1, c1, cycle)
    assert "A" in path and "B" in path

    # Longer cycle A < B < C < A
    h2 = [CycleHandler("A", ["op1"]), CycleHandler("B", ["op2"]), CycleHandler("C", ["op3"])]
    c2 = [("A", "B"), ("B", "C"), ("C", "A")]
    ordered, cycle = toposort_or_cycle(h2, c2)
    assert cycle != []
    path = find_cycle_path(h2, c2, cycle)
    assert "A" in path and "B" in path and "C" in path

    # Acyclic chain
    h3 = [CycleHandler("A", ["op1"]), CycleHandler("B", ["op2"]), CycleHandler("C", ["op3"])]
    c3 = [("A", "B"), ("B", "C")]
    ordered, cycle = toposort_or_cycle(h3, c3)
    assert cycle == []
    assert [h.name for h in ordered] == ["A", "B", "C"]


def test_property_based_eval() -> None:
    rng = random.Random(42)
    suites = [
        test_acyclic_synthesis(50, 10, rng),
        test_cyclic_rejection(50, 10, rng),
        test_property_nesting_respects_constraints(50, 10, rng),
        test_edge_cases(rng),
    ]
    for result in suites:
        assert result.failed == 0, (
            f"{result.summary()}: {result.failures[:5]}"
        )


if __name__ == "__main__":
    test_http_middleware_synthesis()
    test_event_driven_partial_order()
    test_cyclic_detection()
    test_property_based_eval()
    print("All synthesis tests passed.")
