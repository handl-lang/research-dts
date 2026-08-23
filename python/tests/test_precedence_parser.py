#!/usr/bin/env python3
"""
Tests for the precedence parser — explicit `before` relations and numeric
priority sugar, including mixed specs, error cases, and edge cases.

Run:
    uv run python tests/test_precedence_parser.py
"""

import sys

from dts.precedence_parser import (
    parse_spec, format_spec, ParseError, Handler, Spec,
    _derive_priority_constraints, _merge_constraints,
)


class TestRunner:
    def __init__(self):
        self.passed = 0
        self.failed = 0
        self.failures = []

    def assert_eq(self, name, actual, expected):
        if actual == expected:
            self.passed += 1
        else:
            self.failed += 1
            self.failures.append(f"{name}: expected {expected!r}, got {actual!r}")

    def assert_true(self, name, cond, msg=""):
        if cond:
            self.passed += 1
        else:
            self.failed += 1
            self.failures.append(f"{name}: {msg}")

    def assert_raises(self, name, exc_type, fn):
        try:
            fn()
            self.failed += 1
            self.failures.append(f"{name}: expected {exc_type.__name__} but no exception")
        except exc_type:
            self.passed += 1
        except Exception as e:
            self.failed += 1
            self.failures.append(f"{name}: expected {exc_type.__name__}, got {type(e).__name__}: {e}")

    def summary(self):
        total = self.passed + self.failed
        status = "PASS" if self.failed == 0 else "FAIL"
        return f"[{status}] {self.passed}/{total} passed"


def test_explicit_before(t: TestRunner):
    """Parse explicit 'A before B' relations."""
    text = """
    handler Auth handles authenticate
    handler Cache handles lookup, store
    handler Logger handles log

    Auth before Cache
    Cache before Logger
    """
    spec = parse_spec(text)

    t.assert_eq("explicit: handler count", len(spec.handlers), 3)
    t.assert_eq("explicit: handler names",
                [h.name for h in spec.handlers], ["Auth", "Cache", "Logger"])
    t.assert_eq("explicit: constraints", spec.constraints,
                [("Auth", "Cache"), ("Cache", "Logger")])
    t.assert_eq("explicit: clauses",
                spec.handlers[0].clauses, ("authenticate",))
    t.assert_eq("explicit: multi-clauses",
                spec.handlers[1].clauses, ("lookup", "store"))


def test_numeric_priority(t: TestRunner):
    """Parse numeric priority sugar and derive constraints."""
    text = """
    handler A handles op1
    handler B handles op2
    handler C handles op3

    A: 10
    B: 5
    C: 20
    """
    spec = parse_spec(text)

    # B(5) < A(10) < C(20)
    t.assert_eq("priority: handler count", len(spec.handlers), 3)
    t.assert_true("priority: B<A constraint", ("B", "A") in spec.constraints)
    t.assert_true("priority: A<C constraint", ("A", "C") in spec.constraints)
    t.assert_true("priority: B<C constraint", ("B", "C") in spec.constraints)
    t.assert_eq("priority: total constraints", len(spec.constraints), 3)


def test_equal_priority_no_constraint(t: TestRunner):
    """Handlers with equal priority should have no constraint between them."""
    text = """
    handler A
    handler B
    handler C

    A: 5
    B: 5
    C: 10
    """
    spec = parse_spec(text)

    # A and B both have priority 5 — no constraint between them
    # Both should be before C
    t.assert_true("equal: A<C", ("A", "C") in spec.constraints)
    t.assert_true("equal: B<C", ("B", "C") in spec.constraints)
    t.assert_true("equal: no A<B", ("A", "B") not in spec.constraints)
    t.assert_true("equal: no B<A", ("B", "A") not in spec.constraints)
    t.assert_eq("equal: total constraints", len(spec.constraints), 2)


def test_mixed_explicit_and_numeric(t: TestRunner):
    """Mix explicit 'before' and numeric priority in the same spec."""
    text = """
    handler Auth handles authenticate
    handler Cache handles lookup, store
    handler Logger handles log
    handler Metrics handles timing

    Auth before Cache
    Cache before Logger

    Metrics: 50
    Auth: 10
    """
    spec = parse_spec(text)

    # Explicit: Auth < Cache, Cache < Logger
    # Numeric: Auth(10) < Metrics(50)
    t.assert_true("mixed: Auth<Cache", ("Auth", "Cache") in spec.constraints)
    t.assert_true("mixed: Cache<Logger", ("Cache", "Logger") in spec.constraints)
    t.assert_true("mixed: Auth<Metrics", ("Auth", "Metrics") in spec.constraints)
    t.assert_eq("mixed: handler count", len(spec.handlers), 4)


def test_priority_requires_declared_handler(t: TestRunner):
    """Handlers in priorities must be declared with 'handler' first."""
    text = """
    handler A handles op1

    A: 10
    B: 5
    """
    t.assert_raises("priority: undeclared handler error", ParseError, lambda: parse_spec(text))


def test_comments_and_blanks(t: TestRunner):
    """Comments and blank lines are ignored."""
    text = """
    # This is a comment
    handler A handles op1

    # Another comment

    A before B
    handler B handles op2
    """
    spec = parse_spec(text)

    t.assert_eq("comments: handler count", len(spec.handlers), 2)
    t.assert_eq("comments: constraints", spec.constraints, [("A", "B")])


def test_default_clauses(t: TestRunner):
    """Handler without 'handles' gets default clause ('op',)."""
    text = """
    handler A
    handler B

    A before B
    """
    spec = parse_spec(text)

    t.assert_eq("default: A clauses", spec.handlers[0].clauses, ("op",))
    t.assert_eq("default: B clauses", spec.handlers[1].clauses, ("op",))


def test_error_unknown_handler_in_before(t: TestRunner):
    """Error: 'before' references undeclared handler."""
    text = """
    handler A

    A before B
    """
    t.assert_raises("error: unknown handler in before", ParseError, lambda: parse_spec(text))


def test_error_unknown_handler_in_priority(t: TestRunner):
    """Error: priority references undeclared handler."""
    text = """
    handler A

    X: 10
    """
    t.assert_raises("error: unknown handler in priority", ParseError, lambda: parse_spec(text))


def test_error_invalid_priority(t: TestRunner):
    """Error: non-integer priority value."""
    text = """
    handler A

    A: high
    """
    t.assert_raises("error: invalid priority", ParseError, lambda: parse_spec(text))


def test_error_unrecognized_line(t: TestRunner):
    """Error: unrecognized directive."""
    text = """
    handler A
    something weird
    """
    t.assert_raises("error: unrecognized", ParseError, lambda: parse_spec(text))


def test_error_duplicate_handler(t: TestRunner):
    """Error: duplicate handler declaration."""
    text = """
    handler A handles op1
    handler A handles op2
    """
    t.assert_raises("error: duplicate handler", ParseError, lambda: parse_spec(text))


def test_error_self_before(t: TestRunner):
    """Self-before is syntactically valid but will be caught as a cycle by toposort."""
    text = """
    handler A
    A before A
    """
    # Parser should accept this (it's a valid parse); cycle detection is downstream
    spec = parse_spec(text)
    t.assert_eq("self-before: constraints", spec.constraints, [("A", "A")])


def test_empty_spec(t: TestRunner):
    """Empty input produces empty spec."""
    spec = parse_spec("")
    t.assert_eq("empty: handlers", len(spec.handlers), 0)
    t.assert_eq("empty: constraints", len(spec.constraints), 0)


def test_only_comments(t: TestRunner):
    """Only comments produces empty spec."""
    text = """
    # just comments
    # nothing else
    """
    spec = parse_spec(text)
    t.assert_eq("comments-only: handlers", len(spec.handlers), 0)


def test_format_roundtrip(t: TestRunner):
    """format_spec produces parseable output."""
    text = """
    handler Auth handles authenticate
    handler Cache handles lookup, store

    Auth before Cache
    """
    spec = parse_spec(text)
    formatted = format_spec(spec)
    spec2 = parse_spec(formatted)

    t.assert_eq("roundtrip: handler names",
                [h.name for h in spec.handlers], [h.name for h in spec2.handlers])
    t.assert_eq("roundtrip: constraints", spec.constraints, spec2.constraints)


def test_priority_constraints_helper(t: TestRunner):
    """Directly test _derive_priority_constraints."""
    priorities = {"A": 10, "B": 5, "C": 20}
    constraints = _derive_priority_constraints(priorities)

    t.assert_true("helper: B<A", ("B", "A") in constraints)
    t.assert_true("helper: A<C", ("A", "C") in constraints)
    t.assert_true("helper: B<C", ("B", "C") in constraints)
    t.assert_eq("helper: count", len(constraints), 3)


def test_merge_dedup(t: TestRunner):
    """_merge_constraints deduplicates."""
    explicit = [("A", "B"), ("B", "C")]
    derived = [("B", "C"), ("A", "C")]
    merged = _merge_constraints(explicit, derived)

    t.assert_eq("merge: count", len(merged), 3)
    t.assert_true("merge: A<B", ("A", "B") in merged)
    t.assert_true("merge: B<C", ("B", "C") in merged)
    t.assert_true("merge: A<C", ("A", "C") in merged)


def test_single_handler(t: TestRunner):
    """Single handler, no constraints."""
    text = "handler A handles op1"
    spec = parse_spec(text)

    t.assert_eq("single: count", len(spec.handlers), 1)
    t.assert_eq("single: constraints", len(spec.constraints), 0)


def test_declaration_order_preserved(t: TestRunner):
    """Handler declaration order is preserved in the output."""
    text = """
    handler Zebra
    handler Alpha
    handler Mike

    Alpha before Zebra
    """
    spec = parse_spec(text)

    t.assert_eq("order: declaration order",
                [h.name for h in spec.handlers], ["Zebra", "Alpha", "Mike"])


def main():
    t = TestRunner()

    tests = [
        test_explicit_before,
        test_numeric_priority,
        test_equal_priority_no_constraint,
        test_mixed_explicit_and_numeric,
        test_priority_requires_declared_handler,
        test_comments_and_blanks,
        test_default_clauses,
        test_error_unknown_handler_in_before,
        test_error_unknown_handler_in_priority,
        test_error_invalid_priority,
        test_error_unrecognized_line,
        test_error_duplicate_handler,
        test_error_self_before,
        test_empty_spec,
        test_only_comments,
        test_format_roundtrip,
        test_priority_constraints_helper,
        test_merge_dedup,
        test_single_handler,
        test_declaration_order_preserved,
    ]

    for test_fn in tests:
        test_fn(t)

    print(f"Precedence Parser Tests")
    print(f"  {t.summary()}")
    for f in t.failures:
        print(f"    FAIL: {f}")

    return 1 if t.failed > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
