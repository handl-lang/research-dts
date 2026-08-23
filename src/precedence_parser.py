#!/usr/bin/env python3
"""
Precedence parser for declarative handler topology specs.

Supports two syntaxes for declaring precedence:

  1. Explicit `before` relations:
       A before B
       B before C

  2. Numeric priority sugar:
       A: 10
       B: 5
       C: 20

     Lower number = inner (appears first in nesting). So B(5) < A(10) < C(20).

Both can be combined in the same spec. The parser merges constraints from
both sources into a single precedence graph.

Syntax (one directive per line):

  handler <Name> [handles <op>, ...]
  <Name> before <Name>
  <Name>: <priority>

Lines starting with # are comments. Blank lines are ignored.

Example input:
    # handlers
    handler Auth handles authenticate
    handler Cache handles lookup, store
    handler Logger handles log

    # explicit precedence
    Auth before Cache
    Cache before Logger

    # numeric priority (alternative or supplementary)
    Metrics: 5
    Auth: 10
    Logger: 20
"""

from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional


@dataclass
class Handler:
    name: str
    clauses: Tuple[str, ...] = ("op",)

    def __repr__(self) -> str:
        return f"Handler({self.name})"


@dataclass
class Spec:
    handlers: List[Handler]
    constraints: List[Tuple[str, str]]  # (a, b) means a < b (a is inner)


class ParseError(Exception):
    """User-friendly parse error with line number."""
    def __init__(self, line_num: int, line: str, message: str):
        self.line_num = line_num
        self.line = line
        super().__init__(f"Line {line_num}: {message}\n  > {line.strip()}")


def parse_spec(text: str) -> Spec:
    """
    Parse a declarative handler topology spec into a Spec.

    See module docstring for syntax.
    """
    handlers: Dict[str, Handler] = {}
    handler_order: List[str] = []  # preserve declaration order
    explicit_constraints: List[Tuple[str, str]] = []
    priorities: Dict[str, int] = {}

    lines = text.splitlines()

    for line_num, raw_line in enumerate(lines, start=1):
        line = raw_line.strip()

        # Skip comments and blank lines
        if not line or line.startswith("#"):
            continue

        try:
            if line.startswith("handler "):
                _parse_handler_line(line, handlers, handler_order)
            elif " before " in line:
                _parse_before_line(line, explicit_constraints)
            elif ":" in line and not line.startswith("handler"):
                _parse_priority_line(line, priorities)
            else:
                raise ParseError(line_num, raw_line,
                    f"Unrecognized directive. Expected 'handler ...', 'A before B', or 'A: <priority>'")
        except ParseError:
            raise
        except Exception as e:
            raise ParseError(line_num, raw_line, str(e))

    # Validate: all names in constraints and priorities must be declared handlers
    all_names = set(handlers.keys())
    for a, b in explicit_constraints:
        if a not in all_names:
            raise ParseError(0, "", f"Unknown handler '{a}' in before relation")
        if b not in all_names:
            raise ParseError(0, "", f"Unknown handler '{b}' in before relation")

    for name in priorities:
        if name not in all_names:
            raise ParseError(0, "", f"Unknown handler '{name}' in priority assignment")

    # Derive constraints from numeric priorities
    # Lower priority number = inner = appears before (is nested inside)
    # So if priority[A] < priority[B], then A before B (A < B)
    priority_constraints = _derive_priority_constraints(priorities)

    # Merge constraints, deduplicate
    all_constraints = _merge_constraints(explicit_constraints, priority_constraints)

    # Build handler list in declaration order
    handler_list = [handlers[name] for name in handler_order]

    return Spec(handlers=handler_list, constraints=all_constraints)


def _parse_handler_line(
    line: str,
    handlers: Dict[str, Handler],
    handler_order: List[str]
) -> None:
    """Parse: handler <Name> [handles <op>, ...]"""
    parts = line.split(None, 1)  # split on first whitespace
    # parts[0] == "handler"
    rest = parts[1] if len(parts) > 1 else ""

    if " handles " in rest:
        name_part, clauses_part = rest.split(" handles ", 1)
        name = name_part.strip()
        clauses = tuple(c.strip() for c in clauses_part.split(","))
    else:
        name = rest.strip()
        clauses = ("op",)

    if not name:
        raise ValueError("Missing handler name")

    if name in handlers:
        raise ValueError(f"Duplicate handler '{name}'")

    h = Handler(name=name, clauses=clauses)
    handlers[name] = h
    handler_order.append(name)


def _parse_before_line(line: str, constraints: List[Tuple[str, str]]) -> None:
    """Parse: A before B"""
    parts = line.split(" before ")
    if len(parts) != 2:
        raise ValueError(f"Expected 'A before B', got: {line}")
    a = parts[0].strip()
    b = parts[1].strip()
    if not a or not b:
        raise ValueError("Missing handler name in before relation")
    constraints.append((a, b))


def _parse_priority_line(line: str, priorities: Dict[str, int]) -> None:
    """Parse: A: <priority>"""
    name_part, prio_part = line.split(":", 1)
    name = name_part.strip()
    if not name:
        raise ValueError("Missing handler name in priority assignment")
    try:
        priority = int(prio_part.strip())
    except ValueError:
        raise ValueError(f"Invalid priority value: '{prio_part.strip()}' (must be integer)")
    priorities[name] = priority


def _derive_priority_constraints(
    priorities: Dict[str, int]
) -> List[Tuple[str, str]]:
    """
    Derive precedence constraints from numeric priorities.
    Lower number = inner = appears before (A < B if priority[A] < priority[B]).
    Only generates constraints for distinct priority values.
    Handlers with equal priority are unordered (no constraint between them).
    """
    constraints = []
    items = list(priorities.items())
    for i, (a, pa) in enumerate(items):
        for b, pb in items[i + 1:]:
            if pa < pb:
                constraints.append((a, b))
            elif pb < pa:
                constraints.append((b, a))
            # equal: no constraint (partial order)
    return constraints


def _merge_constraints(
    explicit: List[Tuple[str, str]],
    derived: List[Tuple[str, str]]
) -> List[Tuple[str, str]]:
    """Merge and deduplicate constraints from explicit and derived sources."""
    seen = set()
    merged = []
    for c in explicit + derived:
        if c not in seen:
            seen.add(c)
            merged.append(c)
    return merged


# ---------------------------------------------------------------------------
# Pretty printing
# ---------------------------------------------------------------------------

def format_spec(spec: Spec) -> str:
    """Format a Spec back into human-readable declarative syntax."""
    lines = []
    for h in spec.handlers:
        if h.clauses == ("op",):
            lines.append(f"handler {h.name}")
        else:
            lines.append(f"handler {h.name} handles {', '.join(h.clauses)}")
    if spec.constraints:
        lines.append("")
        for a, b in spec.constraints:
            lines.append(f"{a} before {b}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI for testing
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys

    example = """\
# HTTP middleware with mixed explicit + numeric priority
handler Auth handles authenticate
handler Cache handles lookup, store
handler Logger handles log
handler Metrics handles timing

# explicit constraints
Auth before Cache
Cache before Logger

# numeric priority (Metrics should be outermost)
Metrics: 50
Auth: 10
"""

    print("== Input spec ==")
    print(example)

    spec = parse_spec(example)

    print("== Parsed spec ==")
    print(format_spec(spec))

    print(f"\n== Summary ==")
    print(f"  Handlers: {[h.name for h in spec.handlers]}")
    print(f"  Constraints: {spec.constraints}")
