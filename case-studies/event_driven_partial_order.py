#!/usr/bin/env python3
"""
Case Study 2: Event-driven handler chain with partial order.

Unlike the HTTP middleware case study (total order: Auth < Cache < Logger),
this demonstrates a *partial* order: some handlers are unordered relative
to each other, and the synthesis still produces a valid nesting.

Handler set and precedence:
  - Validator   (validates input events)
  - Auth        (checks permissions)
  - Logger      (records all events)
  - Metrics     (collects timing/count metrics)

Precedence constraints:
  Validator < Auth       (validate before auth — don't auth malformed input)
  Validator < Logger     (validate before logging — don't log invalid events)
  Auth < Metrics         (auth before metrics — don't collect metrics on unauthorized)
  Logger < Metrics       (log before metrics — metrics are the outermost layer)

Unordered pairs:
  Auth vs Logger         (no constraint between them — either nesting is valid)

This is a partial order: Auth and Logger are incomparable. The topological
sort picks one valid linear extension, but the other would be equally valid.
"""

from dataclasses import dataclass, field
from collections import deque
from typing import Callable, Dict, List, Tuple


@dataclass
class Handler:
    name: str
    clauses: List[str] = field(default_factory=list)

    def wrap(self, next_fn: Callable[[dict], dict]) -> Callable[[dict], dict]:
        def handler(event: dict) -> dict:
            print(f"  [{self.name}] entering")
            if self.name == "Validator":
                if not event.get("type"):
                    raise ValueError(f"[{self.name}] Missing event type")
                event["validated"] = True
            elif self.name == "Auth":
                if not event.get("token"):
                    raise PermissionError(f"[{self.name}] Missing token")
                event["authenticated"] = True
            elif self.name == "Logger":
                event.setdefault("log", []).append(f"event:{event.get('type')}")
            elif self.name == "Metrics":
                event.setdefault("metrics", {})["count"] = \
                    event.get("metrics", {}).get("count", 0) + 1
            response = next_fn(event)
            print(f"  [{self.name}] exiting")
            return response
        return handler


def toposort(handlers: List[Handler],
             constraints: List[Tuple[str, str]]) -> List[Handler]:
    """
    Topological sort. A constraint (a, b) means a < b (a is inner).
    Returns one valid linear extension. Raises on cycles.
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

    if len(ordered) != len(handlers):
        raise ValueError("Precedence relation contains a cycle")

    return ordered


def synthesize(body: str, ordered: List[Handler]) -> str:
    """Synthesize the explicit nested handle term from the linear extension."""
    if not ordered:
        return body
    prefix = "handle (" * (len(ordered) - 1)
    inner = f"handle {body} with {ordered[0].name}"
    suffix = "".join(f") with {h.name}" for h in ordered[1:])
    return prefix + inner + suffix


def find_incomparable_pairs(
    handlers: List[Handler],
    constraints: List[Tuple[str, str]]
) -> List[Tuple[str, str]]:
    """
    Find pairs of handlers with no precedence constraint in either direction.
    These are the 'unordered' pairs that make the order partial.
    """
    names = [h.name for h in handlers]
    constraint_set = set(constraints)
    pairs = []
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            if (a, b) not in constraint_set and (b, a) not in constraint_set:
                pairs.append((a, b))
    return pairs


def creates_cycle(
    handlers: List[Handler],
    constraints: List[Tuple[str, str]],
    a: str,
    b: str
) -> bool:
    """Check if adding constraint (b, a) on top of existing constraints creates a cycle."""
    try:
        toposort(handlers, constraints + [(b, a)])
        return False
    except ValueError:
        return True


def main() -> None:
    validator = Handler("Validator", ["validate"])
    auth = Handler("Auth", ["authenticate"])
    logger = Handler("Logger", ["log"])
    metrics = Handler("Metrics", ["timing", "count"])
    handlers = [validator, auth, logger, metrics]

    constraints: List[Tuple[str, str]] = [
        ("Validator", "Auth"),
        ("Validator", "Logger"),
        ("Auth", "Metrics"),
        ("Logger", "Metrics"),
    ]

    print("== Declarative spec ==")
    for h in handlers:
        print(f"  handler {h.name}: handles {h.clauses}")
    print(f"  precedence constraints: {constraints}")

    incomparable = find_incomparable_pairs(handlers, constraints)
    print(f"\n== Partial order analysis ==")
    print(f"  Unordered pairs (incomparable): {incomparable}")
    print(f"  This is a PARTIAL order — {len(incomparable)} pair(s) have no constraint.")

    ordered = toposort(handlers, constraints)
    print(f"\n== Linear extension (one valid topological sort) ==")
    print(f"  {' < '.join(h.name for h in ordered)}  (inner -> outer)")
    print(f"  Note: other valid orderings exist for incomparable pairs.")

    body = "event_body"
    term = synthesize(body, ordered)
    print(f"\n== Synthesized nested handle term ==")
    print(f"  {term}")

    # Show an alternative valid ordering by swapping a truly incomparable pair.
    # Auth and Logger have no direct or transitive constraint between them.
    swap_pairs = [(a, b) for a, b in incomparable
                  if not creates_cycle(handlers, constraints, a, b)]
    if swap_pairs:
        a, b = swap_pairs[0]
        print(f"\n== Alternative ordering (swapping {a} and {b}) ==")
        alt_constraints = constraints + [(b, a)]
        alt_ordered = toposort(handlers, alt_constraints)
        alt_term = synthesize(body, alt_ordered)
        print(f"  {' < '.join(h.name for h in alt_ordered)}  (inner -> outer)")
        print(f"  {alt_term}")
        print(f"  Both orderings are valid — the partial order allows either.")

    print("\n== Tiny execution (first ordering) ==")
    body_fn = lambda evt: {"status": "ok", "event": evt}
    pipeline = body_fn
    for h in ordered:
        pipeline = h.wrap(pipeline)

    event = {
        "type": "user.created",
        "token": "Bearer xyz",
    }
    result = pipeline(event)
    print(f"\n== Final result ==")
    print(f"  {result}")


if __name__ == "__main__":
    main()
