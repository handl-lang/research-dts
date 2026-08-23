#!/usr/bin/env python3
"""
Declarative HTTP-middleware topology synthesis case study.

This script mirrors the paper's synthesis function S(D, P):
  - three handlers: Auth, Cache, Logger
  - precedence relation: Auth ≺ Cache ≺ Logger
  - a topological sort produces a linear extension
  - the synthesized explicit nested `handle` term is printed
  - a tiny execution shows the handlers wrapping an HTTP request body.
"""

from dataclasses import dataclass, field
from collections import deque
from typing import Callable, Dict, List, Tuple


@dataclass
class Handler:
    """A handler with a name and one or more operation clauses."""
    name: str
    clauses: List[str] = field(default_factory=list)

    def wrap(self, next_fn: Callable[[dict], dict]) -> Callable[[dict], dict]:
        """Build a nested function that runs this handler around next_fn."""
        def handler(request: dict) -> dict:
            print(f"  [{self.name}] entering")
            if self.name == "Auth":
                if not request.get("headers", {}).get("Authorization"):
                    raise PermissionError(f"[{self.name}] Unauthorized")
                request["user"] = "alice"
            elif self.name == "Cache":
                request["cache"] = "miss"
            elif self.name == "Logger":
                request.setdefault("log", []).append("request received")
            response = next_fn(request)
            print(f"  [{self.name}] exiting")
            return response
        return handler


def toposort(handlers: List[Handler],
             constraints: List[Tuple[str, str]]) -> List[Handler]:
    """
    Topological sort of handlers given precedence constraints.
    A constraint (a, b) means a ≺ b: a must appear before b (a is inner).
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
    """
    Synthesize the explicit nested `handle` term from the linear extension.
    The first handler in `ordered` becomes the innermost handler.
    """
    if not ordered:
        return body
    prefix = "handle (" * (len(ordered) - 1)
    inner = f"handle {body} with {ordered[0].name}"
    suffix = "".join(f") with {h.name}" for h in ordered[1:])
    return prefix + inner + suffix


def main() -> None:
    auth = Handler("Auth", ["authenticate"])
    cache = Handler("Cache", ["lookup", "store"])
    logger = Handler("Logger", ["log"])
    handlers = [auth, cache, logger]

    # Auth ≺ Cache ≺ Logger
    constraints: List[Tuple[str, str]] = [
        ("Auth", "Cache"),
        ("Cache", "Logger"),
    ]

    print("== Declarative spec ==")
    for h in handlers:
        print(f"  handler {h.name}: handles {h.clauses}")
    print(f"  precedence constraints: {constraints}")

    ordered = toposort(handlers, constraints)
    print("\n== Linear extension (topological sort) ==")
    print("  " + " < ".join(h.name for h in ordered) + "  (inner -> outer)")

    body = "http_body"
    term = synthesize(body, ordered)
    print("\n== Synthesized nested handle term ==")
    print(f"  {term}")

    print("\n== Tiny execution ==")
    body_fn = lambda req: {"status": 200, "body": "Hello, world!", "request": req}
    pipeline = body_fn
    for h in ordered:
        pipeline = h.wrap(pipeline)

    request = {
        "headers": {"Authorization": "Bearer xyz"},
        "path": "/",
    }
    result = pipeline(request)
    print("\n== Final result ==")
    print(f"  {result}")


if __name__ == "__main__":
    main()
