#!/usr/bin/env bash
# ci.sh — research-dts CI gate for the bupha shell runner.
#
# Two artifacts gate here:
#   lean/   — the formalization; `lake exe cache get` pulls the pinned
#             mathlib olean cache, `lake build` compiles Dts + ListDigraph.
#   python/ — the tooling/case-study package; tests are self-running
#             scripts (no pytest dep) executed under `uv run`.
set -euo pipefail

cd "$(dirname "$0")"

( cd lean && lake exe cache get && lake build )

( cd python && uv sync \
    && uv run python tests/test_precedence_parser.py \
    && uv run python tests/test_synthesis.py )

echo "ci passed: lake build + python tests"
