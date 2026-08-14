#!/usr/bin/env python3
"""Run the abstract model over every block shape, under every ending.

    uv run --extra solver python scripts/solve_model.py data/skeleton.json

Reports which shapes admit K = 118, validates the model against a real game,
and shows what the home-rank lemma is carrying.

This is a **cross-check**, not the proof. `scripts/analyse_bound.py` refutes
every S ≤ 2 shape by counting, with no solver; what this adds is a second and a
third opinion on the same question.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from long_chess.bound import refutations, switch_lower_bound
from long_chess.model import ENDINGS, all_shapes
from long_chess.model import analyse_independently as independent
from long_chess.skeleton import load

SEGMENT_TARGET = 150


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="solve_model")
    parser.add_argument("skeleton", type=Path, nargs="?")
    parser.add_argument("--max-blocks", type=int, default=4)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    # A missing solver is a skip with exit 0, not a failure — the same shape as
    # `check_movegen.py` skipping when no C compiler is installed. This is a
    # cross-check on a proof that stands without it; turning "OR-Tools is not
    # installed" into "the proof is broken" would be a lie.
    try:
        from long_chess.model import solve, validate
    except ImportError:
        print("[skip] solve_model: OR-Tools absent (uv sync --extra solver)")
        return 0

    shapes = all_shapes(args.max_blocks)
    best: dict[str, int] = {}

    for ending in ENDINGS:
        print(f"--- {ending} ---")
        print(
            f"{'shape':10s} {'S':>2}  {'K = 118?':>10}  {'2nd opinion':>11}"
            f"  {'max K':>5}  {'no lemma':>10}"
        )
        for shape in shapes:
            result = solve(shape, ending=ending)
            second = independent(shape, ending=ending)
            without = solve(shape, ending=ending, home_rank_limit=False)
            if result.feasible != second.feasible:
                print(
                    f"FAIL: the two methods disagree on {shape} ({ending})",
                    file=sys.stderr,
                )
                return 1
            print(
                f"{str(shape):10s} {shape.switches:>2}  {result.status:>10}  "
                f"{'feasible' if second.feasible else 'infeasible':>11}"
                f"  {second.max_k:>5}  {without.status:>10}"
            )
            if result.feasible:
                best[ending] = min(best.get(ending, 99), shape.switches)
        print()

    if not best:
        print("FAIL: no shape admits K = 118, which cannot be right", file=sys.stderr)
        return 1

    for ending in ENDINGS:
        switches = best[ending]
        print(
            f"{ending:>9}: minimum feasible S = {switches}  ->  "
            f"L ≤ {SEGMENT_TARGET} × 118 − {switches} = "
            f"{SEGMENT_TARGET * 118 - switches}"
        )

    # The counting proof decided the same thing without any of this. It only
    # covers S ≤ 2 — the solver refuting more than that (W B W, say) is extra,
    # not a disagreement — but every shape counting kills must come back
    # infeasible here, under both endings, or one of the two is wrong.
    counted = switch_lower_bound()
    refuted = {r.colours for r in refutations()}
    mismatches = [
        (ending, shape)
        for ending in ENDINGS
        for shape in shapes
        if shape.colours in refuted and solve(shape, ending=ending).feasible
    ]
    print()
    print(
        f"counting proof: S ≥ {counted.minimum_switches} "
        f"({len(refuted)} shapes refuted with no solver); solver confirms "
        f"every one: {not mismatches}"
    )
    if mismatches:
        print("FAIL: the solver contradicts the counting proof", file=sys.stderr)
        for ending, shape in mismatches:
            print(f"  {shape} ({ending})", file=sys.stderr)
        return 1
    if any(best[ending] != counted.minimum_switches for ending in ENDINGS):
        print(
            "FAIL: the solver's minimum S does not match the counting proof",
            file=sys.stderr,
        )
        return 1

    carried = [
        (ending, shape)
        for ending in ENDINGS
        for shape in shapes
        if not solve(shape, ending=ending).feasible
        and solve(shape, ending=ending, home_rank_limit=False).feasible
    ]
    print()
    print(
        "ruled out by the home-rank lemma alone: "
        + (", ".join(f"{shape} ({ending})" for ending, shape in carried) or "none")
    )

    if args.skeleton:
        print()
        result = validate(load(args.skeleton))
        observation = result.observation
        print(f"observed   {observation.shape}  S = {observation.shape.switches}")
        print(
            f"           P={observation.total_pawn_moves} "
            f"C={observation.total_captures} Cₚ={observation.pawn_captures} "
            f"M={observation.closing_segment}  ->  K={observation.k}"
        )
        print(f"accepted   {result.accepted}  ({result.status})")
        if not result.accepted:
            print(f"\nFAIL: {result.complaint}", file=sys.stderr)
            return 1
        print("           the model admits a game that exists, so its UNSATs mean")
        print("           something rather than describing its own constraints")

    return 0


if __name__ == "__main__":
    sys.exit(main())
