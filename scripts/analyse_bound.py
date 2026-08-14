#!/usr/bin/env python3
"""Re-derive K ≤ 118 and S ≥ 3 by counting, with no solver involved.

uv run python scripts/analyse_bound.py

This is the proof. `scripts/solve_model.py` re-decides the same question with
CP-SAT and again with arithmetic, and those are cross-checks on this one.
"""

from __future__ import annotations

import argparse
import sys

from long_chess.bound import (
    FILES,
    MAX_NET_PAWN_MOVES,
    captures_plus_closing_bound,
    check_file_lemma,
    check_origin_pair_cap,
    critical_bound,
    ending_profiles,
    equality_conditions,
    net_pawn_move_bound,
    pawn_moves_ceiling,
    ply_bound,
    refutations,
    switch_lower_bound,
)


def wrap(text: str, width: int = 74, indent: str = "    ") -> list[str]:
    words, lines, current = text.split(), [], ""
    for word in words:
        if len(current) + len(word) + 1 > width:
            lines.append(indent + current)
            current = word
        else:
            current = f"{current} {word}".strip()
    if current:
        lines.append(indent + current)
    return lines


def main(argv: list[str] | None = None) -> int:
    argparse.ArgumentParser(prog="analyse_bound").parse_args(argv)

    pair = check_origin_pair_cap()
    print("origin pair   the two pawns starting on one file, neither ever")
    print("              moving diagonally — a relaxation of chess, exhausted")
    print(
        f"              {pair.states_explored} states, at most "
        f"{pair.max_moves} combined moves "
        f"({pair.max_moves_while_both_remain} while both remain, then a whole "
        "second lifetime)"
    )
    if pair.max_moves != 10:
        print(
            f"FAIL: the origin-pair cap came out at {pair.max_moves}",
            file=sys.stderr,
        )
        return 1

    lemma = check_file_lemma()
    print()
    print("file lemma    the same two pawns cannot both promote")
    print(
        f"              {lemma.states_explored} states exhausted, "
        f"both promote: {lemma.goal_reachable}  (must be False)"
    )
    if lemma.goal_reachable:
        print("FAIL: the pawn-capture term is not justified", file=sys.stderr)
        return 1

    envelope = net_pawn_move_bound()
    print()
    print("P − Cₚ        P ≤ min(96, 80 + 2f) and Cₚ ≥ f, maximised over f")
    print("              f:  " + "  ".join(f"{f:>2}" for f in range(FILES + 1)))
    print(
        "              P:  "
        + "  ".join(f"{pawn_moves_ceiling(f):>2}" for f in range(FILES + 1))
    )
    print(
        "            P−O:  "
        + "  ".join(f"{pawn_moves_ceiling(f) - f:>2}" for f in range(FILES + 1))
    )
    print(f"              {envelope.describe()}")

    print()
    print("C + T         30 capturable pieces, and at most one closing segment")
    for profile in ending_profiles():
        print(
            f"              {profile.name:>13s}: C={profile.captures} "
            f"T={profile.closing_segment}  ->  {profile.total}"
        )
    print(f"              C + T ≤ {captures_plus_closing_bound()}, either way")

    bound = critical_bound()
    print()
    print(f"bound         {bound.describe()}")
    if bound.total != MAX_NET_PAWN_MOVES + captures_plus_closing_bound():
        print("FAIL: the terms do not add up", file=sys.stderr)
        return 1

    equality = equality_conditions()
    print()
    print("equality      " + equality.describe())

    print()
    print("S ≤ 2 block shapes — every one refuted, by counting and one lemma")
    for refutation in refutations():
        head, detail = refutation.describe().split("\n", 1)
        print(f"  {head}")
        for line in wrap(detail.strip(), indent="      "):
            print(line)

    try:
        switch = switch_lower_bound()
    except ValueError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    print()
    print(f"at K = 118    {switch.describe()}")

    # `S ≥ 3` is conditional on K = 118 and false in general -- four knight
    # shuffles reach fivefold repetition with K = 1 and S = 0. The theorem needs
    # a case split, and the smaller case needs no switch argument at all.
    print()
    print("result        " + ply_bound().describe().replace("\n", "\n              "))
    return 0


if __name__ == "__main__":
    sys.exit(main())
