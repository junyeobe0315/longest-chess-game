#!/usr/bin/env python3
"""Build the independent C checker and run every check it offers.

    uv run python scripts/check_movegen.py           # perft to depth 5, ~20 s
    uv run python scripts/check_movegen.py --deep    # perft to depth 6, ~30 s

Every other mechanical check in this repository decides chess questions with
python-chess, so python-chess's move generation sits inside the trusted base
stated in docs/verification.md. `checker/longest_check.c` is a second generator, written
against the FIDE Laws in a different language and a different board
representation, and this script is what makes the two of them meet: it compiles
the C, replays the witness under both, and compares the results byte for byte.

Two of the checks are differentials and the rest are self-contained. The
differentials are the ones that reduce trust — a disagreement names a position
and a move, and one of the two implementations is then wrong. The self-contained
ones (perft against published node counts, the hand-written rule cases) are what
stop the two implementations from being wrong in the same direction: agreement
between two generators that both drop en passant is agreement about nothing.

A missing C compiler is not a failure. This mirrors how the CP-SAT tests skip
when OR-Tools is absent: the check that could not run says so and returns 0,
rather than turning "not installed" into "broken".
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

import chess

REPO = Path(__file__).resolve().parent.parent
SOURCE = REPO / "checker" / "longest_check.c"
WITNESS = REPO / "data" / "longest.pgn"
STORED_TRACE = REPO / "data" / "longest.trace.tsv"
DUMP_SCRIPT = REPO / "scripts" / "dump_legal_moves.py"

# The documented build line, exactly as checker/README.md states it. -Werror is
# part of the deliverable and not a convenience: the C file is meant to compile
# clean, and a warning it has started to produce is something a reader should be
# told about rather than something this script should absorb.
CFLAGS = ["-std=c99", "-O2", "-Wall", "-Wextra", "-Werror", "-pedantic"]

# $CC first so a CI matrix can pin the compiler; then the usual names. `cc` is
# tried before `gcc` because it is whatever the platform considers standard.
CANDIDATE_COMPILERS = ("cc", "gcc", "clang")

# These are claims about the game, not knowledge the checker has. Nothing about
# the length or the ending is compiled into the C file; both arrive on its
# command line and are compared against what its own replay found. The same two
# values appear in the Makefile's `witness` target for the same reason.
EXPECTED_PLIES = 17697
EXPECTED_TERMINATION = "checkmate"


@dataclass
class Check:
    """One named verdict, with the line the summary should print for it."""

    name: str
    ok: bool
    detail: str


def find_compiler(requested: str | None) -> str | None:
    """The compiler to build with, or None if there is nothing to build with."""
    if requested is not None:
        return requested if shutil.which(requested) else None
    for name in (os.environ.get("CC"), *CANDIDATE_COMPILERS):
        if name and shutil.which(name):
            return name
    return None


def compiler_version(compiler: str) -> str:
    """The compiler's own first line of self-description, for the log."""
    try:
        completed = subprocess.run(
            [compiler, "--version"], capture_output=True, text=True, check=False
        )
    except OSError:
        return compiler
    first = completed.stdout.splitlines()
    return first[0].strip() if first else compiler


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, capture_output=True, text=True, check=False)


def last_line(completed: subprocess.CompletedProcess[str]) -> str:
    """The final non-empty line of stdout — every C mode ends with its tally."""
    lines = [line for line in completed.stdout.splitlines() if line.strip()]
    return lines[-1] if lines else "(no output)"


def field(completed: subprocess.CompletedProcess[str], label: str) -> str:
    """A value from the checker's aligned `label   value` replay report."""
    for line in completed.stdout.splitlines():
        if line.startswith(label):
            return line[len(label) :].strip()
    return "?"


def first_difference(left: Path, right: Path) -> str | None:
    """Where two text files first disagree, or None if they are identical.

    Reported as a line number and the two lines, because that is the whole
    value of a differential: the answer to "they disagree" has to be a position
    a reader can go and look at, not a byte offset.
    """
    left_lines = left.read_text(encoding="utf-8").splitlines()
    right_lines = right.read_text(encoding="utf-8").splitlines()
    for index in range(min(len(left_lines), len(right_lines))):
        if left_lines[index] != right_lines[index]:
            return (
                f"line {index + 1} differs\n"
                f"    python: {left_lines[index][:200]}\n"
                f"    C     : {right_lines[index][:200]}"
            )
    if len(left_lines) != len(right_lines):
        return f"{len(left_lines)} lines from python, {len(right_lines)} from C"
    return None


def report(check: Check) -> Check:
    """Print one verdict as it is decided, in the C program's own format."""
    mark = "PASS" if check.ok else "FAIL"
    print(f"[{mark}] {check.name:<13} {check.detail}", flush=True)
    return check


def failure_detail(completed: subprocess.CompletedProcess[str]) -> str:
    """What to show when a mode exits nonzero: its own words, then the code."""
    for stream in (completed.stdout, completed.stderr):
        lines = [line for line in stream.splitlines() if line.strip()]
        if lines:
            return f"exit {completed.returncode}: {lines[-1]}"
    return f"exit {completed.returncode}, no output"


def check_perft(binary: Path, depth: int) -> Check:
    """Node counts against the published table compiled into the C file.

    The oracle here is external — the Chess Programming Wiki's numbers, cross
    checked by many engines over many years — so this is the one check that can
    catch both implementations being wrong together.
    """
    completed = run([str(binary), "--perft-suite", "--max-depth", str(depth)])
    if completed.returncode != 0:
        return Check("perft", False, failure_detail(completed))
    return Check("perft", True, last_line(completed))


def check_rule_cases(binary: Path) -> Check:
    """Hand-written positions, each pinning one Law by article number."""
    completed = run([str(binary), "--rule-cases"])
    if completed.returncode != 0:
        return Check("rule cases", False, failure_detail(completed))
    return Check("rule cases", True, last_line(completed))


def check_material(binary: Path) -> Check:
    """The Art. 5.2.2 material test, compared with python-chess over its whole domain.

    This is the one part of the ending rules the other checks cannot reach. The
    reference game ends in checkmate with a queen on the board, so the material
    test never fires anywhere in it: a disagreement here would sit behind a
    byte-identical trace and a byte-identical legal-move dump, unnoticed. It
    did. Before the same-colour bishop clause was written, the two decided ten
    of these inventories differently — every one of them bishops-only with two
    or more bishops all on one colour — while every other check passed.

    The predicate reads nothing but the inventory, so its domain is finite and
    the comparison is exhaustive rather than sampled. What it establishes is
    that two implementations of one approximation agree; the approximation
    itself is not a decision procedure for a dead position, which is the
    subject of docs/verification.md.
    """
    completed = run([str(binary), "--material-scan"])
    if completed.returncode != 0:
        return Check("material", False, failure_detail(completed))

    compared = 0
    disagreements = []
    for line in completed.stdout.splitlines():
        if not line or line.startswith("material-scan:"):
            continue
        fen, verdict = line.split("\t")
        theirs = chess.Board(fen).is_insufficient_material()
        compared += 1
        if (verdict == "dead") != theirs:
            disagreements.append(
                f"{fen}: C says {verdict}, "
                f"python-chess says {'dead' if theirs else 'alive'}"
            )

    if not compared:
        return Check("material", False, "--material-scan produced no verdicts")
    if disagreements:
        detail = f"{len(disagreements)} of {compared} differ; first: {disagreements[0]}"
        return Check("material", False, detail)
    detail = f"{compared} inventories, all agree with python-chess"
    return Check("material", True, detail)


def check_corpus(binary: Path, positions: int, seed: int) -> Check:
    """[H1] [H2] [H5] [H6] re-checked over a walk this program makes itself.

    The same four obligations are checked on the python side by
    `long_chess.bound.invariant`. Passing there leaves python-chess inside the
    trusted base of Lemma 4.5; passing here does not.
    """
    completed = run([str(binary), "--corpus", str(positions), "--seed", str(seed)])
    if completed.returncode != 0:
        return Check("corpus", False, failure_detail(completed))
    return Check("corpus", True, last_line(completed))


def check_replay(binary: Path, pgn: Path, name: str, extra: list[str]) -> Check:
    """Replay a game under the C checker's own reading of the ending rules."""
    completed = run(
        [
            str(binary),
            str(pgn),
            "--expect-plies",
            str(EXPECTED_PLIES),
            "--expect-termination",
            EXPECTED_TERMINATION,
            *extra,
        ]
    )
    if completed.returncode != 0:
        return Check(name, False, failure_detail(completed))
    detail = (
        f"{field(completed, 'plies')} plies, "
        f"{field(completed, 'termination')}, "
        f"{field(completed, 'critical segments')} critical segments"
    )
    return Check(name, True, detail)


def python_trace(work: Path) -> tuple[Path, str]:
    """The verifier's per-ply trace to compare against, and where it came from.

    `data/longest.trace.tsv` is gitignored — it is 1.5 MB of derived data — so a
    fresh checkout has to regenerate it. Regenerating is also the stronger
    check: it compares the C against what python-chess says *now*, not against a
    file that happened to be lying around.
    """
    if STORED_TRACE.exists():
        return STORED_TRACE, f"data/{STORED_TRACE.name}"
    target = work / "python.trace.tsv"
    completed = run(
        [
            sys.executable,
            "-m",
            "long_chess.verifier",
            str(WITNESS),
            "--trace",
            str(target),
        ]
    )
    if completed.returncode != 0 or not target.exists():
        raise RuntimeError(failure_detail(completed))
    return target, "a fresh verifier run"


def check_trace(work: Path, c_trace: Path) -> Check:
    """The two verdict streams, ply by ply, compared as text.

    Each row carries the FEN, the move, whether the ply was critical, the
    halfmove clock, the repetition count and the termination verdict. Agreement
    row by row is agreement about the ending rules, not only about legality.
    """
    try:
        reference, origin = python_trace(work)
    except RuntimeError as error:
        return Check("trace", False, f"python trace unavailable: {error}")
    difference = first_difference(reference, c_trace)
    if difference is not None:
        return Check("trace", False, difference)
    rows = len(reference.read_text(encoding="utf-8").splitlines()) - 1
    return Check("trace", True, f"{rows} rows identical to {origin}")


def check_legal_moves(work: Path, c_moves: Path) -> Check:
    """Every legal move at every position of the game, from both generators.

    Replaying agrees only about the moves that were played. The moves that were
    not played are where a generator's disagreements live, and this compares all
    of them at every position of the game.
    """
    reference = work / "python.moves"
    completed = run(
        [sys.executable, str(DUMP_SCRIPT), str(WITNESS), "-o", str(reference)]
    )
    if completed.returncode != 0 or not reference.exists():
        return Check("legal moves", False, failure_detail(completed))
    difference = first_difference(reference, c_moves)
    if difference is not None:
        return Check("legal moves", False, difference)
    lines = reference.read_text(encoding="utf-8").splitlines()
    total = sum(len(line.split("\t")[1].split()) for line in lines)
    return Check(
        "legal moves", True, f"{len(lines)} positions, {total} moves, all identical"
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="check_movegen")
    parser.add_argument(
        "--cc",
        help="compiler to build with; without it, $CC then cc, gcc, clang",
    )
    parser.add_argument(
        "--max-depth",
        type=int,
        help="deepest perft depth to run (default 5, or 6 with --deep)",
    )
    parser.add_argument(
        "--deep",
        action="store_true",
        help="perft to depth 6 and a ten times larger corpus (~30 s)",
    )
    parser.add_argument(
        "--corpus-positions",
        type=int,
        help="positions for the obligation walk (default 20000)",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=1,
        help="seed for the corpus walk; the run prints the one it used",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    depth = args.max_depth if args.max_depth is not None else (6 if args.deep else 5)
    positions = args.corpus_positions
    if positions is None:
        positions = 200_000 if args.deep else 20_000

    if not SOURCE.exists():
        print(f"FAIL: {SOURCE} is missing", file=sys.stderr)
        return 1

    compiler = find_compiler(args.cc)
    if compiler is None:
        if args.cc is not None:
            print(f"FAIL: {args.cc} was asked for and is not on PATH", file=sys.stderr)
            return 1
        print("no C compiler found (looked for $CC, then cc, gcc, clang)")
        print("SKIP: the second move generator was not built or run")
        return 0

    started = time.perf_counter()
    with tempfile.TemporaryDirectory() as scratch:
        work = Path(scratch)
        binary = work / "longest_check"

        built = run([compiler, *CFLAGS, "-o", str(binary), str(SOURCE)])
        if built.returncode != 0:
            print(built.stdout)
            print(built.stderr, file=sys.stderr)
            print("FAIL: the checker did not build", file=sys.stderr)
            return 1
        print(f"compiler      {compiler_version(compiler)}")
        print(f"flags         {' '.join(CFLAGS)}")
        print(f"build         {SOURCE.relative_to(REPO)} -> clean, no warnings")
        print()

        checks = [
            report(check_perft(binary, depth)),
            report(check_rule_cases(binary)),
            report(check_material(binary)),
        ]

        c_trace = work / "c.trace.tsv"
        c_moves = work / "c.moves"
        witness = check_replay(
            binary,
            WITNESS,
            "witness",
            ["--trace", str(c_trace), "--dump-moves", str(c_moves)],
        )
        checks.append(report(witness))
        if witness.ok:
            checks.append(report(check_trace(work, c_trace)))
            checks.append(report(check_legal_moves(work, c_moves)))
        else:
            # Without a replay there is nothing to compare, and reporting two
            # further failures would triple-count one defect.
            print("[skip] trace         the replay produced no trace")
            print("[skip] legal moves   the replay produced no move dump")

        checks.append(report(check_corpus(binary, positions, args.seed)))

    failed = [check for check in checks if not check.ok]
    elapsed = time.perf_counter() - started
    print()
    print(
        f"check_movegen: {len(checks)} checks, {len(checks) - len(failed)} passed, "
        f"{len(failed)} failed  ({elapsed:.1f} s)"
    )
    if failed:
        sys.stdout.flush()
        print("FAIL: the independent checker did not pass every check", file=sys.stderr)
        for check in failed:
            print(f"  {check.name}: {check.detail}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
