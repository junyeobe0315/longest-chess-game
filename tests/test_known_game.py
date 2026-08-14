"""The verifier gate: the known 17,697-ply game must pass this verifier end to end.

The reference PGN is ``data/longest.pgn`` from https://tom7.org/chess/longest.pgn
(SIGBOVIK 2020). Note it is *not* checked into Tom 7's repository -- the program
there writes it out -- so this file is the artefact, downloaded over plain HTTP
and pinned by hash below. That is acceptable only because nothing here trusts
it: a tampered game that is illegal fails verification, and one that is shorter
fails the ply count.
"""

from __future__ import annotations

import hashlib
from collections import Counter
from pathlib import Path

import chess
import pytest

from long_chess.verifier import (
    SEVENTYFIVE_MOVE_PLY_LIMIT,
    Termination,
    moves_from_pgn,
    verify_game,
)

REFERENCE_PGN = Path(__file__).parent.parent / "data" / "longest.pgn"
REFERENCE_SHA256 = "6700b7b70260c9b4448d58c610601cab938dd0e01392bd876d3379630de680bb"

EXPECTED_PLIES = 17_697
EXPECTED_CRITICAL_SEGMENTS = 118

pytestmark = pytest.mark.skipif(
    not REFERENCE_PGN.exists(),
    reason="reference PGN missing; run scripts/fetch_reference.py",
)


@pytest.fixture(scope="module")
def result():
    return verify_game(moves_from_pgn(REFERENCE_PGN), trace=True)


def test_reference_file_is_the_expected_one():
    digest = hashlib.sha256(REFERENCE_PGN.read_bytes()).hexdigest()
    assert digest == REFERENCE_SHA256


def test_every_move_is_legal_and_the_game_runs_to_the_end(result):
    """verify_game raises on an illegal move or an early termination, so
    reaching here at all is most of the assertion."""
    assert result.plies == EXPECTED_PLIES


def test_the_game_ends_in_checkmate_not_a_draw(result):
    assert result.termination is Termination.CHECKMATE


def test_the_last_move_is_both_the_150th_quiet_move_and_mate(result):
    """The whole game hinges on this priority. If the clock check came first
    this would be a draw and the game one ply shorter."""
    last = result.trace[-1]
    assert last.ply == EXPECTED_PLIES
    assert last.halfmove_clock == SEVENTYFIVE_MOVE_PLY_LIMIT
    assert last.termination == Termination.CHECKMATE.value
    assert not last.critical, "the mating move is neither a pawn move nor a capture"


def test_critical_segment_count(result):
    assert result.critical_count == EXPECTED_CRITICAL_SEGMENTS


def test_no_automatic_termination_fires_before_the_end(result):
    early = [
        r for r in result.trace[:-1] if r.termination != Termination.CONTINUE.value
    ]
    assert early == []


def test_the_clock_never_reaches_the_limit_before_the_end(result):
    over = [
        r for r in result.trace[:-1] if r.halfmove_clock >= SEVENTYFIVE_MOVE_PLY_LIMIT
    ]
    assert over == [], f"{len(over)} ply reached the 75-move limit early"


def test_no_position_occurs_five_times(result):
    over = [r for r in result.trace if r.repetitions >= 5]
    assert over == [], f"{len(over)} position(s) repeated five times"


def test_the_maximum_position_multiplicity_is_exactly_two(result):
    """More is pinned than "fivefold never fires": no position of the game
    occurs even three times, the maximum multiplicity being exactly two.

    Nothing about the bound needs it — any value below five would do — but it
    is a measured property of the witness, so it gets pinned, and equality
    rather than an inequality: a construction that started repeating positions
    three times over would still pass every other check here.
    """
    assert max(record.repetitions for record in result.trace) == 2


def test_the_multiplicity_survives_an_independent_recount(result):
    """The column above is the verifier's own table, incremented as it plays.

    Recounted from scratch off the traced FENs — Article 9.2's four data as
    text, sharing no code with ``repetition_key`` or with the running counter,
    though both still go through python-chess's rendering of the castling and
    en-passant fields — the whole column has to come back identical.
    """
    counts: Counter[str] = Counter()
    recount = []
    for record in result.trace:
        placement, turn, castling, en_passant = record.fen.split()[:4]
        key = f"{placement} {turn} {castling} {en_passant}"
        counts[key] += 1
        recount.append(counts[key])

    assert recount == [record.repetitions for record in result.trace]
    assert max(counts.values()) == 2


def segment_lengths_and_actors(result) -> tuple[list[int], list[str]]:
    boundaries = [0, *result.critical_plies]
    if boundaries[-1] != result.plies:
        boundaries.append(result.plies)  # the closing checkmate
    lengths = [b - a for a, b in zip(boundaries, boundaries[1:], strict=False)]
    # Odd ply numbers are White's.
    actors = ["W" if ply % 2 else "B" for ply in boundaries[1:]]
    return lengths, actors


def test_segments_never_exceed_150_ply(result):
    """L = 150K - S - Σδ assumes each segment is at most 150 ply."""
    lengths, _ = segment_lengths_and_actors(result)
    assert len(lengths) == EXPECTED_CRITICAL_SEGMENTS
    assert max(lengths) <= 150
    assert sum(lengths) == EXPECTED_PLIES


def test_the_length_identity_holds_exactly(result):
    """L = 150K - S - Σδ, with K=118, S=3, Σδ=0.

    This is the check that the verifier's notion of a critical move is the same
    one the theory is stated in. If ``is_critical`` were subtly wrong the
    identity would not close.
    """
    lengths, actors = segment_lengths_and_actors(result)

    previous = "B"  # as if Black made a critical move just before ply 1
    switches = 0
    slack = 0
    for length, actor in zip(lengths, actors, strict=True):
        switched = actor != previous
        switches += switched
        slack += (150 - switched) - length  # a switch costs exactly one ply
        previous = actor

    assert len(lengths) == 118
    assert switches == 3
    assert slack == 0, "the known game fills every segment to its target"
    assert 150 * len(lengths) - switches - slack == result.plies


def test_the_three_lost_plies_are_exactly_the_three_actor_switches(result):
    """Which segments any rescheduling attempt has to attack.

    Nothing is wasted anywhere else: the only ply the known construction gives
    up is one per phase boundary. So 17,697 -> 17,698 means removing a boundary,
    not packing a segment better.
    """
    lengths, actors = segment_lengths_and_actors(result)

    short = [i for i, length in enumerate(lengths) if length == 149]
    pairs = zip(actors, ["B", *actors], strict=False)
    switched = [i for i, (actor, previous) in enumerate(pairs) if actor != previous]
    assert short == switched == [10, 59, 109]


def test_the_critical_phases_are_black_white_black_white(result):
    _, actors = segment_lengths_and_actors(result)
    phases = []
    for actor in actors:
        if not phases or phases[-1][0] != actor:
            phases.append([actor, 0])
        phases[-1][1] += 1
    assert [p[0] for p in phases] == ["B", "W", "B", "W"]
    assert [p[1] for p in phases] == [10, 49, 50, 9]


def test_a_tail_of_the_game_still_reaches_mate(published_moves):
    """The dead-position argument, spot-checked: from any prefix position the
    rest of the game is a legal series reaching mate (FIDE 5.2.2), so no
    position in a mating game is dead. Two cuts stand in for all of them; the
    full-depth replay is the verification above."""
    for cut in (17_000, len(published_moves) - 1):
        board = chess.Board()
        for move in published_moves[:cut]:
            board.push(move)
        tail = verify_game(published_moves[cut:], board)
        assert tail.termination is Termination.CHECKMATE
