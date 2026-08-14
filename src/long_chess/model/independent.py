"""The same question, decided by arithmetic instead of a solver.

A CP-SAT UNSAT is only as trustworthy as the encoding that produced it, and an
encoding bug looks exactly like a proof. So this decides the same question by a
different route: no solver, and an argument short enough to read.

**What it does and does not share.** It reads a :class:`~.shape.Shape` — the
problem statement has to be the same one or the comparison is meaningless — and
nothing else. A shape is the block sequence of the game's `K` segment
**endpoints**, mate included, which is the convention that makes reading
``colours[-1]`` as the mating side sound here too; see the rubric in
:mod:`.abstract`. Every constant below is declared here, as a literal, with a
pointer to where it is proved; nothing is imported from :mod:`long_chess.bound`
and nothing from the rest of :mod:`long_chess.model` beyond the shape and the
ending names, which live in :mod:`.shape` precisely so that this module can be
imported — and tested — without ortools installed. That makes this an
**independent arithmetic cross-check**, not a second proof: it shares the
vocabulary and the numbers, and disagreement is what it is for.
``tests/test_independent.py`` pins these literals against the canonical
definitions so the two cannot drift apart silently.

The reasoning. `K = (P − Cₚ) + (C + T) ≤ 88 + 30 = 118`, and reaching 118 needs
every term at its extreme — in particular all 96 pawn moves. The only question
is therefore **how many pawn moves a block shape permits**, and that has a
closed form.

Fix a pawn. It may move only in blocks of its own colour, at most six times,
and — before it is captured — only in blocks strictly earlier than the one it
dies in. In the very first block it is additionally capped at four, by the
home-rank lemma, unless an enemy pawn has been captured there to open a way
through. So its ceiling is a sum over the blocks still available to it.

Then count who must die. Under a checkmate the mating side keeps at least one
non-king unit, because a lone king cannot mate — that is the whole of what
checkmate imposes, and the mated side may keep most of its army. Under a draw
even that goes, and the counts are free up to the ceiling. (This paragraph used
to say the mated side loses all fifteen and the mating side fourteen. That is
what `K = 118` forces, not what checkmate forces, and the code enforced it until
Scholar's mate was fed to it — see
``tests/test_defects.py::TestCheckmateBranchWasNotAModel``.)

And a colour with no enemy block keeps all fifteen of its units: a capture of
one would be an enemy critical move, and there is no block to hold it. The CP
model imposes this structurally — a captured unit needs a death block of the
enemy colour — and this checker used to be looser, counting captures the shape
cannot contain. That inflated the reported maxima for the single-block shapes
(they read 71; the ceiling with the condition imposed is 64) without touching
any feasibility verdict, since 71 and 64 are both far from 118.

Pawns are interchangeable, so maximising the
total is a matter of choosing how many pawns each side loses and when — a
handful of cases, enumerated below.
"""

from __future__ import annotations

from dataclasses import dataclass

from .shape import CHECKMATE, DRAW, ENDINGS, Shape

# --- constants, declared here on purpose -----------------------------------
# Each is a literal rather than an import, so that a change to the canonical
# derivation shows up as a *disagreement* between the two methods instead of
# propagating silently into both. Where each is proved:
#
#   PAWN_STEPS, PAWNS_PER_SIDE   long_chess.bound.pawns
#   FIRST_BLOCK_LIMIT            long_chess.bound.invariant (the home-rank lemma)
#   UNRESOLVED_PAIR / RESOLVED_PAIR
#                                long_chess.bound.pawns.check_origin_pair_cap
#   CAPTURE_CEILING              long_chess.bound.pawns.ending_profiles

PAWN_STEPS = 6
PAWNS_PER_SIDE = 8
NON_PAWNS_PER_SIDE = 7
CAPTURABLE_PER_SIDE = PAWNS_PER_SIDE + NON_PAWNS_PER_SIDE
FILES = 8
MAX_PAWN_MOVES = 2 * PAWNS_PER_SIDE * PAWN_STEPS

FIRST_BLOCK_LIMIT = 4
"""A pawn's moves in the opening block while the enemy home rank is intact."""

UNRESOLVED_PAIR = 10
"""Combined moves of the two pawns starting on one file, neither of which ever
moves diagonally: four while both are on the file, then six for whichever one
outlives the other."""

RESOLVED_PAIR = 12
"""The same when one of them does move diagonally: six each, and nothing else
binds."""

CAPTURE_CEILING = {CHECKMATE: 29, DRAW: 30}
"""A checkmate leaves the mating side something to mate with; a draw need not.
Taking the thirtieth ends the game on the spot, which the closing segment below
accounts for."""


def _other(colour: str) -> str:
    return "B" if colour == "W" else "W"


def _blocks_of(colours: tuple[str, ...], colour: str) -> list[int]:
    return [index for index, c in enumerate(colours) if c == colour]


def _block_capacity(
    colours: tuple[str, ...], colour: str, block: int, opened: bool
) -> int:
    """Moves one pawn of ``colour`` may make in ``block``.

    Six, except in the first block of the game when the pawn belongs to the
    colour that moves there — then four, unless the enemy home rank has been
    opened by capturing a pawn out of it.
    """
    if block == 0 and colour == colours[0] and not opened:
        return FIRST_BLOCK_LIMIT
    return PAWN_STEPS


def _ceiling(
    colours: tuple[str, ...], colour: str, death: int | None, opened: bool
) -> int:
    """Most moves a pawn of ``colour`` can make if captured in block ``death``.

    ``None`` means it survives. Blocks at or after ``death`` are unusable: a
    piece makes its moves before it is taken.
    """
    usable = [
        block
        for block in _blocks_of(colours, colour)
        if death is None or block < death
    ]
    return min(
        PAWN_STEPS,
        sum(_block_capacity(colours, colour, block, opened) for block in usable),
    )


def _best_if_captured(colours: tuple[str, ...], colour: str, opened: bool) -> int:
    """How many moves the kindest block to die in allows."""
    deaths = _blocks_of(colours, _other(colour))
    if not deaths:
        return 0
    return max(_ceiling(colours, colour, death, opened) for death in deaths)


def _colour_total(
    colours: tuple[str, ...],
    colour: str,
    pawns_lost: int,
    opened: bool,
    opener: str,
) -> int:
    """Most pawn moves ``colour`` can make with ``pawns_lost`` of them captured."""
    per_captured = _best_if_captured(colours, colour, opened)
    per_survivor = _ceiling(colours, colour, None, opened)
    total = pawns_lost * per_captured + (PAWNS_PER_SIDE - pawns_lost) * per_survivor
    if opened and colour == opener:
        # One of them dies in the opening block instead, with no earlier block
        # of its own to have moved in, so it contributes nothing.
        total -= per_captured
    return total


def pawn_ceiling(resolved: int) -> int:
    """``P ≤ min(96, 80 + 2f)`` — the origin-pair caps, summed over eight files."""
    return min(
        MAX_PAWN_MOVES,
        UNRESOLVED_PAIR * (FILES - resolved) + RESOLVED_PAIR * resolved,
    )


@dataclass(frozen=True, slots=True)
class IndependentResult:
    shape: Shape
    max_pawn_moves: int
    max_k: int
    feasible: bool
    account: str
    """How the maximum was reached, in words."""


def analyse(
    shape: Shape, *, ending: str = CHECKMATE, target_k: int = 118
) -> IndependentResult:
    """Decide whether ``K = target_k`` fits this shape, without a solver.

    ``ending`` matters because it changes two things at once. A checkmate needs
    the mating side to keep a piece, so at most 29 captures — but it keeps the
    closing segment the mate sits in. A draw may take all 30, and the thirtieth
    leaves king against king, which is dead and ends the game where it stands,
    giving that closing segment up. The trade is exactly even.
    """
    if ending not in ENDINGS:
        raise ValueError(f"ending must be one of {ENDINGS}, got {ending!r}")

    colours = shape.colours
    opener = _other(colours[0])
    ceiling = CAPTURE_CEILING[ending]
    all_captured = CAPTURE_CEILING[DRAW]

    best_k = -1
    best_moves = 0
    best_account = "no assignment satisfies the constraints"

    for opened in (False, True):
        for lost_w in range(PAWNS_PER_SIDE + 1):
            for lost_b in range(PAWNS_PER_SIDE + 1):
                pawns_lost = {"W": lost_w, "B": lost_b}
                if opened and pawns_lost[opener] == 0:
                    continue
                for extra_w in range(NON_PAWNS_PER_SIDE + 1):
                    for extra_b in range(NON_PAWNS_PER_SIDE + 1):
                        captures = lost_w + lost_b + extra_w + extra_b
                        if captures > ceiling:
                            continue
                        # A unit is captured by a critical move of the other
                        # colour, so a colour with no enemy block loses
                        # nothing. Without this the maxima for single-block
                        # shapes counted captures the shape cannot contain.
                        if any(
                            lost and not _blocks_of(colours, _other(colour))
                            for colour, lost in (
                                ("W", lost_w + extra_w),
                                ("B", lost_b + extra_b),
                            )
                        ):
                            continue

                        if ending == CHECKMATE:
                            # A lone king cannot mate, so the mating side keeps
                            # at least one non-king unit. That is all checkmate
                            # implies — the mated side may still have most of
                            # its army, as it does in Scholar's mate. Forcing it
                            # to lose all fifteen, and forcing a quiet mate, was
                            # reading `K = 118`'s consequences as checkmate's
                            # definition.
                            #
                            # The last block is the mater only because shapes
                            # are endpoint sequences — see `.abstract`.
                            mating = colours[-1]
                            lost = {"W": (lost_w, extra_w), "B": (lost_b, extra_b)}
                            if sum(lost[mating]) > CAPTURABLE_PER_SIDE - 1:
                                continue
                            closing_options = (0, 1)
                        else:
                            # King against king is dead: no closing segment.
                            closing_options = (
                                (0,) if captures == all_captured else (0, 1)
                            )

                        moves = sum(
                            _colour_total(
                                colours, colour, pawns_lost[colour], opened, opener
                            )
                            for colour in ("W", "B")
                        )

                        for closing in closing_options:
                            for resolved in range(FILES + 1):
                                fits = min(moves, pawn_ceiling(resolved))
                                # A pawn capture is a pawn move and a capture, so
                                # the `resolved` pawn_captures this f demands have to
                                # fit inside both totals.
                                if resolved > fits or resolved > captures:
                                    continue
                                k = fits + captures - resolved + closing
                                if k > best_k:
                                    best_k = k
                                    best_moves = fits
                                    best_account = (
                                        f"{ending}, opened={opened}, "
                                        f"pawns lost W{lost_w}/B{lost_b}, "
                                        f"{captures} captures, closing={closing}, "
                                        f"{resolved} files resolved, "
                                        f"{fits} pawn moves"
                                    )

    return IndependentResult(
        shape=shape,
        max_pawn_moves=best_moves,
        max_k=max(best_k, 0),
        feasible=best_k >= target_k,
        account=best_account,
    )
