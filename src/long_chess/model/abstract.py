"""The abstract model: can a given K be scheduled into a given block shape?

Deliberately a **relaxation**. It knows nothing about squares, reachability,
whether a capture is physically available, or whether the quiet bridges between
events exist. Every legal game maps to a solution, so UNSAT here means no legal
game — while SAT means only that nothing in this model rules one out.

Under-constraining is the safe direction and the only safe direction. A
constraint stronger than legality produces UNSAT, and UNSAT is indistinguishable
from a proof.

This is a **cross-check, not the proof.** `long_chess.bound.blocks` settles
`S ≥ 3` by counting, with no solver; run it via scripts/analyse_bound.py.

.. rubric:: Which sequence the shapes are shapes of

A :class:`Shape` is the block sequence of a game's `K` **segment endpoints** —
its critical moves plus, when quiet moves follow the last of them, the terminal
endpoint that closes the game: a quiet mate, or the ply that runs out the
75-move or repetition clock. It is the same sequence `S` is measured over in
:mod:`long_chess.bound.blocks`, where
``check_dropping_terminal_endpoint_never_adds_a_switch`` is the seam between
statements about it and statements about critical moves alone.

The convention is load-bearing, not cosmetic. The checkmate branch below reads
``colours[-1]`` as the mating side, and over endpoint sequences that is a fact:
the mate is the game's last endpoint — the last critical move when it captures
or pushes a pawn, the terminal quiet endpoint otherwise — and it is made by the
mating side. Over critical moves alone it is **false**: a quiet mate can be
delivered by the colour that made no critical move last. Black can take all
fifteen White units, the bare White king can take one Black pawn, and Black can
then mate the lone king quietly — critical actors `(B, W)`, mate by Black. Read
that way, the branch would reject a legal game, which is the one failure this
model must not have; read over endpoints, the game's shape is `(B, W, B)` and
the branch is sound. The game exists and both readings are pinned in
``tests/test_defects.py::TestMatingSideIsTheLastEndpoint``.

.. rubric:: A scope error that was here

The checkmate branch used to force the mated side to lose all fifteen of its
capturable units. That is not what checkmate implies — Scholar's mate ends with
Black's army almost untouched — it is what `K = 118` implies, via `C = 29` and
`T = 1`. Asserting it made the model reject legal games at any other `K`, so
the documented claim "every legal game maps to a solution" was false outside
`K = 118`. It has been weakened to the general fact: a lone king cannot mate,
so the mating side keeps at least one non-king unit.

The verdicts at `K = 118` were unaffected — the dropped constraint is derivable
there — but the maxima reported for lower `K` were conditional on a constraint
that does not hold, and are now genuine.

See docs/abstract-model.md for the variable list and the constraint audit.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ortools.sat.python import cp_model

from ..bound.pawns import (
    FILES,
    FIRST_BLOCK_PAWN_LIMIT,
    MAX_CAPTURES,
    MAX_CAPTURES_DRAW,
    MAX_CRITICAL_SEGMENTS,
    MAX_PAWN_MOVES,
    PAWN_STEPS,
    RESOLVED_ORIGIN_PAIR_MOVE_CAP,
    UNRESOLVED_ORIGIN_PAIR_MOVE_CAP,
)
from .shape import CHECKMATE, Shape, require_ending

PAWNS_PER_SIDE = 8
NON_PAWNS_PER_SIDE = 7
CAPTURABLE_PER_SIDE = PAWNS_PER_SIDE + NON_PAWNS_PER_SIDE
TARGET_K = MAX_CRITICAL_SEGMENTS


class Inconclusive(RuntimeError):
    """The solver neither proved nor refuted feasibility.

    Raised rather than returned. A timeout is not a proof, and the whole result
    rests on INFEASIBLE meaning "no legal game" — quietly reporting UNKNOWN as
    infeasible would turn "the solver gave up" into "no such game exists",
    which is the one failure mode this project cannot afford to have silent.
    """


@dataclass
class Solution:
    feasible: bool
    status: str
    pawn_moves: int = 0
    captures: int = 0
    pawn_captures: int = 0
    closing_segment: int = 0
    """Whether there were quiet moves after the last critical one.

    One for a quiet checkmate, one for the moves that run out the 75-move or
    repetition clock, zero when the last critical move ended the game — which a
    draw taking all thirty pieces always does.
    """
    moves_by_pawn: dict[str, list[int]] = field(default_factory=dict)

    @property
    def k(self) -> int:
        return (
            self.pawn_moves
            + self.captures
            - self.pawn_captures
            + self.closing_segment
        )


@dataclass
class Handles:
    """The model's variables, so callers can pin or read them."""

    moves: dict
    totals: dict
    captured: dict
    capture_block: dict
    pawn_moves: cp_model.IntVar
    total_captures: cp_model.IntVar
    pawn_captures: cp_model.IntVar
    closing_segment: cp_model.IntVar


def build(
    shape: Shape,
    *,
    target_k: int = TARGET_K,
    home_rank_limit: bool = True,
    pawn_capture_floor: int | None = None,
    ending: str = CHECKMATE,
) -> tuple[cp_model.CpModel, Handles]:
    """The model for one block shape, unsolved.

    ``home_rank_limit`` exists to be turned off. Switching it off should make
    the S ≤ 2 shapes feasible again — if they stay infeasible without it, the
    UNSAT is coming from somewhere else and that somewhere else needs auditing.
    """
    require_ending(ending)
    model = cp_model.CpModel()

    # --- pawn moves -------------------------------------------------------
    # Each pawn makes at most six moves, all of them in blocks of its colour.
    # Equivalence: a pawn crosses six ranks, and a double push covers two of
    # them in one move, so six moves is the ceiling and needs single pushes.
    moves: dict[tuple[str, int], dict[int, cp_model.IntVar]] = {}
    totals: dict[tuple[str, int], cp_model.IntVar] = {}
    for colour in ("W", "B"):
        for index in range(PAWNS_PER_SIDE):
            per_block = {
                block: model.new_int_var(0, PAWN_STEPS, f"mv_{colour}{index}_{block}")
                for block in shape.blocks_of(colour)
            }
            total = model.new_int_var(0, PAWN_STEPS, f"mv_{colour}{index}")
            model.add(total == sum(per_block.values()))
            moves[colour, index] = per_block
            totals[colour, index] = total

    pawn_moves = model.new_int_var(0, MAX_PAWN_MOVES, "pawn_moves")
    model.add(pawn_moves == sum(totals.values()))

    # --- captures ---------------------------------------------------------
    # A capture of a piece is an event of the *other* colour: only the opponent
    # can take it. That is the observation the whole reduction rests on, and it
    # makes the capturing block's colour forced rather than chosen.
    captured: dict[tuple[str, str, int], cp_model.IntVar] = {}
    capture_block: dict[tuple[str, str, int], dict[int, cp_model.IntVar]] = {}

    for colour in ("W", "B"):
        enemy_blocks = shape.blocks_of("B" if colour == "W" else "W")
        for kind, count in (("P", PAWNS_PER_SIDE), ("N", NON_PAWNS_PER_SIDE)):
            for index in range(count):
                key = (colour, kind, index)
                is_captured = model.new_bool_var(f"cap_{colour}{kind}{index}")
                where = {
                    block: model.new_bool_var(f"capat_{colour}{kind}{index}_{block}")
                    for block in enemy_blocks
                }
                model.add(sum(where.values()) == 1).only_enforce_if(is_captured)
                model.add(sum(where.values()) == 0).only_enforce_if(~is_captured)
                captured[key] = is_captured
                capture_block[key] = where

                # A piece makes its own moves before it is taken. For a pawn
                # that means every block in which it moves comes at or before
                # the block it dies in.
                if kind == "P":
                    for own_block, moved in moves[colour, index].items():
                        for dead_block, here in where.items():
                            if dead_block < own_block:
                                model.add(moved == 0).only_enforce_if(here)

    ceiling = MAX_CAPTURES if ending == CHECKMATE else MAX_CAPTURES_DRAW
    total_captures = model.new_int_var(0, ceiling, "captures")
    model.add(total_captures == sum(captured.values()))

    # `closing` is the segment after the last critical move — the one holding a
    # quiet mate, or the quiet moves that run out the 75-move or repetition
    # clock. It is worth one more segment when it exists.
    closing = model.new_int_var(0, 1, "closing_segment")

    if ending == CHECKMATE:
        # A lone king cannot give mate, so the mating side keeps at least one
        # non-king unit. That is *all* a checkmate implies in general.
        #
        # `shape.mating_colour` is the last block because shapes are sequences
        # of segment *endpoints* and the mate is the last endpoint. Over
        # critical moves alone the attribution would be false — a quiet mate
        # can come from the colour that made no critical move last — and this
        # constraint would reject a legal game. Both readings are pinned in
        # `tests/test_defects.py::TestMatingSideIsTheLastEndpoint`.
        #
        # This used to also force the mated side to lose all fifteen of its
        # capturable units. That is not a property of checkmate — Scholar's
        # mate ends with Black's army almost intact — it is a consequence of
        # `K = 118`, which pins `C = 29` and `T = 1`, leaving exactly one
        # non-king unit on the board for the mating side to mate with. Asserting
        # it here made the model reject legal games, so it was **stronger than
        # legality** in a model whose whole value is being weaker. Pinned as a
        # regression in `tests/test_defects.py::TestCheckmateBranchWasNotAModel`.
        model.add(
            sum(
                value
                for (colour, _, _), value in captured.items()
                if colour == shape.mating_colour
            )
            <= CAPTURABLE_PER_SIDE - 1
        )
    else:
        # A draw needs no mating material, so every non-king piece may go — but
        # the thirtieth capture leaves king against king, which is dead and ends
        # the game where it stands. No closing segment in that case.
        everything = model.new_bool_var("everything_captured")
        model.add(total_captures == MAX_CAPTURES_DRAW).only_enforce_if(everything)
        model.add(total_captures <= MAX_CAPTURES_DRAW - 1).only_enforce_if(~everything)
        model.add(closing == 0).only_enforce_if(everything)

    # --- the home-rank lemma ----------------------------------------------
    # Before the enemy has moved a pawn, every square of its home rank holds
    # one, and a pawn arriving there can neither push through nor step aside.
    # So in the very first block a pawn stops four moves short of promoting —
    # *unless* a way through has been opened, and the only way to open one is
    # to capture an enemy pawn on that rank.
    #
    # Making the limit conditional matters. Applied unconditionally it would be
    # stronger than legality, and a constraint stronger than legality produces
    # UNSAT that looks exactly like a proof. The trade it allows is real but
    # ruinous: a pawn captured before it moves gives up all six of its moves,
    # and the K identity below charges for that.
    #
    # Later blocks of the same colour are left unconstrained. Not because the
    # enemy's pawns must have moved by then — its block may have been captures
    # alone, leaving its home rank exactly where it started — but because
    # omitting a constraint only loosens a relaxation, and loose is the safe
    # direction here.
    first_colour = shape.colours[0]
    enemy_of_first = "B" if first_colour == "W" else "W"
    opened = model.new_bool_var("home_rank_opened")
    # Block 0 belongs to the first colour, so the enemy of the first colour
    # can die in it: every one of its eight pawns carries a block-0 death
    # variable, and `breaches` always has eight entries. Indexing without a
    # guard keeps that structural — if the invariant ever broke this would
    # raise, rather than silently modelling the rank as never opened. (A dead
    # `else opened == 0` arm used to sit here for the impossible empty case.)
    breaches = [
        capture_block[enemy_of_first, "P", index][0]
        for index in range(PAWNS_PER_SIDE)
    ]
    model.add_max_equality(opened, breaches)

    if home_rank_limit:
        for index in range(PAWNS_PER_SIDE):
            per_block = moves[first_colour, index]
            if 0 in per_block:
                model.add(per_block[0] <= FIRST_BLOCK_PAWN_LIMIT).only_enforce_if(
                    ~opened
                )

    # --- the K identity ---------------------------------------------------
    # Pawn captures are not a free axiom. The two pawns that start on file i are its
    # *origin pair*, and the file is resolved when one of those two itself makes
    # a diagonal pawn move — which is the only way a pawn changes file, and is
    # therefore a capture, and therefore a pawn capture. An unresolved pair is
    # capped at ten combined moves and a resolved one at twelve, so with
    # `resolved` files resolved:
    #
    #     pawn moves ≤ 10·(8 − resolved) + 12·resolved = 80 + 2·resolved
    #     pawn_captures   ≥ resolved
    #
    # Coupling them is what forces all eight files to be resolved when K = 118,
    # rather than asserting `pawn_captures ≥ 8` outright. Asserting it was wrong in
    # the permissive direction: a shape that cannot reach 96 pawn moves needs
    # fewer files resolved, so charging it eight pawn captures understates its K.
    #
    # The unresolved cap was 4 here until it was found to be false — a pawn
    # whose opposite number is captured by some other piece runs on alone. See
    # `bound.pawns.UNRESOLVED_ORIGIN_PAIR_MOVE_CAP` for the legal counterexample
    # and the exhaustive re-derivation of 10.
    resolved = model.new_int_var(0, FILES, "resolved_files")
    per_resolved = RESOLVED_ORIGIN_PAIR_MOVE_CAP - UNRESOLVED_ORIGIN_PAIR_MOVE_CAP
    model.add(
        pawn_moves
        <= UNRESOLVED_ORIGIN_PAIR_MOVE_CAP * FILES + per_resolved * resolved
    )
    pawn_captures = model.new_int_var(0, MAX_PAWN_MOVES, "pawn_captures")
    model.add(pawn_captures >= resolved)
    # A pawn capture is a pawn move *and* a capture, so it is bounded by both. Both
    # are implied by legality, so imposing them excludes no legal game — and
    # without them the solver could answer a low `target_k` with more pawn_captures
    # than pawn moves, which is permissive (safe) but makes the reported maxima
    # describe nothing.
    model.add(pawn_captures <= pawn_moves)
    model.add(pawn_captures <= total_captures)
    if pawn_capture_floor is not None:
        model.add(pawn_captures >= pawn_capture_floor)

    model.add(pawn_moves + total_captures - pawn_captures + closing == target_k)

    return model, Handles(
        moves=moves,
        totals=totals,
        captured=captured,
        capture_block=capture_block,
        pawn_moves=pawn_moves,
        total_captures=total_captures,
        pawn_captures=pawn_captures,
        closing_segment=closing,
    )


def solve(
    shape: Shape,
    *,
    target_k: int = TARGET_K,
    home_rank_limit: bool = True,
    pawn_capture_floor: int | None = None,
    ending: str = CHECKMATE,
    time_limit: float = 60.0,
) -> Solution:
    """Is there an assignment reaching ``target_k`` critical events in ``shape``?"""
    require_ending(ending)
    model, handles = build(
        shape,
        target_k=target_k,
        home_rank_limit=home_rank_limit,
        pawn_capture_floor=pawn_capture_floor,
        ending=ending,
    )

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    status = solver.solve(model)
    name = solver.status_name(status)

    if status == cp_model.INFEASIBLE:
        return Solution(feasible=False, status=name)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise Inconclusive(
            f"{shape} ({ending}): solver returned {name} after {time_limit}s. "
            "This is not a refutation; raise the time limit or simplify the "
            "model before drawing any conclusion."
        )

    return Solution(
        feasible=True,
        status=name,
        pawn_moves=solver.value(handles.pawn_moves),
        captures=solver.value(handles.total_captures),
        pawn_captures=solver.value(handles.pawn_captures),
        closing_segment=solver.value(handles.closing_segment),
        moves_by_pawn={
            f"{colour}{index}": [
                solver.value(var) for var in handles.moves[colour, index].values()
            ]
            for colour in ("W", "B")
            for index in range(PAWNS_PER_SIDE)
        },
    )


