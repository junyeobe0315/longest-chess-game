"""Does the abstract model accept games that actually exist?

The check that decides whether anything the model says is worth having. A model
that rejects the published 17,697-ply game is not a model of chess, and its
UNSAT results are artefacts of its own constraints.

Run it before believing any UNSAT, and again after any constraint is added. (No
CEGAR loop was ever built — the model returned no candidate to refine — so in
practice "any constraint added" has meant the ones added by hand.)
"""

from __future__ import annotations

from dataclasses import dataclass

import chess

from ..search import EventKind, extract_events, phases
from ..skeleton import Skeleton
from .abstract import PAWNS_PER_SIDE
from .shape import CHECKMATE, Shape

PAWN_KINDS = (EventKind.PAWN, EventKind.PROMOTION, EventKind.PAWN_CAPTURE)

# Starting squares, which is what `PieceTracker` uses for identity.
WHITE_PAWN_SQUARES = tuple(range(8, 16))
BLACK_PAWN_SQUARES = tuple(range(48, 56))
WHITE_BACK_SQUARES = tuple(square for square in range(0, 8) if square != chess.E1)
BLACK_BACK_SQUARES = tuple(square for square in range(56, 64) if square != chess.E8)


def piece_key(identity: int) -> tuple[str, str, int] | None:
    """Map a tracked identity to the model's ``(colour, kind, index)``.

    Returns None for the kings, which the model does not represent — they are
    never captured, so they carry no variables.
    """
    for squares, colour, kind in (
        (WHITE_PAWN_SQUARES, "W", "P"),
        (BLACK_PAWN_SQUARES, "B", "P"),
        (WHITE_BACK_SQUARES, "W", "N"),
        (BLACK_BACK_SQUARES, "B", "N"),
    ):
        if identity in squares:
            return colour, kind, squares.index(identity)
    return None


@dataclass(frozen=True, slots=True)
class Observation:
    """A real game, expressed in the model's vocabulary."""

    shape: Shape
    pawn_moves_by_block: dict[tuple[str, int], list[int]]
    """Per pawn, how many moves it makes in each block of its colour."""

    capture_block: dict[tuple[str, str, int], int]
    """Per captured piece, which block it dies in. Absent means it survived."""

    total_pawn_moves: int
    total_captures: int
    pawn_captures: int
    closing_segment: int
    """Quiet moves after the last critical one, as a 0/1 segment count."""

    @property
    def k(self) -> int:
        return (
            self.total_pawn_moves
            + self.total_captures
            - self.pawn_captures
            + self.closing_segment
        )


def observe(skeleton: Skeleton) -> Observation:
    """Read a real game into the model's variables.

    Checkmate games only. The closing segment is read off the MATE
    pseudo-event, which is how a quiet mate appears in a skeleton; a draw's
    clock-runout closing segment has no representation in :class:`Skeleton` —
    every segment there carries a critical move — so a draw game would come
    back with `T = 0` and a `K` one short, silently. :func:`validate` refuses
    such a skeleton rather than mis-stating it.
    """
    events = extract_events(skeleton)
    runs = phases(events)
    shape = Shape(tuple(colour for colour, _, _ in runs))

    block_of_event: dict[int, int] = {}
    for block, (_, first, last) in enumerate(runs):
        for index in range(first, last + 1):
            block_of_event[index] = block

    blocks_of = {colour: shape.blocks_of(colour) for colour in ("W", "B")}
    pawn_moves: dict[tuple[str, int], list[int]] = {
        (colour, index): [0] * len(blocks_of[colour])
        for colour in ("W", "B")
        for index in range(PAWNS_PER_SIDE)
    }
    capture_block: dict[tuple[str, str, int], int] = {}

    for event in events:
        block = block_of_event[event.index]
        if event.kind in PAWN_KINDS:
            key = piece_key(event.mover)
            if key is not None and key[1] == "P":
                colour, _, index = key
                pawn_moves[colour, index][blocks_of[colour].index(block)] += 1
        if event.victim is not None:
            victim = piece_key(event.victim)
            if victim is not None:
                capture_block[victim] = block

    return Observation(
        shape=shape,
        pawn_moves_by_block=pawn_moves,
        capture_block=capture_block,
        total_pawn_moves=sum(1 for e in events if e.kind in PAWN_KINDS),
        total_captures=sum(1 for e in events if e.is_capture),
        pawn_captures=sum(1 for e in events if e.kind is EventKind.PAWN_CAPTURE),
        closing_segment=sum(1 for e in events if e.kind is EventKind.MATE),
    )


@dataclass(frozen=True, slots=True)
class ValidationResult:
    accepted: bool
    status: str
    observation: Observation
    complaint: str = ""


def validate(skeleton: Skeleton) -> ValidationResult:
    """Feed a real game to the model and insist it is accepted.

    Every variable is pinned to what the game actually did, so the solver is
    only being asked whether the constraints permit it. INFEASIBLE means a
    constraint contradicts a game that demonstrably exists.
    """
    from ortools.sat.python import cp_model

    from .abstract import build

    if not skeleton.ends_in_checkmate:
        raise ValueError(
            "validate() maps checkmate games only: the observation reads the "
            "closing segment off the MATE pseudo-event, and a draw's "
            "clock-runout closing segment has no representation in a "
            "Skeleton. Extending this needs a skeleton form that carries "
            "that segment, not a silent T = 0."
        )

    observation = observe(skeleton)
    # The ending is explicit, not the default: this function's whole point is
    # pinning what the model is asked, and the skeleton just attested to it.
    model, handles = build(
        observation.shape, target_k=observation.k, ending=CHECKMATE
    )

    for (colour, index), per_block in observation.pawn_moves_by_block.items():
        variables = list(handles.moves[colour, index].values())
        for variable, value in zip(variables, per_block, strict=True):
            model.add(variable == value)

    for key, variable in handles.captured.items():
        model.add(variable == (1 if key in observation.capture_block else 0))
    for key, block in observation.capture_block.items():
        model.add(handles.capture_block[key][block] == 1)

    model.add(handles.pawn_captures == observation.pawn_captures)
    model.add(handles.closing_segment == observation.closing_segment)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60.0
    status = solver.solve(model)
    accepted = status in (cp_model.OPTIMAL, cp_model.FEASIBLE)

    return ValidationResult(
        accepted=accepted,
        status=solver.status_name(status),
        observation=observation,
        complaint=(
            ""
            if accepted
            else "the model rejects a game that exists; a constraint is "
            "stronger than legality and every UNSAT from it is void"
        ),
    )
