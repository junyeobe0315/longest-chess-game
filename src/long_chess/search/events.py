"""Critical events, with the piece identities that constrain their order.

The observation this milestone turns on: **nobody chooses who plays a critical
move.** A pawn move is made by that pawn's colour, and a capture is made by the
colour that does not own the victim. So for a fixed set of critical events the
multiset of actors is fixed too — here 60 Black and 58 White — and S depends on
nothing but the *order* they are played in.

That reduces "can S be cut from 3 to 2" from a question about chess to a
question about scheduling 118 coloured events under precedence constraints.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

import chess

from ..skeleton import Skeleton


class EventKind(StrEnum):
    PAWN = "pawn"
    """A pawn push. Also covers double pushes."""

    PROMOTION = "promotion"
    PAWN_CAPTURE = "pawn-capture"
    """A pawn capturing: one move doing the work of two critical moves.

    These are the ``Cₚ`` in ``K ≤ 96 + 30 − 8``, and there are exactly 8.
    """

    CAPTURE = "capture"
    MATE = "mate"
    """The closing checkmate, when it is neither a pawn move nor a capture.

    It closes a segment anyway, because mate outranks the 75-move draw.
    """


@dataclass(frozen=True, slots=True)
class CriticalEvent:
    index: int
    """Position in the skeleton, 0-based."""

    actor: chess.Color
    kind: EventKind
    mover: int
    """Identity of the piece that moves, stable across the whole game.

    A promoting pawn keeps its identity as the piece it becomes; that is what
    makes "this rook cannot be captured before the pawn promoted" expressible.
    """

    victim: int | None
    san: str

    @property
    def actor_name(self) -> str:
        return "W" if self.actor else "B"

    @property
    def is_capture(self) -> bool:
        return self.kind in (EventKind.CAPTURE, EventKind.PAWN_CAPTURE)


class PieceTracker:
    """Follows each of the 32 starting pieces by identity, not by square.

    Squares are useless for this: pieces move, and a promoted pawn changes type
    without changing identity.
    """

    def __init__(self, board: chess.Board) -> None:
        self.at: dict[int, int] = {}
        for identity, square in enumerate(sorted(chess.SQUARES)):
            if board.piece_at(square) is not None:
                self.at[square] = identity

    def apply(self, board: chess.Board, move: chess.Move) -> tuple[int, int | None]:
        """Play ``move`` on the tracker. Returns ``(mover, victim)`` identities."""
        mover = self.at.pop(move.from_square)
        victim: int | None = None

        if board.is_en_passant(move):
            captured_square = move.to_square + (-8 if board.turn else 8)
            victim = self.at.pop(captured_square, None)
        elif move.to_square in self.at:
            victim = self.at.pop(move.to_square)

        self.at[move.to_square] = mover

        if board.is_castling(move):
            # The rook moves too. Filler never castles, but a skeleton might.
            back = chess.square_rank(move.from_square) * 8
            kingside = chess.square_file(move.to_square) > chess.square_file(
                move.from_square
            )
            rook_from = back + (7 if kingside else 0)
            rook_to = back + (5 if kingside else 3)
            if rook_from in self.at:
                self.at[rook_to] = self.at.pop(rook_from)

        return mover, victim


def classify(board: chess.Board, move: chess.Move, is_last: bool) -> EventKind:
    piece = board.piece_at(move.from_square)
    is_pawn = piece is not None and piece.piece_type == chess.PAWN
    if board.is_capture(move):
        return EventKind.PAWN_CAPTURE if is_pawn else EventKind.CAPTURE
    if move.promotion:
        return EventKind.PROMOTION
    if is_pawn:
        return EventKind.PAWN
    if is_last:
        return EventKind.MATE
    raise ValueError(f"{move.uci()} is not a critical move")


def extract_events(skeleton: Skeleton) -> list[CriticalEvent]:
    """The skeleton's critical moves, with actors and piece identities."""
    board = chess.Board(skeleton.start_fen)
    tracker = PieceTracker(board)
    events: list[CriticalEvent] = []

    for index, segment in enumerate(skeleton.segments):
        for move in segment.bridge_moves:
            tracker.apply(board, move)
            board.push(move)

        move = segment.critical_move
        kind = classify(board, move, is_last=index == len(skeleton.segments) - 1)
        san = board.san(move)
        actor = board.turn
        mover, victim = tracker.apply(board, move)
        board.push(move)

        events.append(
            CriticalEvent(
                index=index,
                actor=actor,
                kind=kind,
                mover=mover,
                victim=victim,
                san=san,
            )
        )

    return events


def actor_counts(events: list[CriticalEvent]) -> dict[str, int]:
    counts = {"W": 0, "B": 0}
    for event in events:
        counts[event.actor_name] += 1
    return counts


def phases(events: list[CriticalEvent]) -> list[tuple[str, int, int]]:
    """Runs of consecutive same-colour events, as ``(colour, first, last)``."""
    runs: list[list] = []
    for event in events:
        if runs and runs[-1][0] == event.actor_name:
            runs[-1][2] = event.index
        else:
            runs.append([event.actor_name, event.index, event.index])
    return [tuple(run) for run in runs]
