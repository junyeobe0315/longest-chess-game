"""FIDE rule primitives.

This module — and the whole ``verifier`` package — deliberately imports nothing
from the rest of ``long_chess``. The verifier is the independent judge of what
counts as a legal game; if it shared code with the search it would stop being
independent evidence.

References
----------
FIDE Laws of Chess, Article 9.6: https://handbook.fide.com/chapter/e012023
"""

from __future__ import annotations

from enum import StrEnum

import chess

# FIDE 9.6.2: drawn when the last 75 moves by *each* player have been completed
# without a pawn move and without a capture. 75 moves by each = 150 ply.
SEVENTYFIVE_MOVE_PLY_LIMIT = 150

# FIDE 9.6.1: drawn when the same position has appeared five times.
FIVEFOLD_REPETITION_COUNT = 5

# The position identity used for repetition counting:
#   (piece placement, side to move, castling rights, legal en-passant square)
RepetitionKey = tuple[str, bool, int, "int | None"]


class Termination(StrEnum):
    """Why the game ended, or CONTINUE if it did not.

    The order in which these are tested is itself a rule — see
    :func:`classify_position`.
    """

    CONTINUE = "continue"
    CHECKMATE = "checkmate"
    STALEMATE = "stalemate"
    INSUFFICIENT_MATERIAL = "insufficient-material"
    FIVEFOLD_REPETITION = "fivefold-repetition"
    SEVENTYFIVE_MOVE_RULE = "seventyfive-move-rule"

    @property
    def is_over(self) -> bool:
        return self is not Termination.CONTINUE

    @property
    def is_draw(self) -> bool:
        return self.is_over and self is not Termination.CHECKMATE


def repetition_key(board: chess.Board) -> RepetitionKey:
    """The position identity for five-fold repetition.

    Comparing whole FENs is wrong: the halfmove clock and the move number play
    no part in repetition, so including them makes every position look new and
    the five-fold rule never fires.

    Two subtleties, both of which FIDE spells out and both of which the raw
    python-chess attributes get wrong in the *same* direction (they distinguish
    positions that are in fact identical, which loses repetitions):

    - ``board.ep_square`` is set whenever the previous move was a double pawn
      push, even when no en-passant capture is actually available. Only a
      *legal* en-passant right makes two positions different.
    - ``board.castling_rights`` keeps bits for rights that cannot in fact be
      exercised. ``clean_castling_rights()`` masks those off.
    """
    ep_square = board.ep_square if board.has_legal_en_passant() else None
    return (
        board.board_fen(),
        board.turn,
        int(board.clean_castling_rights()),
        ep_square,
    )


def is_critical(board: chess.Board, move: chess.Move) -> bool:
    """Whether ``move`` (legal in ``board``) resets the 75-move counter.

    A pawn move or a capture — both are irreversible, which is what makes the
    game decompose into independent segments. Note that en passant and
    promotion are both already covered: en passant is a capture *and* a pawn
    move, promotion is a pawn move.

    A quiet final checkmate is neither, and this predicate says so. It still
    closes a segment — as the endpoint of the terminal quiet segment, the
    closing-segment term `T` in `K = (P − Cₚ) + (C + T)` — because checkmate
    takes precedence over the 75-move draw (Art. 9.6.2). That accounting
    lives in the segment layer (`critical_count` and the paper's
    Definition 2.2), not here.
    """
    piece = board.piece_at(move.from_square)
    return board.is_capture(move) or (
        piece is not None and piece.piece_type == chess.PAWN
    )


def classify_position(board: chess.Board, repetitions: int) -> Termination:
    """Classify the position *after* a move has been played.

    The order of these tests is the rule, not an implementation detail:

        checkmate > stalemate > insufficient material > fivefold > 150 ply

    In particular checkmate must be tested before the 150-ply limit. The last
    move of a maximal game is simultaneously the 150th quiet move of its
    segment and a checkmate; testing the clock first would score that game as a
    draw and one ply shorter.

    ``repetitions`` is how many times the current position has now occurred,
    counting this occurrence.
    """
    if board.is_checkmate():
        return Termination.CHECKMATE
    if board.is_stalemate():
        return Termination.STALEMATE
    # Fast first-pass only. This is python-chess's material-only test, not a
    # decision procedure for FIDE dead positions -- see docs/verification.md.
    if board.is_insufficient_material():
        return Termination.INSUFFICIENT_MATERIAL
    if repetitions >= FIVEFOLD_REPETITION_COUNT:
        return Termination.FIVEFOLD_REPETITION
    if board.halfmove_clock >= SEVENTYFIVE_MOVE_PLY_LIMIT:
        return Termination.SEVENTYFIVE_MOVE_RULE
    return Termination.CONTINUE
