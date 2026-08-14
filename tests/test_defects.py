"""Regressions for defects found by review rather than by a failing test.

Each of these passed silently before, and each was wrong in the direction that
does not announce itself: a game longer than it really is, a timeout reported
as a proof, a documented safety argument pointing the wrong way.
"""

from __future__ import annotations

import chess
import pytest

from long_chess.verifier import (
    GameVerifier,
    Termination,
    VerificationError,
    moves_from_san,
    verify_game,
)

MATE_IN_FOUR = "f3 e5 g4 Qh4"

# White to move with the clock at 149; Ra2 is quiet and draws by the 75-move
# rule, closing a segment that holds no critical move at all.
BRINK = "6k1/5ppp/8/8/8/8/8/R6K w - - 149 100"


class TestLeftoverMovesAfterTermination:
    """`verify_game` counted leftovers by re-reading its input, which a
    one-shot generator cannot do. Moves after a checkmate went unnoticed."""

    def test_a_list_with_trailing_moves_is_rejected(self):
        moves = moves_from_san(MATE_IN_FOUR) + [chess.Move.from_uci("h1g1")]
        with pytest.raises(VerificationError, match="unplayed"):
            verify_game(moves)

    def test_a_generator_with_trailing_moves_is_rejected_too(self):
        """The actual defect. Same game, same trailing move, fed lazily."""
        moves = moves_from_san(MATE_IN_FOUR) + [chess.Move.from_uci("h1g1")]
        with pytest.raises(VerificationError, match="unplayed"):
            verify_game(move for move in moves)

    def test_a_generator_that_ends_cleanly_still_works(self):
        result = verify_game(move for move in moves_from_san(MATE_IN_FOUR))
        assert result.termination is Termination.CHECKMATE
        assert result.plies == 4

    def test_the_leftover_count_is_right(self):
        moves = moves_from_san(MATE_IN_FOUR) + [chess.Move.from_uci("h1g1")] * 3
        with pytest.raises(VerificationError, match="3 move"):
            verify_game(move for move in moves)


class TestAlreadyFinishedStartingPosition:
    """Nothing checked whether the board handed in was already over."""

    def test_a_checkmated_start_is_rejected(self):
        board = chess.Board()
        for move in moves_from_san(MATE_IN_FOUR):
            board.push(move)
        assert board.is_checkmate()
        with pytest.raises(VerificationError, match="already over"):
            verify_game([], board)

    def test_a_stalemated_start_is_rejected(self):
        board = chess.Board("7k/8/6Q1/8/8/8/8/K7 b - - 0 1")
        assert board.is_stalemate()
        with pytest.raises(VerificationError, match="already over"):
            verify_game([], board)

    def test_a_dead_material_start_is_rejected(self):
        with pytest.raises(VerificationError, match="already over"):
            verify_game([], chess.Board("7k/8/8/8/8/8/8/K7 w - - 0 1"))

    def test_an_ordinary_start_is_fine(self):
        result = verify_game(moves_from_san(MATE_IN_FOUR))
        assert result.plies == 4


class TestClosingSegmentForEveryEnding:
    """`critical_count` credited the closing segment only to checkmate.

    K counts segments, and quiet moves after the last critical one form one
    whatever ends the game. Counting it only for mate understates K for every
    draw — which is exactly what the bound's draw case is made of.
    """

    def test_a_quiet_checkmate_closes_a_segment(self):
        result = verify_game(moves_from_san(MATE_IN_FOUR))
        assert result.termination is Termination.CHECKMATE
        assert result.critical_plies == (1, 2, 3)
        assert result.critical_count == 4

    def test_a_quiet_seventyfive_move_draw_closes_one_too(self):
        """The regression. This used to report 0."""
        result = verify_game([chess.Move.from_uci("a1a2")], chess.Board(BRINK))
        assert result.termination is Termination.SEVENTYFIVE_MOVE_RULE
        assert result.critical_plies == ()
        assert result.critical_count == 1

    def test_a_quiet_stalemate_closes_one_too(self):
        result = verify_game(
            [chess.Move.from_uci("g5g6")],
            chess.Board("7k/8/8/6Q1/8/8/8/K7 w - - 0 1"),
        )
        assert result.termination is Termination.STALEMATE
        assert result.critical_count == 1

    def test_a_critical_last_move_closes_nothing_extra(self):
        """Scholar's mate ends on a capture, which is already a segment."""
        result = verify_game(moves_from_san("e4 e5 Bc4 Nc6 Qh5 Nf6 Qxf7"))
        assert result.critical_plies[-1] == result.plies
        assert result.critical_count == len(result.critical_plies) == 3

    def test_an_unfinished_game_closes_nothing(self):
        verifier = GameVerifier()
        for move in moves_from_san("e4 e5"):
            verifier.push(move)
        assert verifier.termination is Termination.CONTINUE
        assert verifier.critical_count == 2



class TestSolverInconclusive:
    """A timeout is not a refutation."""

    def test_unknown_raises_instead_of_reporting_infeasible(self):
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from long_chess.model import Inconclusive, Shape, solve

        with pytest.raises(Inconclusive, match="not a refutation"):
            solve(Shape(("B", "W", "B")), time_limit=1e-4)

    def test_a_real_infeasible_still_reports_infeasible(self):
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from long_chess.model import Shape, solve

        result = solve(Shape(("B", "W", "B")))
        assert result.status == "INFEASIBLE"
        assert not result.feasible


class TestTheUnresolvedPairCapWasFalse:
    """`UNRESOLVED_FILE_CAP = 4` excluded legal games.

    It is the one defect on this list that was wrong in the *strong* direction:
    a constraint tighter than legality turns legal games into UNSAT, and UNSAT
    is what the whole result is made of. Everything else here inflated a number;
    this one would have invented a proof.

    The counterexample is in `tests/test_bound.py::TestTheOldCapWasFalse`. What
    is checked here is that no arm of the pipeline still uses 4.
    """

    def test_the_ceiling_with_no_file_resolved_is_80_not_32(self):
        from long_chess.bound import pawn_moves_ceiling

        assert pawn_moves_ceiling(0) == 80
        assert pawn_moves_ceiling(0) != 4 * 8

    def test_the_coupling_is_80_plus_2f_across_the_board(self):
        from long_chess.bound import FILES, pawn_moves_ceiling

        for resolved in range(FILES + 1):
            assert pawn_moves_ceiling(resolved) == min(96, 80 + 2 * resolved)

    def test_the_cross_check_agrees_rather_than_carrying_the_old_number(self):
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from long_chess.bound import FILES, pawn_moves_ceiling
        from long_chess.model import independent

        for resolved in range(FILES + 1):
            assert independent.pawn_ceiling(resolved) == pawn_moves_ceiling(resolved)

    def test_the_old_constant_is_gone_entirely(self):
        """Not left behind as an alias. A name that says `FILE` and means
        `origin pair`, holding a number that is false, is worse than absent."""
        from long_chess.bound import pawns

        assert not hasattr(pawns, "UNRESOLVED_FILE_CAP")

    def test_the_conclusion_survived_the_correction(self):
        """The whole point: the bound was re-derived, not adjusted to fit."""
        from long_chess.bound import critical_bound, switch_lower_bound

        assert critical_bound().total == 118
        assert switch_lower_bound().max_plies == 17_697


class TestCheckmateBranchWasNotAModel:
    """The checkmate branch forced the mated side to lose all fifteen units.

    That is what `K = 118` implies, not what checkmate implies. At 118,
    `C + T = 30` with `C ≤ 29` and `T ≤ 1` forces `C = 29, T = 1`, and 29
    captures leave one non-king unit — which the mating side must own, since a
    lone king cannot mate. So the mated side is a lone king *there*, and only
    there.

    Scholar's mate is the counterexample: a legal checkmate in which Black has
    lost exactly one unit. The model rejected it, so "every legal game maps to a
    solution" was false for every K but 118 — a claim of generality the model
    did not have, in a model whose whole value is being weaker than legality.

    The verdicts at 118 were never affected, and the counting proof does not use
    the model at all.
    """

    # 1. e4 e5  2. Bc4 Nc6  3. Qh5 Nf6  4. Qxf7#
    # Critical: e4 (White), e5 (Black), Qxf7 (White). Blocks W B W.
    SCHOLAR = "e4 e5 Bc4 Nc6 Qh5 Nf6 Qxf7"

    @staticmethod
    def solver():
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from ortools.sat.python import cp_model

        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 30.0
        return cp_model, solver

    def test_scholars_mate_is_a_checkmate_that_keeps_its_army(self):
        """The premise, checked against the verifier rather than asserted."""
        result = verify_game(moves_from_san(self.SCHOLAR))
        assert result.termination is Termination.CHECKMATE
        assert result.critical_count == 3
        # Black has lost one unit; White none.
        board = chess.Board()
        for move in moves_from_san(self.SCHOLAR):
            board.push(move)
        assert len(board.piece_map()) == 31

    def test_the_model_accepts_its_profile(self):
        """P=2, C=1, O=0, T=0, K=3, shape W B W. This used to be INFEASIBLE."""
        cp_model, solver = self.solver()
        from long_chess.model import Shape, build

        model, handles = build(Shape(("W", "B", "W")), target_k=3, ending="checkmate")
        model.add(handles.pawn_moves == 2)
        model.add(handles.total_captures == 1)
        model.add(handles.pawn_captures == 0)
        model.add(handles.closing_segment == 0)
        assert solver.solve(model) in (cp_model.OPTIMAL, cp_model.FEASIBLE)

    def test_the_mated_side_may_keep_almost_everything(self):
        cp_model, solver = self.solver()
        from long_chess.model import Shape, build

        model, handles = build(Shape(("W", "B", "W")), target_k=3, ending="checkmate")
        kept = sum(
            value for (colour, _, _), value in handles.captured.items() if colour == "B"
        )
        model.add(kept <= 1)
        assert solver.solve(model) in (cp_model.OPTIMAL, cp_model.FEASIBLE)

    def test_but_the_mating_side_still_needs_something_to_mate_with(self):
        """The one thing checkmate does imply, and it is still imposed."""
        cp_model, solver = self.solver()
        from long_chess.model import Shape, build

        model, handles = build(Shape(("W", "B", "W")), target_k=3, ending="checkmate")
        lost = sum(
            value for (colour, _, _), value in handles.captured.items() if colour == "W"
        )
        model.add(lost == 15)
        assert solver.solve(model) == cp_model.INFEASIBLE

    def test_pawn_captures_cannot_exceed_the_totals_they_are_part_of(self):
        """`pawn_captures` had a floor but no ceiling, so a low target could be met
        with more pawn captures than pawn moves. Both bounds follow from a pawn capture
        being a pawn move *and* a capture."""
        cp_model, solver = self.solver()
        from long_chess.model import Shape, build

        model, handles = build(Shape(("W", "B", "W")), target_k=3, ending="checkmate")
        model.add(handles.pawn_moves == 0)
        model.add(handles.pawn_captures >= 1)
        assert solver.solve(model) == cp_model.INFEASIBLE

    def test_the_cross_check_was_over_constrained_the_same_way(self):
        """It also forced a quiet mate. A mate delivered by a capture or a pawn
        move closes no extra segment, so T = 0 is legal."""
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from long_chess.model import Shape, analyse_independently

        # If T were still pinned to 1, checkmate could not reach the draw
        # column's maxima, which is exactly the symptom.
        for colours in (("B", "W"), ("B", "W", "B")):
            mate = analyse_independently(Shape(colours), ending="checkmate")
            draw = analyse_independently(Shape(colours), ending="draw")
            assert mate.max_k == draw.max_k, colours

    def test_the_118_verdicts_were_never_affected(self):
        """Which is why the result did not move: the dropped constraint is
        derivable at K = 118, and the counting proof never used the model."""
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from long_chess.bound import switch_lower_bound
        from long_chess.model import ENDINGS, Shape, solve

        for ending in ENDINGS:
            for colours in (("B",), ("W",), ("B", "W"), ("W", "B"), ("B", "W", "B")):
                assert not solve(Shape(colours), ending=ending).feasible
            assert solve(Shape(("B", "W", "B", "W")), ending=ending).feasible
        assert switch_lower_bound().max_plies == 17_697


class TestMatingSideIsTheLastEndpoint:
    """`mating_colour = colours[-1]` is sound over *endpoint* shapes only.

    A quiet mate can be delivered by the colour that made no critical move
    last. In the game below, Black captures all fifteen White units while
    White shuffles a knight, the bare White king captures one Black pawn —
    White's only critical move — and Black mates the lone king quietly. The
    critical actors are (B, W); the mater is Black.

    Pinning that game's profile into shape (B, W) under checkmate is
    INFEASIBLE, because there the model reads White as the mater and White
    has nothing left. The model is not wrong; the reading is. The mate is the
    game's last segment *endpoint*, so under the endpoint convention — the
    sequence S is measured over, now stated in `model/abstract.py` — the
    game's shape is (B, W, B), where the same profile is feasible. The
    convention was unstated, and the sentence in docs/abstract-model.md that
    defined the model's question said the opposite one; under that documented
    reading the checkmate branch rejected this legal game, the same failure
    class as the false cap of 4 and the old checkmate branch.
    """

    # Black eats everything with knights and bishops, in an order that never
    # gives check; White declines every capture, shuffling a knight until both
    # are eaten, then walks the bare king out to take the one Black pawn left
    # hanging for it. 76 ply, verified legal move by move.
    QUIET_MATE_BY_THE_OTHER_COLOUR = (
        "Nf3 Nf6 Ng1 Ng4 Nf3 Nxf2 Ng1 Nxh1 Nf3 Ng3 Ng1 Nxf1 Nf3 Nxd2 Ng1 Nb3 "
        "Nf3 Nxa1 Ng1 Nc6 Nf3 Nd4 Ng1 Nxe2 Nf3 Nxc1 Ng1 Nxa2 Nf3 Nb4 Ng1 Nd5 "
        "Nf3 Nc3 Ng1 Nxd1 Nf3 Nxb2 Ng1 d5 Nf3 Bf5 Ng1 Bxc2 Nf3 e6 Ng1 Bd6 "
        "Nf3 Bxh2 Ng1 h5 Nf3 h4 Ng1 h3 Nf3 hxg2 Ng1 Bxg1 "
        "Na3 Rh5 Nb1 Bc5 Na3 Bd6 Nb1 Bxb1 "
        "Kd2 Bd3 Ke3 Qh4 Kf3 Rf5+ Kxg2 Qh2#"
    )

    # What the game observes: P = 6 (e6, d5, and the h-pawn's four), C = 16
    # (all 15 White units, plus the king taking the g2 pawn), Cₚ = 1 (hxg2),
    # T = 1 (the mate is quiet), K = 6 + 16 - 1 + 1 = 22.
    PROFILE = {"pawn_moves": 6, "captures": 16, "pawn_captures": 1, "closing": 1}
    TARGET_K = 22

    def test_the_game_is_legal_and_black_mates_quietly(self):
        """The premise, checked against the verifier rather than asserted."""
        moves = moves_from_san(self.QUIET_MATE_BY_THE_OTHER_COLOUR)
        result = verify_game(moves)
        assert result.termination is Termination.CHECKMATE
        assert result.plies == 76
        # The mate is quiet: the last critical ply is White's Kxg2, one before.
        assert result.critical_plies[-1] == 75
        # The mating move is Black's (even ply), so the terminal endpoint is B.
        assert result.plies % 2 == 0

    def test_white_makes_exactly_one_critical_move_and_it_is_the_last(self):
        """Critical actors (B, W): every Black critical move precedes it."""
        board = chess.Board()
        actors = []
        for move in moves_from_san(self.QUIET_MATE_BY_THE_OTHER_COLOUR):
            is_pawn = board.piece_at(move.from_square).piece_type == chess.PAWN
            if is_pawn or board.is_capture(move):
                actors.append("W" if board.turn == chess.WHITE else "B")
            board.push(move)
        assert actors == ["B"] * 20 + ["W"]

    def test_black_captures_all_fifteen_white_units(self):
        board = chess.Board()
        for move in moves_from_san(self.QUIET_MATE_BY_THE_OTHER_COLOUR):
            board.push(move)
        white_units = [
            piece
            for piece in board.piece_map().values()
            if piece.color == chess.WHITE and piece.piece_type != chess.KING
        ]
        assert white_units == []

    def _pin(self, colours: tuple[str, ...]):
        from long_chess.model import Shape, build

        model, handles = build(
            Shape(colours), target_k=self.TARGET_K, ending="checkmate"
        )
        model.add(handles.pawn_moves == self.PROFILE["pawn_moves"])
        model.add(handles.total_captures == self.PROFILE["captures"])
        model.add(handles.pawn_captures == self.PROFILE["pawn_captures"])
        model.add(handles.closing_segment == self.PROFILE["closing"])
        for colour, lost in (("W", 15), ("B", 1)):
            model.add(
                sum(
                    value
                    for (owner, _, _), value in handles.captured.items()
                    if owner == colour
                )
                == lost
            )
        return model

    def test_the_profile_is_feasible_in_its_endpoint_shape(self):
        """(B, W, B): the quiet mate is Black's endpoint and Black is the
        mater, so `captured(B) = 1` clears the mating-side cap."""
        cp_model, solver = TestCheckmateBranchWasNotAModel.solver()
        model = self._pin(("B", "W", "B"))
        assert solver.solve(model) in (cp_model.OPTIMAL, cp_model.FEASIBLE)

    def test_the_same_profile_in_the_critical_actor_shape_is_not(self):
        """(B, W) reads White as the mater, and `captured(W) = 15` breaks the
        cap. Correct behaviour — an endpoint-shape (B, W) checkmate really is
        mated by White — and exactly why the shapes must be endpoint shapes:
        were they critical-actor shapes, this game would land here and the
        INFEASIBLE would be rejecting a legal game."""
        cp_model, solver = TestCheckmateBranchWasNotAModel.solver()
        model = self._pin(("B", "W"))
        assert solver.solve(model) == cp_model.INFEASIBLE

    def test_the_two_shapes_are_two_readings_of_one_game(self):
        """The seam is the one `bound.blocks` already owns: dropping the
        terminal endpoint turns (B, W, B) into (B, W) and cannot add a switch."""
        from long_chess.bound import critical_actor_shape, switches

        endpoint = ("B", "W", "B")
        assert critical_actor_shape(endpoint, terminal_alone=True) == ("B", "W")
        assert switches(("B", "W")) <= switches(endpoint)


class TestPgnParseErrorsAreNotSwallowed:
    """`chess.pgn` records unparseable tokens on `game.errors` and reads on.

    A truncated move list would then reach the verifier, which would report a
    short game as perfectly legal rather than as a parse failure.
    """

    def test_a_broken_pgn_raises_rather_than_truncating(self, tmp_path):
        from long_chess.verifier import moves_from_pgn

        path = tmp_path / "broken.pgn"
        path.write_text("1. e4 e5 2. Nf3 zz9 3. Bc4 Nc6\n", encoding="utf-8")
        with pytest.raises(ValueError, match="parse error"):
            moves_from_pgn(path)

    def test_a_clean_pgn_still_reads(self, tmp_path):
        from long_chess.verifier import moves_from_pgn

        path = tmp_path / "fine.pgn"
        path.write_text("1. e4 e5 2. Nf3 Nc6 1/2-1/2\n", encoding="utf-8")
        assert len(moves_from_pgn(path)) == 4

    def test_the_reference_game_parses_without_errors(self, published_moves):
        assert len(published_moves) == 17_697


class TestUnknownEndingIsRejected:
    """`ending` fell through to the draw branch for any unrecognised string.

    The draw branch has the *higher* capture ceiling, so a typo relaxed the
    model silently and every verdict from it would have been about a game
    nobody asked about.
    """

    @pytest.mark.parametrize("bad", ["stalemate", "Draw", "", "mate"])
    def test_the_model_rejects_it(self, bad: str):
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from long_chess.model import Shape, build, solve

        with pytest.raises(ValueError, match="ending must be one of"):
            build(Shape(("B", "W", "B")), ending=bad)
        with pytest.raises(ValueError, match="ending must be one of"):
            solve(Shape(("B", "W", "B")), ending=bad)

    @pytest.mark.parametrize("bad", ["stalemate", "Draw", ""])
    def test_the_cross_check_rejects_it_too(self, bad: str):
        pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")
        from long_chess.model import Shape, analyse_independently

        with pytest.raises(ValueError, match="ending must be one of"):
            analyse_independently(Shape(("B", "W", "B")), ending=bad)

