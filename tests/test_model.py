"""The abstract model. Skipped unless the ``solver`` extra is installed."""

from __future__ import annotations

import pytest

pytest.importorskip("ortools", reason="needs `uv sync --extra solver`")

from long_chess.bound import refutations, switch_lower_bound  # noqa: E402
from long_chess.model import (  # noqa: E402
    CHECKMATE,
    DRAW,
    ENDINGS,
    Shape,
    all_shapes,
    build,
    require_ending,
    solve,
    validate,
)


@pytest.fixture(scope="module")
def results():
    return {
        (ending, shape.colours): solve(shape, ending=ending)
        for ending in ENDINGS
        for shape in all_shapes(4)
    }


class TestSoundness:
    """The checks that decide whether any UNSAT from this model is worth having."""

    def test_the_model_accepts_the_published_game(self, compressed_skeleton):
        """If it did not, a constraint would be stronger than legality and
        every infeasible result would be an artefact."""
        result = validate(compressed_skeleton)
        assert result.accepted, result.complaint

    def test_the_observation_matches_the_known_numbers(self, compressed_skeleton):
        observation = validate(compressed_skeleton).observation
        assert observation.shape.colours == ("B", "W", "B", "W")
        assert observation.shape.switches == 3
        assert (
            observation.total_pawn_moves,
            observation.total_captures,
            observation.pawn_captures,
            observation.closing_segment,
        ) == (96, 29, 8, 1)
        assert observation.k == 118

    def test_the_known_game_satisfies_the_new_coupling(self, compressed_skeleton):
        """P ≤ 80 + 2f with f ≤ O. The constraint that replaced the false
        `P ≤ 32 + 8f`, checked against a game that demonstrably exists."""
        observation = validate(compressed_skeleton).observation
        assert observation.total_pawn_moves <= 80 + 2 * observation.pawn_captures
        assert observation.total_pawn_moves - observation.pawn_captures <= 88
        assert observation.total_captures + observation.closing_segment <= 30

    def test_the_shape_the_known_game_uses_is_feasible(self, results):
        assert results[CHECKMATE, ("B", "W", "B", "W")].feasible


class TestValidateScope:
    """`validate()` maps checkmate games only, and now says so.

    The observation reads the closing segment off the MATE pseudo-event, and a
    draw's clock-runout closing segment has no representation in a `Skeleton` —
    so a draw game used to come back with `T = 0`, a `K` one short, and the
    default checkmate branch silently applied. The tool whose job is catching
    over-constraint must not itself mis-state the game it feeds in.
    """

    def test_a_draw_skeleton_is_refused_loudly(self, compressed_skeleton):
        import dataclasses

        draw = dataclasses.replace(compressed_skeleton, ends_in_checkmate=False)
        with pytest.raises(ValueError, match="checkmate games only"):
            validate(draw)

    def test_the_checkmate_path_is_unchanged(self, compressed_skeleton):
        assert compressed_skeleton.ends_in_checkmate
        assert validate(compressed_skeleton).accepted


class TestFeasibility:
    @pytest.mark.parametrize("ending", ENDINGS)
    def test_no_shape_with_two_or_fewer_switches_works(self, results, ending):
        for (found, colours), result in results.items():
            if found == ending and Shape(colours).switches <= 2:
                assert not result.feasible, (ending, colours)

    @pytest.mark.parametrize("ending", ENDINGS)
    def test_the_minimum_feasible_switch_count_is_three(self, results, ending):
        feasible = [
            Shape(colours).switches
            for (found, colours), result in results.items()
            if found == ending and result.feasible
        ]
        assert min(feasible) == 3

    @pytest.mark.parametrize("ending", ENDINGS)
    def test_which_gives_17697(self, results, ending):
        best = min(
            Shape(colours).switches
            for (found, colours), result in results.items()
            if found == ending and result.feasible
        )
        assert 150 * 118 - best == 17_697

    @pytest.mark.parametrize("ending", ENDINGS)
    def test_a_feasible_solution_maxes_out_every_term(self, results, ending):
        """K = 118 leaves no slack: P − Cₚ = 88 and C + T = 30, both forced."""
        solution = results[ending, ("B", "W", "B", "W")]
        assert solution.pawn_moves - solution.pawn_captures == 88
        assert solution.captures + solution.closing_segment == 30
        assert solution.pawn_moves == 96
        assert solution.pawn_captures == 8

    def test_the_solver_agrees_with_the_counting_proof(self, results):
        """`bound.blocks` refutes every S ≤ 2 shape without a solver. The model
        is the cross-check on that, not the other way round."""
        refuted = {r.colours for r in refutations()}
        for ending in ENDINGS:
            for colours in refuted:
                assert not results[ending, colours].feasible, (ending, colours)
        assert switch_lower_bound().minimum_switches == 3


class TestWhatCarriesTheResult:
    """Which constraint rules out which shape, so nothing is taken on faith."""

    @pytest.mark.parametrize("colours", [("B", "W"), ("W", "B")])
    @pytest.mark.parametrize("ending", ENDINGS)
    def test_the_two_block_shapes_die_to_counting_alone(self, colours, ending):
        """Not to the home-rank lemma. The colour moving first must make all
        its captures before the other has moved, which kills pawns unmoved."""
        assert not solve(
            Shape(colours), ending=ending, home_rank_limit=False
        ).feasible

    @pytest.mark.parametrize("ending", ENDINGS)
    def test_black_white_black_dies_only_to_the_home_rank_lemma(self, ending):
        """The decisive one. Without the lemma this shape is feasible, so the
        whole S ≥ 3 result rests on it — which is why it is conditional and
        machine-checked."""
        assert solve(
            Shape(("B", "W", "B")), ending=ending, home_rank_limit=False
        ).feasible
        assert not solve(Shape(("B", "W", "B")), ending=ending).feasible

    def test_the_lemma_does_not_rule_out_the_known_shape(self):
        """A constraint that killed the shape the real game uses would be
        unsound on its face."""
        assert solve(Shape(("B", "W", "B", "W"))).feasible

    @pytest.mark.parametrize("colours", [("B",), ("W",)])
    @pytest.mark.parametrize("ending", ENDINGS)
    def test_the_single_block_shapes_need_no_lemma_either(self, colours, ending):
        """P = 96 needs both colours' pawns to move and one colour has no
        block; the lemma never enters. Previously documented in the README
        table but pinned nowhere."""
        assert not solve(
            Shape(colours), ending=ending, home_rank_limit=False
        ).feasible

    @pytest.mark.parametrize("ending", ENDINGS)
    def test_white_black_white_also_flips_without_the_lemma(self, ending):
        """The mirror of B W B — the other shape the lemma alone rules out.
        With this, every row of the no-lemma column is pinned, not just the
        three the docs happened to discuss."""
        assert solve(
            Shape(("W", "B", "W")), ending=ending, home_rank_limit=False
        ).feasible
        assert not solve(Shape(("W", "B", "W")), ending=ending).feasible

    @pytest.mark.parametrize(
        "colours", [("B", "W", "B", "W"), ("W", "B", "W", "B")]
    )
    @pytest.mark.parametrize("ending", ENDINGS)
    def test_the_feasible_shapes_do_not_depend_on_it(self, colours, ending):
        """Dropping a constraint can only widen the feasible set, and the two
        S ≥ 3 shapes stay feasible with it dropped."""
        assert solve(Shape(colours), ending=ending, home_rank_limit=False).feasible


class TestTheEndingArgument:
    """A typo must not silently pick the more permissive branch."""

    @pytest.mark.parametrize("bad", ["stalemate", "Draw", "", "CHECKMATE", "mate"])
    def test_an_unknown_ending_is_rejected(self, bad: str):
        with pytest.raises(ValueError, match="ending must be one of"):
            require_ending(bad)

    @pytest.mark.parametrize("bad", ["stalemate", "Draw", ""])
    def test_build_rejects_it_too(self, bad: str):
        with pytest.raises(ValueError, match="ending must be one of"):
            build(Shape(("B", "W", "B")), ending=bad)

    @pytest.mark.parametrize("bad", ["stalemate", "Draw", ""])
    def test_and_so_does_solve(self, bad: str):
        with pytest.raises(ValueError, match="ending must be one of"):
            solve(Shape(("B", "W", "B")), ending=bad)

    def test_the_two_real_endings_still_pass(self):
        assert require_ending(CHECKMATE) == CHECKMATE
        assert require_ending(DRAW) == DRAW


class TestShapes:
    def test_switches_count_the_virtual_black_opening(self):
        assert Shape(("B",)).switches == 0
        assert Shape(("W",)).switches == 1
        assert Shape(("B", "W")).switches == 1
        assert Shape(("W", "B")).switches == 2
        assert Shape(("B", "W", "B")).switches == 2
        assert Shape(("B", "W", "B", "W")).switches == 3

    def test_the_mating_colour_is_the_last_block(self):
        assert Shape(("B", "W", "B")).mating_colour == "B"
        assert Shape(("B", "W", "B", "W")).mating_colour == "W"

    def test_all_shapes_alternate(self):
        for shape in all_shapes(5):
            for first, second in zip(shape.colours, shape.colours[1:], strict=False):
                assert first != second

    def test_the_shape_enumerations_agree(self):
        """`bound.blocks` enumerates the same shapes for the counting proof."""
        from long_chess.bound import alternating_shapes

        assert [shape.colours for shape in all_shapes(4)] == alternating_shapes(4)
