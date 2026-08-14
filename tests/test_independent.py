"""The arithmetic cross-check, and whether it agrees with the solver.

A CP-SAT UNSAT is worth exactly as much as its encoding, and an encoding bug is
indistinguishable from a proof. ``long_chess.model.independent`` decides the
same question with no solver, declaring its own constants rather than importing
them. These check the two agree — and, first, that the cross-check is capable of
disagreeing.

It is a cross-check, not a second proof: it reads the same ``Shape`` and works
in the same numbers. The counting proof in ``long_chess.bound.blocks`` is the
one that stands alone.

Most of this file runs **without the solver extra** — that is the point of a
solver-free cross-check, and it used to be skipped wholesale exactly when no
solver was installed. Only the agreement tests, which call CP-SAT to have
something to agree with, skip on a missing ortools.
"""

from __future__ import annotations

import pytest

from long_chess.model import ENDINGS, Shape, all_shapes, analyse_independently
from long_chess.model.shape import CHECKMATE, DRAW


@pytest.fixture(scope="module")
def independent_results(request):
    """Every shape × ending, decided by the arithmetic checker alone.

    Cached across runs keyed by the checker's own sources, so any change to
    the arithmetic re-runs the enumeration instead of replaying old output.
    """
    import hashlib
    from pathlib import Path

    import long_chess.model.independent as independent_module
    import long_chess.model.shape as shape_module
    from long_chess.model.independent import IndependentResult

    digest = hashlib.sha256()
    for module in (independent_module, shape_module):
        digest.update(Path(module.__file__).read_bytes())
    key = f"long_chess/independent-results-{digest.hexdigest()[:16]}"
    cached = request.config.cache.get(key, None)
    if cached is not None:
        return {
            (ending, tuple(colours)): IndependentResult(
                shape=Shape(tuple(colours)), **fields
            )
            for ending, colours, fields in cached
        }
    results = {
        (ending, shape.colours): analyse_independently(shape, ending=ending)
        for ending in ENDINGS
        for shape in all_shapes(4)
    }
    request.config.cache.set(
        key,
        [
            [
                ending,
                list(colours),
                {
                    "max_pawn_moves": result.max_pawn_moves,
                    "max_k": result.max_k,
                    "feasible": result.feasible,
                    "account": result.account,
                },
            ]
            for (ending, colours), result in results.items()
        ],
    )
    return results





class TestTheConstantsHaveNotDrifted:
    """The cross-check declares its own numbers on purpose. These pin them to
    the canonical derivations, so a change to one shows up as a failure here
    rather than propagating silently into both."""

    def test_the_origin_pair_caps_match(self):
        from long_chess.bound import (
            RESOLVED_ORIGIN_PAIR_MOVE_CAP,
            UNRESOLVED_ORIGIN_PAIR_MOVE_CAP,
        )
        from long_chess.model import independent

        assert independent.UNRESOLVED_PAIR == UNRESOLVED_ORIGIN_PAIR_MOVE_CAP
        assert independent.RESOLVED_PAIR == RESOLVED_ORIGIN_PAIR_MOVE_CAP

    def test_the_pawn_and_home_rank_constants_match(self):
        from long_chess.bound import (
            FILES,
            FIRST_BLOCK_PAWN_LIMIT,
            MAX_PAWN_MOVES,
            PAWN_STEPS,
        )
        from long_chess.model import independent

        assert independent.PAWN_STEPS == PAWN_STEPS
        assert independent.FILES == FILES
        assert independent.MAX_PAWN_MOVES == MAX_PAWN_MOVES
        assert independent.FIRST_BLOCK_LIMIT == FIRST_BLOCK_PAWN_LIMIT

    def test_the_capture_ceilings_match(self):
        from long_chess.bound import MAX_CAPTURES, MAX_CAPTURES_DRAW
        from long_chess.model import independent

        assert independent.CAPTURE_CEILING[CHECKMATE] == MAX_CAPTURES
        assert independent.CAPTURE_CEILING[DRAW] == MAX_CAPTURES_DRAW

    def test_the_pawn_ceiling_matches_the_canonical_one(self):
        from long_chess.bound import FILES, pawn_moves_ceiling
        from long_chess.model import independent

        for resolved in range(FILES + 1):
            assert independent.pawn_ceiling(resolved) == pawn_moves_ceiling(resolved)


class TestTheCrossCheckIsInformative:
    """It reports a margin, not just a verdict, so the verdicts can be sanity
    checked against arithmetic rather than taken on faith."""

    def test_the_feasible_shape_reaches_exactly_118(self):
        result = analyse_independently(Shape(("B", "W", "B", "W")))
        assert result.max_pawn_moves == 96
        assert result.max_k == 118

    def test_black_white_black_falls_short_by_one_pawn(self):
        """90, not 96 — the six moves of the pawn spent opening the home rank.

        That leaves K at 115. The margin used to read 6 under the false
        `P ≤ 32 + 8f`, which charged this shape eight pawn captures it does not need;
        the honest coupling charges five, and the margin is 3.
        """
        result = analyse_independently(Shape(("B", "W", "B")))
        assert result.max_pawn_moves == 90
        assert result.max_k == 90 + 29 - 5 + 1 == 115
        assert 118 - result.max_k == 3

    def test_the_two_block_shapes_fall_short(self):
        """90 pawn moves, which needs five files resolved: 80 + 2×5.

        These read 54 and 84 while the checkmate branch forced the mated side to
        lose all fifteen units — a constraint that only holds at K = 118. The
        general maximum is higher, and still nowhere near 118.

        Note this is a *different* quantity from the counting proof's `P ≤ 54`
        for two blocks. That one is conditional on the K = 118 equality, which
        forces `C ≥ 29`; this maximises over every capture count.
        """
        for colours in (("B", "W"), ("W", "B")):
            result = analyse_independently(Shape(colours))
            assert result.max_pawn_moves == 90
            assert result.max_k == 90 + 23 - 5 + 1 == 109
            assert not result.feasible

    def test_a_single_block_is_hopeless(self):
        """Only one colour has a block, so only its eight pawns move at all —
        48 of the 96 are unreachable before anything else is considered — and
        only that colour captures, so at most the enemy's 15 units ever go:
        48 + 15 + 1 = 64.

        This read 71 while the checker counted captures of the blockless
        colour's own units — captures only an enemy critical move could make,
        in a shape with no enemy block. The CP model always excluded them
        structurally; the checker was looser, in the safe direction, and the
        inflated maximum was the visible cost.
        """
        for colours in (("B",), ("W",)):
            result = analyse_independently(Shape(colours))
            assert result.max_pawn_moves == 48 == 8 * 6
            assert result.max_k == 64 == 48 + 15 + 1
            assert "15 captures" in result.account
            assert not result.feasible


class TestShapeValidation:
    """`switches` reads S off the block count, which is only right when the
    blocks are maximal single-colour runs. A malformed tuple used to be
    accepted and silently miscounted; it is now rejected at construction."""

    def test_every_alternating_shape_still_passes(self):
        for shape in all_shapes(6):
            assert shape.switches >= 0

    def test_consecutive_same_colour_blocks_are_rejected(self):
        with pytest.raises(ValueError, match="must differ"):
            Shape(("B", "B", "W"))

    def test_an_empty_shape_is_rejected(self):
        with pytest.raises(ValueError, match="at least one block"):
            Shape(())

    def test_unknown_colours_are_rejected(self):
        with pytest.raises(ValueError, match="'B' or 'W'"):
            Shape(("B", "X"))


class TestTheModelImportsWithoutTheSolver:
    """The point of a solver-free cross-check is being there when the solver
    is not. `Shape` and the ending names used to live in `abstract`, which
    imports ortools at module scope, so this file was skipped wholesale on a
    solver-less install — the cross-check was untestable exactly when it was
    the only decider left."""

    def test_the_solver_free_names_come_from_shape(self):
        import long_chess.model.independent as independent
        import long_chess.model.shape as shape

        assert independent.Shape is shape.Shape
        assert independent.CHECKMATE is shape.CHECKMATE

    def test_shape_and_independent_do_not_import_ortools(self):
        """Read the imports off the source rather than simulating an absent
        ortools, which an installed one would make awkward. The package
        façade defers its ortools-backed names via `__getattr__`."""
        import ast
        import inspect

        import long_chess.model.independent as independent
        import long_chess.model.shape as shape

        for module in (shape, independent):
            tree = ast.parse(inspect.getsource(module))
            imported = {
                name.name.split(".")[0]
                for node in ast.walk(tree)
                if isinstance(node, ast.Import)
                for name in node.names
            } | {
                (node.module or "").split(".")[0]
                for node in ast.walk(tree)
                if isinstance(node, ast.ImportFrom) and node.level == 0
            }
            assert "ortools" not in imported, module.__name__


class TestTheCrossCheckCanDisagree:
    """A check that always says the same thing agrees with everything."""

    def test_relaxing_the_lemma_flips_its_verdict(self):
        """Not via a flag — by asking about a shape where the lemma does not
        bite. If the cross-check were hard-wired to say 'infeasible' for three
        blocks, this would fail."""
        assert not analyse_independently(Shape(("B", "W", "B"))).feasible
        assert analyse_independently(Shape(("B", "W", "B", "W"))).feasible

    def test_the_margin_tracks_the_pawn_total(self):
        """The arithmetic is live, not a lookup table. Each pawn move the shape
        cannot fit costs one from P, and the coupling gives some of it back."""
        three = analyse_independently(Shape(("B", "W", "B")))
        four = analyse_independently(Shape(("B", "W", "B", "W")))
        assert four.max_pawn_moves - three.max_pawn_moves == 6
        assert four.max_k - three.max_k == 3

    def test_a_lower_target_becomes_feasible(self):
        """The verdict is a comparison against a target, not a constant."""
        shape = Shape(("B", "W", "B"))
        assert not analyse_independently(shape, target_k=118).feasible
        assert analyse_independently(shape, target_k=115).feasible

    def test_pawn_captures_are_optimised_over_not_assumed(self):
        """A shape that cannot reach 96 pawn moves needs fewer files resolved,
        and must be charged fewer pawn captures. Assuming eight understated its K and
        was how the two methods first came to disagree."""
        result = analyse_independently(Shape(("B", "W", "B")))
        assert "files resolved" in result.account
        # 90 pawn moves needs 80 + 2f ≥ 90, so five files and no more.
        assert "5 files resolved" in result.account
        assert result.max_k == 90 + 29 - 5 + 1

    def test_the_charge_follows_the_pawn_total(self):
        """90 pawn moves needs 80 + 2f ≥ 90, so five files and no more — the
        charge is read off the total rather than fixed at eight."""
        result = analyse_independently(Shape(("B", "W")))
        assert "5 files resolved" in result.account
        assert result.max_pawn_moves == 90


class TestBothEndings:
    """A game need not end in checkmate. Draws were missing from the first
    version of the model, and they change two things at once."""

    def test_a_draw_may_take_all_thirty_pieces(self):
        """No mating material is needed, so the capture ceiling rises to 30 —
        which is why draws had to be checked separately at all."""
        from long_chess.bound import MAX_CAPTURES, MAX_CAPTURES_DRAW

        assert MAX_CAPTURES == 29 and MAX_CAPTURES_DRAW == 30

    def test_but_the_thirtieth_capture_ends_the_game(self):
        """King against king is dead material, so a 30-capture game gives up
        the closing segment. The trade is exactly even, which is the reason the
        extra capture buys a draw nothing — and why `C + T ≤ 30` covers both.
        """
        from long_chess.bound import MAX_CAPTURES, MAX_CAPTURES_DRAW

        take_everything = 96 + MAX_CAPTURES_DRAW - 8 + 0
        keep_one_back = 96 + MAX_CAPTURES - 8 + 1
        assert take_everything == keep_one_back == 118

        result = analyse_independently(Shape(("B", "W", "B", "W")), ending=DRAW)
        assert result.max_k == 118

    @pytest.mark.parametrize(
        "colours", [("B",), ("W",), ("B", "W"), ("W", "B"), ("B", "W", "B")]
    )
    @pytest.mark.parametrize("ending", ENDINGS)
    def test_no_two_switch_shape_works_under_either_ending(
        self, independent_results, colours, ending
    ):
        assert not independent_results[ending, colours].feasible

    @pytest.mark.parametrize("ending", ENDINGS)
    def test_the_bound_is_17697_under_either_ending(
        self, independent_results, ending: str
    ):
        best = min(
            shape.switches
            for shape in all_shapes(4)
            if independent_results[ending, shape.colours].feasible
        )
        assert best == 3
        assert 150 * 118 - best == 17_697


    def test_the_two_endings_reach_the_same_maximum_everywhere(
        self, independent_results
    ):
        """A draw's extra capture is paid for exactly by the closing segment it
        gives up, and not only at 118 — at every shape.

        These columns used to differ, but only because the checkmate branch was
        carrying a constraint that does not hold outside K = 118. With it gone
        the trade is visibly even all the way down, which is the same fact the
        `C + T ≤ 30` bound states.
        """
        for shape in all_shapes(4):
            mate = independent_results[CHECKMATE, shape.colours]
            draw = independent_results[DRAW, shape.colours]
            assert mate.max_k == draw.max_k, shape
            assert mate.feasible == draw.feasible, shape

    def test_the_ending_still_changes_what_is_allowed(self):
        """Equal maxima are not a sign the ending is ignored: a draw may take
        all 30 units, a checkmate at most 29."""
        from long_chess.model import independent

        assert independent.CAPTURE_CEILING[DRAW] == 30
        assert independent.CAPTURE_CEILING[CHECKMATE] == 29

    @pytest.mark.parametrize("bad", ["stalemate", "Draw", "", "mate"])
    def test_an_unknown_ending_is_rejected(self, bad: str):
        """Not silently read as a draw, which has the higher ceiling."""
        with pytest.raises(ValueError, match="ending must be one of"):
            analyse_independently(Shape(("B", "W", "B")), ending=bad)
