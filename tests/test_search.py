"""Critical events, the precedence graph, and the lower bound on S."""

from __future__ import annotations

import chess
import pytest

from long_chess.search import (
    EventKind,
    actor_counts,
    best_schedule,
    build_dependencies,
    extract_events,
    find_chains,
    king_capture_requirement,
    phases,
    schedule_from,
)
from long_chess.search.obstruction import QUIET_WHITE_PIECES
from long_chess.skeleton import analyse


@pytest.fixture(scope="module")
def events(compressed_skeleton):
    return extract_events(compressed_skeleton)


@pytest.fixture(scope="module")
def dependencies(events):
    return build_dependencies(events)


class TestEvents:
    def test_there_are_118(self, events):
        assert len(events) == 118

    def test_the_actor_split_is_sixty_fifty_eight(self, events):
        assert actor_counts(events) == {"B": 60, "W": 58}

    def test_every_actor_is_forced_by_the_moving_piece(
        self, events, compressed_skeleton
    ):
        """The observation the whole milestone rests on.

        A pawn move is made by that pawn's colour; a capture is made by the
        colour that does not own the victim. Nobody chooses. So the multiset of
        actors is fixed and S depends only on the order.
        """
        board = chess.Board(compressed_skeleton.start_fen)
        for event, segment in zip(events, compressed_skeleton.segments, strict=True):
            for move in segment.bridge_moves:
                board.push(move)
            piece = board.piece_at(segment.critical_move.from_square)
            assert piece.color == event.actor
            if event.is_capture:
                victim_square = segment.critical_move.to_square
                victim = board.piece_at(victim_square)
                if victim is not None:  # not en passant
                    assert victim.color != event.actor
            board.push(segment.critical_move)

    def test_there_are_exactly_eight_pawn_capture_events(self, events):
        """K ≤ 96 + 30 − 8: the 8 is pawn moves that are also captures."""
        pawn_captures = [e for e in events if e.kind is EventKind.PAWN_CAPTURE]
        assert len(pawn_captures) == 8

    def test_the_move_and_capture_counts_add_up_to_118(self, events):
        pawn_moves = sum(
            1
            for e in events
            if e.kind in (EventKind.PAWN, EventKind.PROMOTION, EventKind.PAWN_CAPTURE)
        )
        captures = sum(1 for e in events if e.is_capture)
        pawn_captures = sum(1 for e in events if e.kind is EventKind.PAWN_CAPTURE)
        mates = sum(1 for e in events if e.kind is EventKind.MATE)
        assert pawn_moves == 96
        assert captures == 29
        assert pawn_moves + captures - pawn_captures + mates == 118

    def test_the_observed_phases(self, events):
        assert [(c, hi - lo + 1) for c, lo, hi in phases(events)] == [
            ("B", 10),
            ("W", 49),
            ("B", 50),
            ("W", 9),
        ]


class TestDependencies:
    def test_the_graph_is_sound(self, events, dependencies):
        """Every precedence must hold in the actual game.

        This is the check that makes the bound mean anything. An edge the real
        game violates is not a necessary condition, and a graph containing one
        would give a bound that is simply wrong.
        """
        violated = [d for d in dependencies if d.before >= d.after]
        assert violated == []

    def test_a_pawn_advances_in_order(self, dependencies):
        assert any(d.reason == "a pawn advances in order" for d in dependencies)

    def test_a_piece_moves_before_it_is_captured(self, dependencies):
        assert any(
            d.reason == "a piece moves before it is captured" for d in dependencies
        )

    def test_blocking_is_deliberately_omitted(self, dependencies):
        """A pawn cannot advance onto an occupied square, which is real and
        strong — and left out, because it depends on where everything is rather
        than on the events. Omitting a constraint only weakens the bound, so
        under-including is the safe direction."""
        assert not any("block" in d.reason for d in dependencies)


class TestLowerBound:
    def test_neither_starting_colour_does_better_than_three(self, events, dependencies):
        black = schedule_from(events, dependencies, chess.BLACK)
        white = schedule_from(events, dependencies, chess.WHITE)
        assert black.blocks == 4 and black.switches == 3
        assert white.blocks == 3 and white.switches == 3

    def test_the_bound_is_three(self, events, dependencies):
        assert best_schedule(events, dependencies).switches == 3

    def test_the_known_construction_is_optimal_for_this_multiset(
        self, events, dependencies, compressed_skeleton
    ):
        bound = best_schedule(events, dependencies).switches
        assert analyse(compressed_skeleton).actor_switches == bound == 3

    def test_the_bound_caps_the_length_at_17697(self, events, dependencies):
        bound = best_schedule(events, dependencies).switches
        assert 150 * len(events) - bound == 17_697

    def test_a_schedule_respects_every_precedence(self, events, dependencies):
        schedule = best_schedule(events, dependencies)
        block = dict(zip((e.index for e in events), schedule.block_of, strict=True))
        for dependency in dependencies:
            assert block[dependency.before] <= block[dependency.after]

    def test_every_block_is_one_colour(self, events, dependencies):
        schedule = best_schedule(events, dependencies)
        colours: dict[int, chess.Color] = {}
        for event, index in zip(events, schedule.block_of, strict=True):
            assert colours.setdefault(index, event.actor) == event.actor


class TestObstruction:
    def test_the_chains_exist(self, events):
        chains = find_chains(events)
        assert len(chains) == 8

    def test_each_chain_really_alternates(self, events):
        for chain in find_chains(events):
            assert chain.white_move.actor == chess.WHITE
            assert chain.black_capture.actor == chess.BLACK
            assert chain.white_recapture.actor == chess.WHITE

    def test_each_chain_is_a_real_precedence_path(self, events):
        """The middle event captures the first's mover; the last captures the
        middle's. Both are 'a piece moves before it is captured'."""
        for chain in find_chains(events):
            assert chain.black_capture.victim == chain.white_move.mover
            assert chain.white_recapture.victim == chain.black_capture.mover

    def test_every_black_capturer_is_itself_captured(self, events):
        """Black ends with only its king, so nothing else survives. That is
        what turns each W→B into a W→B→W."""
        captured = {e.victim for e in events if e.victim is not None}
        capturers = {e.mover for e in events if e.is_capture and e.actor == chess.BLACK}
        assert capturers <= captured

    def test_the_king_capture_requirement(self, events):
        requirement = king_capture_requirement(events)
        assert requirement.black_captures_needed == 14
        assert requirement.quiet_white_pieces_available == QUIET_WHITE_PIECES == 7
        assert requirement.forced_king_captures == 7
        assert requirement.actual_king_captures == 0
        assert not requirement.satisfied
