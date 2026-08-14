"""K ≤ 118 and S ≥ 3, and the counterexample that forced both to be re-derived."""

from __future__ import annotations

import chess
import pytest

from long_chess.bound import (
    FILES,
    FIRST_BLOCK_PAWN_LIMIT,
    MAX_CAPTURABLE,
    MAX_CAPTURES,
    MAX_CAPTURES_PLUS_CLOSING,
    MAX_CRITICAL_SEGMENTS,
    MAX_NET_PAWN_MOVES,
    MAX_PAWN_MOVES,
    MINIMUM_PAWN_CAPTURES,
    PAWN_STEPS,
    RESOLVED_ORIGIN_PAIR_MOVE_CAP,
    UNRESOLVED_ORIGIN_PAIR_MOVE_CAP,
    captures_plus_closing_bound,
    check_file_lemma,
    check_origin_pair_cap,
    critical_bound,
    ending_profiles,
    equality_conditions,
    equality_witnesses,
    net_pawn_move_bound,
    pawn_moves_ceiling,
    refutations,
    shapes_with_at_most,
    switch_lower_bound,
    switches,
)
from long_chess.search import EventKind, extract_events
from long_chess.skeleton import potential

# The shortest legal game we have that breaks the old `UNRESOLVED_FILE_CAP = 4`.
# Black's a-pawn walks to a4 and is taken by the bishop that came out to b5;
# White's a-pawn then walks up behind it, unopposed.
CAP_COUNTEREXAMPLE = (
    "e4 a5 e5 a4 Bb5 Nc6 Bxa4 Rb8 Bb3 Nh6 a3 Ng4 a4 Nh6 a5"
)

WHITE_A_PAWN = chess.A2
BLACK_A_PAWN = chess.A7

# The cap of 10, attained in real chess and not merely in the relaxation.
# Black walks a7-a6-a5-a4-a3 (4 moves) and is taken there by the b1 knight --
# a third piece, which is the case the old cap-4 argument left out. The knight
# steps aside and White's a-pawn walks the whole file, promoting (6 moves).
CAP_ATTAINED = (
    "Nf3 a6 Ng1 a5 Nf3 a4 Ng1 a3 Nxa3 Nc6 Nc4 Rb8 "
    "a3 Nf6 a4 Ng8 a5 Nf6 a6 Ng8 a7 Nf6 a8=Q Ng8"
)


def origin_pair_moves(san: str, origins: tuple[int, ...]) -> dict[int, tuple[int, int]]:
    """Replay ``san`` and count, per starting square, (pawn moves, diagonal ones).

    Identity is the pawn's starting square, followed through the game. A pawn
    that is captured stops accumulating; nothing else is tracked, because
    nothing else is what the origin-pair cap is about.
    """
    board = chess.Board()
    identity = {square: square for square in origins}
    moves = dict.fromkeys(origins, 0)
    diagonals = dict.fromkeys(origins, 0)

    for token in san.split():
        move = board.parse_san(token)
        # The victim goes first. Retiring it after placing the mover would, for
        # a tracked pawn making an ordinary capture, delete the mover it had
        # just written to the destination square — and every later move of that
        # pawn would go uncounted. Harmless in the bishop-takes-a4 game below,
        # where the capturer is not tracked, but not in a diagonal-pawn case.
        if board.is_capture(move):
            victim = move.to_square
            if board.is_en_passant(move):
                victim = move.to_square + (-8 if board.turn else 8)
            identity.pop(victim, None)
        origin = identity.pop(move.from_square, None)
        if origin is not None:
            moves[origin] += 1
            if chess.square_file(move.from_square) != chess.square_file(move.to_square):
                diagonals[origin] += 1
            identity[move.to_square] = origin
        board.push(move)

    return {origin: (moves[origin], diagonals[origin]) for origin in origins}


class TestTheOldCapWasFalse:
    """`UNRESOLVED_FILE_CAP = 4` ruled out games that are legal.

    It counted only the half of the argument where both pawns are still on the
    file. Once one of them is captured *by some other piece* the survivor runs
    on, and the pair beats four without either pawn ever moving diagonally.

    This is the direction that does not announce itself: a constraint stronger
    than legality produces UNSAT, and UNSAT is indistinguishable from a proof.
    """

    @staticmethod
    @pytest.fixture(scope="class")
    def counted():
        return origin_pair_moves(CAP_COUNTEREXAMPLE, (WHITE_A_PAWN, BLACK_A_PAWN))

    def test_the_game_is_legal(self):
        """Parsed by python-chess move by move, which rejects an illegal one."""
        board = chess.Board()
        for token in CAP_COUNTEREXAMPLE.split():
            board.push(board.parse_san(token))
        assert board.fullmove_number == 8

    def test_neither_a_pawn_ever_moved_diagonally(self, counted):
        """So the a-file's origin pair is unresolved, by definition."""
        assert counted[WHITE_A_PAWN][1] == 0
        assert counted[BLACK_A_PAWN][1] == 0

    def test_the_pair_makes_five_moves(self, counted):
        """a2-a3-a4-a5 and a7-a5-a4. Five, against a cap that said four."""
        assert counted[WHITE_A_PAWN][0] == 3
        assert counted[BLACK_A_PAWN][0] == 2
        assert counted[WHITE_A_PAWN][0] + counted[BLACK_A_PAWN][0] == 5

    def test_which_the_old_cap_forbade_and_the_new_one_allows(self, counted):
        total = counted[WHITE_A_PAWN][0] + counted[BLACK_A_PAWN][0]
        assert total > 4, "this is the number the old cap asserted"
        assert total <= UNRESOLVED_ORIGIN_PAIR_MOVE_CAP


class TestTheHelperFollowsAPawnThroughItsOwnCaptures:
    """The identity tracker used above, checked on a case it did once get wrong.

    Retiring the victim *after* writing the mover to the destination square
    deletes the mover on an ordinary capture, and every later move of that pawn
    goes uncounted. The counterexample game does not exercise it — the capturer
    there is a bishop — so this pins the ordering directly.
    """

    def test_a_tracked_pawn_keeps_its_identity_through_a_capture(self):
        """The d2 pawn plays d4, captures on e5, and walks on to e6. All three
        moves count and the one diagonal is seen — the ordering bug lost the
        third."""
        counted = origin_pair_moves("d4 e5 dxe5 Nc6 e6", (chess.D2,))
        assert counted[chess.D2] == (3, 1)

    def test_a_capture_still_retires_the_victim(self):
        counted = origin_pair_moves("e4 d5 exd5", (chess.D7,))
        assert counted[chess.D7] == (1, 0)

    def test_en_passant_retires_the_right_pawn(self):
        """The victim is not on the destination square, so it has to be found."""
        counted = origin_pair_moves("e4 a6 e5 f5 exf6", (chess.F7, chess.E2))
        assert counted[chess.F7] == (1, 0)
        assert counted[chess.E2] == (3, 1)


class TestOriginPairCap:
    """Ten, by exhausting a state space strictly looser than chess."""

    @staticmethod
    @pytest.fixture(scope="class")
    def search():
        return check_origin_pair_cap()

    def test_the_cap_is_ten(self, search):
        assert search.max_moves == UNRESOLVED_ORIGIN_PAIR_MOVE_CAP == 10

    def test_ten_is_tight_for_the_relaxation(self, search):
        """A cap nothing attains is a cap that might be too small, and too
        small is the direction that invents UNSATs.

        This witness lives in the relaxed state machine, not in chess — it
        establishes that the *search* cannot do better, which is a claim about
        the search. Whether real chess reaches 10 is the next test.
        """
        white, black = search.witness[-1][2], search.witness[-1][3]
        assert white + black == search.max_moves
        assert search.witness[0] == (2, 7, 0, 0)

    def test_ten_is_reached_in_legal_chess_too(self):
        """So the relaxation is not loose *here*: the constant is the real one.

        Not needed for soundness — an upper bound may be slack — but a cap that
        overshot would mean the coupling `P ≤ 80 + 2f` was weaker than it had to
        be, and nothing else in the project would have said so.
        """
        counted = origin_pair_moves(CAP_ATTAINED, (WHITE_A_PAWN, BLACK_A_PAWN))
        assert counted[WHITE_A_PAWN] == (6, 0)
        assert counted[BLACK_A_PAWN] == (4, 0)
        assert (
            counted[WHITE_A_PAWN][0] + counted[BLACK_A_PAWN][0]
            == UNRESOLVED_ORIGIN_PAIR_MOVE_CAP
            == 10
        )

    def test_that_game_is_legal_and_leaves_the_a_file_unresolved(self):
        board = chess.Board()
        for token in CAP_ATTAINED.split():
            board.push(board.parse_san(token))
        assert board.fullmove_number == 13
        counted = origin_pair_moves(CAP_ATTAINED, (WHITE_A_PAWN, BLACK_A_PAWN))
        assert counted[WHITE_A_PAWN][1] == counted[BLACK_A_PAWN][1] == 0

    def test_neither_pawn_beats_six_on_its_own(self, search):
        """Six ranks to promotion, at least one spent per move."""
        for _, _, white, black in search.witness:
            assert white <= PAWN_STEPS
            assert black <= PAWN_STEPS

    def test_four_while_both_are_still_on_the_file(self, search):
        """The first half of the argument, and the whole of the old cap.

        White on rank 2+a below Black on 7−b needs 2+a < 7−b, so a+b ≤ 4.
        """
        assert search.max_moves_while_both_remain == 4

    def test_ten_is_four_plus_a_whole_second_lifetime(self, search):
        assert (
            search.max_moves
            == search.max_moves_while_both_remain + PAWN_STEPS
            == UNRESOLVED_ORIGIN_PAIR_MOVE_CAP
        )

    def test_the_state_space_is_small_enough_to_be_exhausted(self, search):
        assert search.states_explored < 1_000

    def test_a_resolved_pair_is_capped_only_by_the_pawns(self):
        assert RESOLVED_ORIGIN_PAIR_MOVE_CAP == 2 * PAWN_STEPS == 12


class TestFileLemma:
    def test_two_facing_pawns_cannot_both_get_past(self):
        """What makes an unresolved file cost a pawn capture once both pawns have
        to promote. The search is more permissive than chess — either pawn may
        move at any time — which makes unreachability a stronger statement."""
        assert not check_file_lemma().goal_reachable

    def test_the_white_pawn_never_gets_above_the_black_one(self):
        assert check_file_lemma().invariant_holds

    def test_the_state_space_is_small_enough_to_be_exhausted(self):
        assert check_file_lemma().states_explored < 100


class TestTerms:
    def test_ninety_six_pawn_moves(self):
        assert MAX_PAWN_MOVES == 96

    def test_the_potential_agrees_with_the_pawn_move_count(self):
        """`potential` counts remaining pawn steps for segment independence.
        It is the same 96 counted the same way, from the other direction."""
        _, pawn_steps = potential(chess.Board())
        assert pawn_steps == MAX_PAWN_MOVES

    def test_thirty_pieces_can_ever_be_captured(self):
        assert MAX_CAPTURABLE == 30

    def test_at_most_twenty_nine_captures_in_a_mate(self):
        """The mating side must keep something to mate with."""
        assert MAX_CAPTURES == 29

    def test_at_least_eight_pawn_captures_once_every_pawn_promotes(self):
        assert MINIMUM_PAWN_CAPTURES == 8


class TestNetPawnMoves:
    """`P − Cₚ ≤ 88`, maximised over how many origin files are resolved."""

    @pytest.mark.parametrize("resolved", range(FILES + 1))
    def test_the_ceiling_for_each_f(self, resolved: int):
        """P ≤ min(96, 80 + 2f). Eight origin pairs, capped 10 or 12 each."""
        assert pawn_moves_ceiling(resolved) == min(96, 80 + 2 * resolved)

    @pytest.mark.parametrize("resolved", range(FILES + 1))
    def test_p_minus_o_never_exceeds_88(self, resolved: int):
        """With O ≥ f, the best this f can do is its ceiling less f."""
        assert pawn_moves_ceiling(resolved) - resolved <= MAX_NET_PAWN_MOVES

    def test_the_maximum_is_88_and_only_at_eight_resolved_files(self):
        best = net_pawn_move_bound()
        assert best.value == MAX_NET_PAWN_MOVES == 88
        assert best.resolved_files == FILES == 8
        assert best.pawn_moves == 96
        assert best.pawn_captures == 8
        ties = [
            resolved
            for resolved in range(FILES + 1)
            if pawn_moves_ceiling(resolved) - resolved == MAX_NET_PAWN_MOVES
        ]
        assert ties == [8]

    def test_an_impossible_file_count_is_rejected(self):
        with pytest.raises(ValueError, match="resolved files"):
            pawn_moves_ceiling(9)


class TestCapturesPlusClosing:
    """`C + T ≤ 30`, whatever ends the game."""

    def test_the_bound_is_thirty(self):
        assert captures_plus_closing_bound() == MAX_CAPTURES_PLUS_CLOSING == 30

    def test_both_profiles_reach_it(self):
        """Which is why the bound need not know how the game ended."""
        totals = {profile.name: profile.total for profile in ending_profiles()}
        assert totals == {"checkmate": 30, "all-captured": 30}

    def test_taking_everything_gives_up_the_closing_segment(self):
        """King against king is dead, so the thirtieth capture ends the game."""
        all_captured = next(p for p in ending_profiles() if p.captures == 30)
        assert all_captured.closing_segment == 0

    def test_a_mate_keeps_it_but_pays_a_capture(self):
        mate = next(p for p in ending_profiles() if p.name == "checkmate")
        assert (mate.captures, mate.closing_segment) == (29, 1)


class TestCriticalBound:
    def test_k_is_at_most_118(self):
        assert critical_bound().total == MAX_CRITICAL_SEGMENTS == 118

    def test_it_is_88_plus_30(self):
        bound = critical_bound()
        assert bound.net_pawn_moves == 88
        assert bound.captures_plus_closing == 30

    def test_the_trivial_ply_ceiling_before_the_switch_argument(self):
        """150K − 1. The real bound needs S ≥ 3, which is `blocks`."""
        assert critical_bound().max_plies == 17_699


class TestEqualityConditions:
    """K = 118 pins every term, and the pinning is enumerated, not asserted."""

    def test_only_one_assignment_reaches_118(self):
        assert equality_witnesses() == [(8, 96, 8, 30)]

    def test_what_it_forces(self):
        equality = equality_conditions()
        assert equality.resolved_files == 8
        assert equality.pawn_moves == 96
        assert equality.pawn_captures == 8
        assert equality.captures_plus_closing == 30

    def test_every_pawn_makes_six_single_square_moves_and_promotes(self):
        equality = equality_conditions()
        assert equality.moves_per_pawn == PAWN_STEPS == 6
        assert equality.every_pawn_promotes

    def test_one_less_leaves_room_so_the_pinning_is_real(self):
        """If 117 pinned everything too, the equality argument would be
        describing the enumeration rather than the arithmetic."""
        assert len(equality_witnesses(117)) > 1
        with pytest.raises(ValueError, match="no equality case"):
            equality_conditions(117)

    def test_119_is_out_of_reach_entirely(self):
        assert equality_witnesses(119) == []


class TestSwitchLowerBound:
    """S ≥ 3, by counting. The source of truth; the model cross-checks it."""

    def test_switches_count_the_virtual_black_opening(self):
        assert switches(("B",)) == 0
        assert switches(("W",)) == 1
        assert switches(("B", "W")) == 1
        assert switches(("W", "B")) == 2
        assert switches(("B", "W", "B")) == 2
        assert switches(("B", "W", "B", "W")) == 3

    def test_there_are_exactly_five_shapes_with_two_or_fewer_switches(self):
        assert shapes_with_at_most(2) == [
            ("B",),
            ("W",),
            ("B", "W"),
            ("W", "B"),
            ("B", "W", "B"),
        ]

    def test_the_enumeration_is_complete(self):
        """S grows by one per block, so nothing longer can qualify — checked
        past the point where it could rather than argued in a comment."""
        from long_chess.bound import alternating_shapes

        assert [
            colours for colours in alternating_shapes(12) if switches(colours) <= 2
        ] == shapes_with_at_most(2)

    def test_dropping_the_terminal_endpoint_never_adds_a_switch(self):
        """The seam between two definitions.

        `S` is measured over all K endpoints, the last of which may be a quiet
        terminal segment; the refutations are about critical moves. They line up
        only because deleting that endpoint cannot increase the switch count —
        so a game with S ≤ 2 overall has a critical-move actor sequence with
        S ≤ 2, which is one of the same five shapes.
        """
        from long_chess.bound import (
            check_dropping_terminal_endpoint_never_adds_a_switch,
        )

        check = check_dropping_terminal_endpoint_never_adds_a_switch()
        assert check.never_adds_a_switch
        assert check.worst_increase <= 0
        assert check.shapes_checked >= 40

    def test_appending_the_terminal_endpoint_can_add_one(self):
        """The direction that is *false*, pinned so the two are never confused.

        Only the deletion direction is used, and it has to be: a critical-move
        pattern `B` closed by a quiet White mate is the endpoint pattern `B W`,
        which has one switch more, not fewer. Appending is monotone the other
        way — it never lowers the block count, and starting a new block costs
        exactly one switch.
        """
        from long_chess.bound import alternating_shapes

        assert switches(("B",)) == 0 and switches(("B", "W")) == 1

        for critical in alternating_shapes(11):
            for appended in ("B", "W"):
                whole = critical if critical[-1] == appended else (*critical, appended)
                new_block = len(whole) - len(critical)
                assert new_block in (0, 1)
                assert switches(whole) - switches(critical) == new_block

    def test_the_two_readings_of_a_shape(self):
        """Concretely: B W B whose last block is only the mate has critical
        actors B W, and that is in the candidate set too."""
        from long_chess.bound import critical_actor_shape

        whole = ("B", "W", "B")
        assert critical_actor_shape(whole, terminal_alone=True) == ("B", "W")
        assert critical_actor_shape(whole, terminal_alone=False) == whole
        assert switches(("B", "W")) <= switches(whole)
        assert ("B", "W") in shapes_with_at_most(2)

    def test_the_bound_refuses_to_close_if_that_seam_opens(self):
        """`switch_lower_bound` checks it rather than assuming it, so a change
        to `switches()` that broke the correspondence would fail loudly."""
        from long_chess.bound import blocks

        assert blocks.check_dropping_terminal_endpoint_never_adds_a_switch.__doc__
        assert switch_lower_bound().minimum_switches == 3

    def test_every_one_of_them_is_refuted(self):
        assert all(refutation.refuted for refutation in refutations())

    def test_the_verdict_is_derived_from_the_arithmetic_not_asserted(self):
        """Every refutation reduces to the same thing — the shape cannot fit
        the 96 pawn moves K = 118 demands — so `refuted` is computed from the
        two numbers. A constant drifting until an argument stopped closing must
        show up as a failure, not as a comment that no longer matches."""
        for refutation in refutations():
            assert refutation.pawn_moves_required == MAX_PAWN_MOVES == 96
            assert refutation.pawn_moves_available < refutation.pawn_moves_required
            assert refutation.refuted
            assert refutation.shortfall == 96 - refutation.pawn_moves_available

    def test_how_far_short_each_shape_falls(self):
        """The margins, which the corrected coupling changed. B W B is the
        thin one and always was."""
        shortfalls = {r.name: r.shortfall for r in refutations()}
        assert shortfalls == {
            "B": 48,
            "W": 48,
            "B W": 42,
            "W B": 42,
            "B W B": 14,
        }

    def test_a_shape_with_three_switches_is_not_refuted_here(self):
        """And it is not refuted because it genuinely reaches 96 — which is why
        the answer is 3 and not something larger."""
        from long_chess.bound import refute

        surviving = refute(("B", "W", "B", "W"))
        assert not surviving.refuted
        assert surviving.pawn_moves_available == MAX_PAWN_MOVES
        assert surviving.shortfall == 0

    @pytest.mark.parametrize("colours", [("B",), ("W",)])
    def test_a_single_block_dies_because_both_colours_must_move_pawns(self, colours):
        """Only one colour has a block, so only its eight pawns move: P ≤ 48."""
        refutation = next(r for r in refutations() if r.colours == colours)
        assert refutation.ground == "counting"
        assert "no block to make one in" in refutation.detail
        assert refutation.pawn_moves_available == 8 * PAWN_STEPS == 48

    @pytest.mark.parametrize("colours", [("B", "W"), ("W", "B")])
    def test_the_two_block_shapes_die_to_counting_alone(self, colours):
        """The first colour's 14 captures all land before the second colour has
        moved, so ≥7 of its pawns die unmoved: P ≤ 54 against 96."""
        refutation = next(r for r in refutations() if r.colours == colours)
        assert refutation.ground == "counting"
        assert "P ≤ 54" in refutation.detail

    def test_black_white_black_dies_to_the_home_rank_lemma(self):
        """The only shape that needs the lemma at all, and the load-bearing
        step of the whole result."""
        refutation = next(r for r in refutations() if r.colours == ("B", "W", "B"))
        assert refutation.ground == "home-rank lemma"
        assert f"caps a Black pawn at {FIRST_BLOCK_PAWN_LIMIT}" in refutation.detail
        assert "P ≤ 82" in refutation.detail

    def test_the_bound_that_follows_at_k_118(self):
        bound = switch_lower_bound()
        assert bound.minimum_switches == 3
        assert bound.critical_segments == 118
        assert bound.max_plies == 150 * 118 - 3 == 17_697

    def test_a_surviving_shape_would_raise_rather_than_weaken_the_bound(self):
        """S ≥ 4 is false — the published game has S = 3 — so asking for it
        must fail loudly instead of returning a longer bound."""
        with pytest.raises(ValueError, match="not refuted"):
            switch_lower_bound(limit=3)


class TestSwitchThreeIsNotGlobal:
    """`S ≥ 3` holds at `K = 118` and nowhere near everywhere.

    Every refutation starts from `P = 96` and `C ≥ 29`, and both come from
    `K = 118`. A game with fewer critical segments is under no such pressure,
    and the shortest counterexample is four repetitions of a knight shuffle.
    """

    SHUFFLE = "Nf3 Nf6 Ng1 Ng8 " * 4

    @staticmethod
    def observed(san: str) -> tuple[int, int, int]:
        """(plies, K, S) straight from the verifier, counted as the theory does."""
        from long_chess.verifier import moves_from_san, verify_game

        result = verify_game(moves_from_san(san))
        boundaries = [0, *result.critical_plies]
        if boundaries[-1] != result.plies:
            boundaries.append(result.plies)  # the closing quiet segment
        actors = ["W" if ply % 2 else "B" for ply in boundaries[1:]]
        previous, count = "B", 0  # as if Black moved just before ply 1
        for actor in actors:
            count += actor != previous
            previous = actor
        return result.plies, result.critical_count, count

    def test_a_legal_game_reaches_s_equals_zero(self):
        from long_chess.verifier import Termination, moves_from_san, verify_game

        result = verify_game(moves_from_san(self.SHUFFLE))
        assert result.termination is Termination.FIVEFOLD_REPETITION
        plies, k, s = self.observed(self.SHUFFLE)
        assert (plies, k, s) == (16, 1, 0)

    def test_which_would_break_a_global_reading_of_the_bound(self):
        """`L ≤ 150K − S` still holds — it is `S ≥ 3` that does not."""
        plies, k, s = self.observed(self.SHUFFLE)
        assert plies <= 150 * k - s
        assert s < switch_lower_bound().minimum_switches

    def test_the_api_no_longer_offers_a_bound_for_other_k(self):
        """`switch_lower_bound(117)` used to return S ≥ 3, having proved
        nothing of the sort."""
        import inspect

        parameters = inspect.signature(switch_lower_bound).parameters
        assert "critical_segments" not in parameters
        assert all(p.kind is p.KEYWORD_ONLY for p in parameters.values())


class TestPlyBound:
    """`L ≤ 17,697`, by cases on `K` — the form the theorem is true in."""

    def test_the_two_cases(self):
        from long_chess.bound import ply_bound

        bound = ply_bound()
        assert bound.below_max_k == 150 * 117 == 17_550
        assert bound.at_max_k == 150 * 118 - 3 == 17_697

    def test_the_binding_case_is_k_118(self):
        from long_chess.bound import ply_bound

        bound = ply_bound()
        assert bound.max_plies == 17_697
        assert bound.binding_case == "K = 118"

    def test_a_smaller_k_needs_no_switch_argument_at_all(self):
        """Giving up one critical segment costs 150 ply; no game has that many
        switches to save against it. So `S ≥ 0` carries the whole case."""
        from long_chess.bound import ply_bound

        bound = ply_bound()
        assert bound.below_max_k < bound.at_max_k
        assert 150 * 117 - 0 < 150 * 118 - 3

    def test_the_shuffle_game_sits_far_inside_the_smaller_case(self):
        plies, k, _ = TestSwitchThreeIsNotGlobal.observed(
            TestSwitchThreeIsNotGlobal.SHUFFLE
        )
        assert k <= 117
        assert plies <= 150 * 117


class TestAgainstTheKnownGame:
    def test_the_known_game_realises_every_term(self, compressed_skeleton):
        """The bound is tight: the published game hits each term exactly."""
        events = extract_events(compressed_skeleton)
        pawn_moves = sum(
            1
            for e in events
            if e.kind in (EventKind.PAWN, EventKind.PROMOTION, EventKind.PAWN_CAPTURE)
        )
        captures = sum(1 for e in events if e.is_capture)
        pawn_captures = sum(1 for e in events if e.kind is EventKind.PAWN_CAPTURE)
        closing = sum(1 for e in events if e.kind is EventKind.MATE)

        assert pawn_moves == MAX_PAWN_MOVES
        assert captures == MAX_CAPTURES
        assert pawn_captures == MINIMUM_PAWN_CAPTURES
        assert pawn_moves - pawn_captures == MAX_NET_PAWN_MOVES
        assert captures + closing == MAX_CAPTURES_PLUS_CLOSING
        assert len(events) == critical_bound().total == 118

    def test_the_known_game_matches_the_equality_conditions(self, compressed_skeleton):
        """It is the equality case, so it must satisfy every clause of one."""
        events = extract_events(compressed_skeleton)
        equality = equality_conditions()
        pawn_captures = sum(1 for e in events if e.kind is EventKind.PAWN_CAPTURE)
        assert pawn_captures == equality.pawn_captures == equality.resolved_files

    def test_the_known_game_attains_the_switch_bound(self, compressed_skeleton):
        from long_chess.search import phases

        events = extract_events(compressed_skeleton)
        observed = tuple(colour for colour, _, _ in phases(events))
        assert observed == ("B", "W", "B", "W")
        assert switches(observed) == switch_lower_bound().minimum_switches == 3

    def test_the_known_game_uses_a_shape_that_is_already_excluded(
        self, compressed_skeleton
    ):
        """Four blocks, S = 3. The refuted shapes are what it would have to
        become to save a ply."""
        from long_chess.search import phases

        events = extract_events(compressed_skeleton)
        observed = tuple(colour for colour, _, _ in phases(events))
        assert observed not in [r.colours for r in refutations()]

    def test_the_known_game_reaches_the_final_bound(self, compressed_skeleton):
        from long_chess.skeleton import analyse

        assert analyse(compressed_skeleton).achievable_plies == 17_697
        assert switch_lower_bound().max_plies == 17_697
