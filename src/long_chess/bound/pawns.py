"""Why K ≤ 118, re-derived rather than taken on trust.

The whole project sits on this number, and it now comes from one identity that
does not care how the game ends:

    K = (P − Cₚ) + (C + T)  ≤  88 + 30  =  118

with

    P   pawn moves
    C   captures
    Cₚ  pawn captures — moves that are both, i.e. diagonal pawn captures
    T   the closing segment: 1 if quiet moves follow the last critical move,
        else 0

`K` appears as an *upper* bound, so every term above the line needs an upper
bound and every term below it a **lower** bound. Overestimating `Cₚ` would
narrow the bound without justification — it would rule out games that are in
fact legal.

`P − Cₚ ≤ 88` is the half that is easy to get wrong, and an earlier version of
this module did get it wrong; see :data:`UNRESOLVED_ORIGIN_PAIR_MOVE_CAP` and
``tests/test_defects.py::TestTheUnresolvedPairCapWasFalse``, which pins the
correction.
"""

from __future__ import annotations

from dataclasses import dataclass

FILES = 8
PAWN_STEPS = 6
"""Squares a pawn crosses from its home rank to promotion."""

MAX_PAWN_MOVES = 2 * FILES * PAWN_STEPS
"""96. Eight pawns a side, six steps each, and no pawn can do better."""

MAX_CAPTURABLE = 30
"""Pieces that can ever be captured: 32 on the board, less the two kings."""

MAX_CLOSING_SEGMENT = 1
"""T is a segment count, and there is at most one segment after the last
critical move."""

MAX_CAPTURES = 29
"""At most 29 captures **in a game that ends in checkmate**.

Neither king can be taken, which leaves 30. And the side that gives mate has to
keep something to give it with — a lone king cannot mate — so at least one of
the 30 survives. 29 is reached: the known game ends king and queen against king.
"""

MAX_CAPTURES_DRAW = MAX_CAPTURABLE
"""At most 30 captures in a game that ends in a draw.

No mating material is needed, so every non-king piece may go. But taking the
thirtieth leaves king against king, which is dead material and ends the game on
the spot — so a game with 30 captures has **no moves after its last critical
one**, and gives up the closing segment that a shorter-capture game keeps.

That trade is exactly even, which is why draws do not beat checkmates. It is
also why the source of truth for `K` is `C + T ≤ 30` rather than either profile
on its own — see :func:`captures_plus_closing_bound`.
"""


@dataclass(frozen=True, slots=True)
class FileLemma:
    """Two pawns facing each other on a file cannot both get past.

    Machine-checked below rather than asserted, because the whole pawn-capture term
    rests on it.
    """

    states_explored: int
    goal_reachable: bool
    invariant_holds: bool
    """Whether the White pawn stays strictly below the Black one throughout."""


def check_file_lemma() -> FileLemma:
    """Exhaust one file with both pawns on it and no sideways moves allowed.

    The White pawn starts on rank 2 heading for rank 8, the Black pawn on rank
    7 heading for rank 1. Pushes of one or two squares, a double only from
    home, neither able to move onto or through the other.

    The search is deliberately *more* permissive than chess: either pawn may
    move at any time, ignoring whose turn it is. Showing the goal unreachable
    under a relaxation is a stronger statement than showing it for the real
    rules.
    """
    start = (2, 7)
    seen = {start}
    frontier = [start]
    invariant_holds = True

    while frontier:
        white, black = frontier.pop()
        if white >= black:
            invariant_holds = False

        moves: list[tuple[int, int]] = []
        if white < 8 and white + 1 != black:
            moves.append((white + 1, black))
            if white == 2 and white + 2 != black:
                moves.append((white + 2, black))
        if black > 1 and black - 1 != white:
            moves.append((white, black - 1))
            if black == 7 and black - 2 != white:
                moves.append((white, black - 2))

        for state in moves:
            if state not in seen:
                seen.add(state)
                frontier.append(state)

    return FileLemma(
        states_explored=len(seen),
        goal_reachable=(8, 1) in seen,
        invariant_holds=invariant_holds,
    )


@dataclass(frozen=True, slots=True)
class HomeRankLemma:
    """How far a pawn gets while the enemy pawns have not moved.

    Not far. The enemy's home rank is eight pawns wide with nothing between
    them, so a pawn arriving there can neither push through nor step aside —
    every square it could go to holds an enemy pawn, and taking one is what the
    lemma forbids.
    """

    reachable_ranks: tuple[int, ...]
    furthest_rank: int
    moves_available: int


FIRST_BLOCK_PAWN_LIMIT = 4
"""Moves a pawn can make before the enemy pawns have moved at all.

Rank 7 down to rank 3 for Black, rank 2 up to rank 6 for White. Computed by
:func:`check_home_rank_lemma`.
"""


def check_home_rank_lemma() -> HomeRankLemma:
    """Exhaust where a Black pawn can go while White's pawns sit on rank 2.

    Rules, all of them more generous than chess:

    - the pawn may move to the square ahead if it is empty, or diagonally
      forward onto any enemy piece;
    - White's pawns never move, because moving one is a White critical move and
      the block being modelled has none;
    - White's pawns are never captured, because a pawn taken before it has
      moved gives up all six of its moves, and ``P = 96`` needs every one;
    - the Black pawn may otherwise roam, and no other piece is in its way.

    White's non-pawns cannot help either: all eight squares of rank 2 hold
    White pawns that do not move, so nothing else can stand there for the Black
    pawn to take. Quiet moves change nothing about this — they cannot move a
    pawn and cannot occupy a square a pawn is standing on.
    """
    # Ranks are 1..8. Black starts on 7 and wants 1; White's pawns fill rank 2.
    reachable = {7}
    frontier = [7]
    while frontier:
        rank = frontier.pop()
        ahead = rank - 1
        if ahead < 1:
            continue
        # A push needs the square empty; rank 2 is full of White pawns.
        # A diagonal capture needs an enemy piece there; on rank 2 the only
        # enemy pieces are pawns, which this lemma forbids taking. On any other
        # rank there is nothing in the way to begin with.
        if ahead == 2:
            continue
        if ahead not in reachable:
            reachable.add(ahead)
            frontier.append(ahead)

    furthest = min(reachable)
    return HomeRankLemma(
        reachable_ranks=tuple(sorted(reachable, reverse=True)),
        furthest_rank=furthest,
        moves_available=7 - furthest,
    )


# ---------------------------------------------------------------------------
# The origin pair, which is where `P − Cₚ ≤ 88` comes from
# ---------------------------------------------------------------------------

GONE = 0
"""Sentinel rank for a pawn that has been captured or has promoted.

Either way it makes no further pawn move, and either way treating it as no
longer blocking the file is the permissive reading.
"""


@dataclass(frozen=True, slots=True)
class OriginPairSearch:
    """Exhaustive search over one unresolved origin pair."""

    states_explored: int
    max_moves: int
    """The combined pawn-move total, maximised over the whole state space."""

    max_moves_while_both_remain: int
    """The same total restricted to states where neither pawn has left."""

    witness: tuple[tuple[int, int, int, int], ...]
    """A path attaining :attr:`max_moves` **within this relaxation**.

    It shows the search cannot do better, which is a claim about the search. That
    real chess also reaches 10 is a separate fact, witnessed by a legal game in
    the tests rather than by anything here.
    """


UNRESOLVED_ORIGIN_PAIR_MOVE_CAP = 10
"""Combined pawn moves of an **unresolved** origin pair.

The two pawns that start on file `i` — one White, one Black — are that file's
*origin pair*. The file is **resolved** when one of those two pawns itself makes
a diagonal pawn move, which is the only way a pawn changes file; otherwise it is
unresolved and both pawns live and die on file `i`.

Ten, and the argument is in two halves:

- While both are still on the file they cannot pass each other, so with White
  on rank ``2 + a`` and Black on rank ``7 − b`` we need ``2 + a < 7 − b``, and
  their combined moves are at most their combined advance ``a + b ≤ 4``.
- One of them may then be **captured by some other piece**, and the survivor
  gets its own six moves — a whole lifetime, since it can only ever have made
  moves counted in the first half. So ``4 + 6 = 10``.

Both halves are re-derived by :func:`check_origin_pair_cap`, which exhausts a
state space strictly more permissive than chess.

That search also exhibits a path reaching 10 — but a witness inside a relaxation
only shows that **10 is tight for the relaxation**, which is a fact about the
search rather than about chess. The stronger claim needs a legal game, and there
is one: ``tests/test_bound.py::CAP_ATTAINED`` walks Black's a-pawn to a3 in four
moves, has the b1 knight take it there, steps the knight aside, and marches
White's a-pawn the length of the file in six. Ten, in 24 ply of legal chess,
with neither pawn ever moving diagonally. So the constant is exactly right, not
merely an upper bound that happens to hold.

.. rubric:: The correction this constant records

An earlier version of this module asserted ``UNRESOLVED_FILE_CAP = 4`` — the
first half only. That is **false**, and false in the direction that turns legal
games into UNSAT. Once one of the pair is captured the other is free to run.
The counterexample is short and legal:

    1. e4 a5  2. e5 a4  3. Bb5 Nc6  4. Bxa4 Rb8  5. Bb3 Nh6
    6. a3 Ng4  7. a4 Nh6  8. a5

Black's a-pawn plays ``a7-a5-a4`` (2 moves) and is taken by a bishop; White's
plays ``a2-a3-a4-a5`` (3 moves). Neither ever moved diagonally, so the a-file is
unresolved — and the pair has already made 5 moves. Pinned as a regression in
``tests/test_bound.py::TestTheOldCapWasFalse``.
"""

RESOLVED_ORIGIN_PAIR_MOVE_CAP = 2 * PAWN_STEPS
"""12. A resolved origin pair is capped only by the pawns themselves."""


def check_origin_pair_cap() -> OriginPairSearch:
    """Exhaust one unresolved origin pair and read off its move ceiling.

    The state is ``(white rank, black rank, white moves, black moves)`` with
    :data:`GONE` for a pawn that has been captured or has promoted. Transitions,
    every one of them at least as permissive as chess:

    - either pawn may push one square, or two from its own home rank, at any
      time — **turn order is ignored**, and no piece other than the pair's own
      two blocks the file;
    - a push needs every square it crosses to be empty of the *other pawn of the
      pair*. This is a real rule, not an added restriction: a double push over
      an occupied square is illegal, and dropping it would let White answer a
      Black pawn on rank 3 by jumping to rank 4, which no legal game can do;
    - either pawn may be removed at any moment, by any third piece, at no cost
      and with nothing left standing in its place;
    - **no diagonal pawn move**, which is the definition of unresolved;
    - reaching the last rank promotes, and a promoted pawn makes no further
      pawn move.

    What is deliberately *not* modelled — whose turn it is, where the capturing
    piece has to come from, whether it can get there, what it leaves on the
    square, and every other piece on the board — is left out in the direction
    that adds states, never removes them.
    """
    start = (2, 7, 0, 0)
    seen: dict[tuple[int, int, int, int], tuple[int, int, int, int] | None] = {
        start: None
    }
    frontier = [start]
    best = 0
    best_state = start
    best_intact = 0

    while frontier:
        state = frontier.pop()
        white, black, white_moves, black_moves = state
        total = white_moves + black_moves
        if total > best:
            best, best_state = total, state
        if white != GONE and black != GONE and total > best_intact:
            best_intact = total

        successors: list[tuple[int, int, int, int]] = []
        if white != GONE:
            for step in (1, 2):
                if step == 2 and white != 2:
                    continue
                target = white + step
                if target > 8:
                    continue
                if black != GONE and any(
                    black == white + crossed for crossed in range(1, step + 1)
                ):
                    continue
                promoted = target == 8
                successors.append(
                    (GONE if promoted else target, black, white_moves + 1, black_moves)
                )
            successors.append((GONE, black, white_moves, black_moves))
        if black != GONE:
            for step in (1, 2):
                if step == 2 and black != 7:
                    continue
                target = black - step
                if target < 1:
                    continue
                if white != GONE and any(
                    white == black - crossed for crossed in range(1, step + 1)
                ):
                    continue
                promoted = target == 1
                successors.append(
                    (white, GONE if promoted else target, white_moves, black_moves + 1)
                )
            successors.append((white, GONE, white_moves, black_moves))

        for successor in successors:
            if successor not in seen:
                seen[successor] = state
                frontier.append(successor)

    path: list[tuple[int, int, int, int]] = []
    cursor: tuple[int, int, int, int] | None = best_state
    while cursor is not None:
        path.append(cursor)
        cursor = seen[cursor]

    return OriginPairSearch(
        states_explored=len(seen),
        max_moves=best,
        max_moves_while_both_remain=best_intact,
        witness=tuple(reversed(path)),
    )


@dataclass(frozen=True, slots=True)
class NetPawnMoveBound:
    """The maximiser of ``P − Cₚ`` over how many origin files are resolved."""

    resolved_files: int
    pawn_moves: int
    pawn_captures: int

    @property
    def value(self) -> int:
        return self.pawn_moves - self.pawn_captures

    def describe(self) -> str:
        return (
            f"P − Cₚ ≤ {self.pawn_moves} − {self.pawn_captures} = {self.value}, "
            f"at f = {self.resolved_files}"
        )


def pawn_moves_ceiling(resolved_files: int) -> int:
    """``P ≤ min(96, 80 + 2f)``.

    Every pawn belongs to exactly one origin pair and every origin pair to one
    file, so the eight pairs partition the sixteen pawns and their caps add:

        P ≤ 10·(8 − f) + 12·f = 80 + 2f

    and no game beats the flat 96 either.
    """
    if not 0 <= resolved_files <= FILES:
        raise ValueError(f"resolved files must be in 0..{FILES}, got {resolved_files}")
    return min(
        MAX_PAWN_MOVES,
        UNRESOLVED_ORIGIN_PAIR_MOVE_CAP * (FILES - resolved_files)
        + RESOLVED_ORIGIN_PAIR_MOVE_CAP * resolved_files,
    )


MAX_NET_PAWN_MOVES = 88
"""88. The maximum of ``min(96, 80 + 2f) − f`` over ``f ≤ 8``, at ``f = 8``.

`Cₚ ≥ f` because resolving file `i` means a pawn of *that* origin pair made a
diagonal capture, and a diagonal capture has exactly one mover, whose origin
file is one file. Distinct resolved files therefore demand distinct pawn-capture
moves.

Derived by :func:`net_pawn_move_bound` rather than typed in; this constant
is the answer, kept so the model and the cross-check can be read against it.
"""


def net_pawn_move_bound() -> NetPawnMoveBound:
    """Maximise ``P − Cₚ`` subject to ``P ≤ min(96, 80 + 2f)`` and ``Cₚ ≥ f``.

    Taking the maximum over `f` is what makes this a bound over *all* games
    rather than a statement about games with eight pawn captures. Asserting
    ``pawn_captures ≥ 8`` outright is only true *because* `K = 118` forces it, and is
    therefore circular; a shape that cannot reach 96 pawn moves needs fewer
    files resolved and must be charged fewer pawn captures.
    """
    return max(
        (
            NetPawnMoveBound(
                resolved_files=resolved,
                pawn_moves=pawn_moves_ceiling(resolved),
                pawn_captures=resolved,
            )
            for resolved in range(FILES + 1)
        ),
        key=lambda bound: bound.value,
    )


MINIMUM_PAWN_CAPTURES = 8
"""Pawn captures forced on any game in which all sixteen pawns promote.

Not a free lower bound for every game — a game where no pawn ever captures has
none. The argument needs the promotions:

- A pawn only changes file by capturing, so a sideways move *is* a capture —
  one move doing the work of two critical moves, which is exactly a pawn capture.
- Fix a file ``i``. If its origin pair is unresolved, both its pawns spend the
  whole game on file ``i``, one travelling up and one down, and
  :func:`check_file_lemma` says they cannot both get past. So if both promote,
  **at least one of the two makes a sideways move.**
- Every pawn belongs to exactly one starting file, so the eight files call on
  eight different pawns and their sideways moves are distinct.

`K = 118` forces `P = 96`, which forces all sixteen promotions, so 8 is what the
equality case runs on — see :func:`equality_conditions`. The bound is tight: the
published game has exactly 8 pawn captures.
"""


# ---------------------------------------------------------------------------
# C + T ≤ 30, whatever ends the game
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class EndingProfile:
    """One way the last critical move and the end of the game can line up."""

    name: str
    captures: int
    closing_segment: int
    why: str

    @property
    def total(self) -> int:
        return self.captures + self.closing_segment


def ending_profiles() -> tuple[EndingProfile, ...]:
    """The two extremes of ``C + T``, both of which reach 30.

    Reaching the same total is the point: the bound does not have to know how
    the game ends, so nothing downstream has to case-split on it.
    """
    return (
        EndingProfile(
            name="checkmate",
            captures=MAX_CAPTURES,
            closing_segment=MAX_CLOSING_SEGMENT,
            why="the mating side keeps something to mate with, so one of the "
            "30 survives; the mate itself may be quiet and close a segment",
        ),
        EndingProfile(
            name="all-captured",
            captures=MAX_CAPTURABLE,
            closing_segment=0,
            why="every non-king piece goes, but the thirtieth capture leaves "
            "king against king, which is dead and ends the game on the spot",
        ),
    )


def captures_plus_closing_bound() -> int:
    """``C + T ≤ 30``, by cases on whether every capturable piece goes.

    - ``C = 30`` leaves the two kings alone on the board. That is a dead
      position, so the game ends on that very move and ``T = 0``.
    - ``C ≤ 29`` leaves ``T ≤ 1``, since there is at most one segment after the
      last critical move.

    Both give 30, so the bound holds for checkmate, the 75-move rule, fivefold
    repetition, stalemate and dead positions alike.
    """
    all_captured = MAX_CAPTURABLE + 0
    something_left = (MAX_CAPTURABLE - 1) + MAX_CLOSING_SEGMENT
    return max(all_captured, something_left)


MAX_CAPTURES_PLUS_CLOSING = 30
"""The answer :func:`captures_plus_closing_bound` computes, kept as a name."""


# ---------------------------------------------------------------------------
# K ≤ 118 and what equality forces
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class CriticalBound:
    pawn_moves: int
    pawn_captures: int
    resolved_files: int
    captures_plus_closing: int

    @property
    def net_pawn_moves(self) -> int:
        return self.pawn_moves - self.pawn_captures

    @property
    def total(self) -> int:
        return self.net_pawn_moves + self.captures_plus_closing

    @property
    def max_plies(self) -> int:
        """``150K − S`` with the trivial ``S ≥ 1``.

        Both colours have to make at least one critical move — `K = 118` forces
        every pawn to move, and pawns come in two colours — so the actor changes
        at least once against the virtual Black move before ply 1. The real
        bound needs ``S ≥ 3``, which is :mod:`long_chess.bound.blocks`; this is
        the ceiling before that argument runs.
        """
        return 150 * self.total - 1

    def describe(self) -> str:
        return (
            f"K ≤ (P − Cₚ) + (C + T) ≤ {self.net_pawn_moves} + "
            f"{self.captures_plus_closing} = {self.total};  "
            f"at most {self.max_plies} ply before the switch argument"
        )


def critical_bound() -> CriticalBound:
    """``K ≤ 118``, from ``P − Cₚ ≤ 88`` and ``C + T ≤ 30``.

    One formula covers every ending. The two profiles in
    :func:`ending_profiles` are how a game *reaches* 30; neither is the source
    of truth, because a bound that case-split on the ending would have to be
    re-argued every time a new way of ending a game came up.
    """
    envelope = net_pawn_move_bound()
    return CriticalBound(
        pawn_moves=envelope.pawn_moves,
        pawn_captures=envelope.pawn_captures,
        resolved_files=envelope.resolved_files,
        captures_plus_closing=captures_plus_closing_bound(),
    )


MAX_CRITICAL_SEGMENTS = 118
"""The answer :func:`critical_bound` computes, kept as a name."""


@dataclass(frozen=True, slots=True)
class EqualityConditions:
    """The unique term assignment reaching ``K = 118``."""

    resolved_files: int
    pawn_moves: int
    pawn_captures: int
    captures_plus_closing: int

    @property
    def moves_per_pawn(self) -> int:
        return self.pawn_moves // (2 * FILES)

    @property
    def every_pawn_promotes(self) -> bool:
        """Six moves each, each advancing at least one rank over six ranks."""
        return self.moves_per_pawn == PAWN_STEPS

    def describe(self) -> str:
        return (
            f"K = {MAX_CRITICAL_SEGMENTS} forces f = {self.resolved_files}, "
            f"P = {self.pawn_moves}, Cₚ = {self.pawn_captures}, "
            f"C + T = {self.captures_plus_closing}; every pawn makes "
            f"{self.moves_per_pawn} single-square moves and promotes"
        )


def equality_witnesses(
    target: int = MAX_CRITICAL_SEGMENTS,
) -> list[tuple[int, int, int, int]]:
    """Every ``(f, P, O, C+T)`` the bounds permit with ``K = target``.

    Enumerated rather than argued. `K = 118` is the maximum of a sum of
    individually bounded terms, so it should pin all of them — but "should" is
    how the free ``pawn_captures ≥ 8`` axiom got in, so this checks.
    """
    witnesses = []
    for resolved in range(FILES + 1):
        ceiling = pawn_moves_ceiling(resolved)
        for pawn_moves in range(ceiling + 1):
            # A pawn capture is a pawn move and a capture, so it is bounded by both.
            for pawn_captures in range(resolved, min(pawn_moves, MAX_CAPTURABLE) + 1):
                captures_plus_closing = target - (pawn_moves - pawn_captures)
                if 0 <= captures_plus_closing <= MAX_CAPTURES_PLUS_CLOSING:
                    witnesses.append(
                        (resolved, pawn_moves, pawn_captures, captures_plus_closing)
                    )
    return witnesses


def equality_conditions(target: int = MAX_CRITICAL_SEGMENTS) -> EqualityConditions:
    """What ``K = target`` forces, or a failure if it does not force one thing.

    Raises :class:`ValueError` when the target admits no assignment or more than
    one, because both would mean the caller is quoting an equality case the
    arithmetic does not actually have.
    """
    witnesses = equality_witnesses(target)
    if len(witnesses) != 1:
        raise ValueError(
            f"K = {target} admits {len(witnesses)} term assignments, not 1; "
            "there is no equality case to state"
        )
    resolved, pawn_moves, pawn_captures, captures_plus_closing = witnesses[0]
    return EqualityConditions(
        resolved_files=resolved,
        pawn_moves=pawn_moves,
        pawn_captures=pawn_captures,
        captures_plus_closing=captures_plus_closing,
    )
