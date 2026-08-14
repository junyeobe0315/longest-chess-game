# The abstract model

> Backs the ancillary cross-checks named in the paper's "Data and code
> availability" section ([paper/main.tex](../paper/main.tex)): the CP-SAT
> and arithmetic cross-checks, constraint by constraint. The cross-checks
> are not the proof; the counting argument of the paper's §§3–4 is.

A modelling mistake here does not produce a wrong answer loudly. It produces
UNSAT, which looks exactly like a proof. So every variable and constraint is
listed below with whether it is an equivalence or a relaxation, and the list
describes **what the code actually does** — an earlier version of this file
described a design that was never built, which is its own kind of unsound.

## What the model is for

**It is not the proof.** `long_chess.bound.blocks` refutes every `S ≤ 2` shape
by counting, with no solver — that is the paper's §4, run by
`scripts/analyse_bound.py`. This model re-decides
the same question by a different route, and
`long_chess.model.independent` re-decides it by a third. Three methods
disagreeing is how a mistake in any one of them surfaces; three agreeing is the
strongest thing available here, since CP-SAT emits no proof object for UNSAT.

The question all three answer:

> Is there a legal game with `K = 118` whose `K` **segment endpoints** fall
> into a given sequence of single-colour blocks?

Endpoints, not critical moves alone: the last endpoint may be the terminal
quiet segment — a quiet mate, or the moves that run out the 75-move or
repetition clock — and it belongs to the block of its own colour. This is the
same sequence `S` is measured over in `bound.blocks`, and the distinction is
load-bearing for exactly one constraint; an earlier version of this sentence
said "critical events", and the correction below records what that reading
would have broken.

For any shape with `S ≤ 2`, a yes would leave a 17,698-ply game open. All five
come back no, under both endings.

| shape | S | why counting kills it |
|---|---|---|
| B | 0 | `P = 96` needs White's pawns to move, and White has no block: `P ≤ 48` |
| W | 1 | the same, colours exchanged |
| B, W | 1 | the first colour's ≥14 captures land before the second colour has made any *critical* move, so ≥7 pawn-origin units of that side die having made no pawn move and ≥42 pawn moves are lost: `P ≤ 54` |
| W, B | 2 | the same count, colours exchanged |
| B, W, B | 2 | ≥7 pawn-origin Black units die in the middle block, so they need six pawn moves each in block 1 — where the home-rank lemma allows four: `P ≤ 82` |

Two things this table is short for. "Before the second colour moves" means
before its first **critical** move — quiet moves are free throughout, and the
side in question may make plenty. And the counting is over **units**, the 32
things that start on the board: `P = 96` promotes every pawn, so a pawn-origin
unit captured later is captured as a piece, and "only 7 of a side's capturable
units did not start as pawns" is a statement about origins.

## What B, W, B forces before any solving

The hardest shape, read by hand. This was the route the model was built for,
before the counting proof closed it directly; it is kept because it is the same
position from a different angle, and because the model's variables are easier to
read against it.

Black's block comes last, so **Black gives mate**. White therefore ends with a
lone king and all 15 of White's capturable pieces are taken by Black; Black
keeps its king and the piece it mates with, so White takes 14.

Every White critical event is in the middle block. That sorts each Black event
into one of two places:

- **must follow a White event → block 3.** Every Black capture of a White piece
  that has itself made a critical move is here.
- **must precede a White event → block 1.** A Black piece that White captures
  has to finish its own events first, so all 14 of White's victims are done by
  the end of block 1.

Block 3 therefore contains only Black pieces White never captures — the king
and the mater, two pieces. And at least 8 of Black's captures are stuck there,
because White's eight pawns must each make six moves and so cannot be among the
"forces nothing" victims.

> **The condition to decide: Black's king and one other piece, between them,
> capture at least eight White pieces after White's last critical move, and
> then mate — with White reduced to a lone king and never capturing or moving a
> pawn in reply.**

## Variables — what was built, not what was sketched

This section used to describe a design. The implementation is coarser, and the
difference matters enough to spell out: **every variable the sketch proposed
and the model does not have is a constraint the model does not impose**, which
makes it looser. A looser model refutes less, so an UNSAT from it is a
*stronger* statement, not a weaker one. The mismatch was a documentation bug,
not a modelling one.

What `long_chess.model.abstract` actually declares:

| variable | domain | meaning |
|---|---|---|
| `mv_{c}{i}_{b}` | 0..6 | moves by pawn `i` of colour `c` in block `b`, for blocks of its own colour |
| `mv_{c}{i}` | 0..6 | that pawn's total |
| `pawn_moves` | 0..96 | everyone's total |
| `cap_{c}{kind}{i}` | bool | is this piece captured at all |
| `capat_{c}{kind}{i}_{b}` | bool | captured in block `b`, over blocks of the *enemy* colour |
| `captures` | 0..29 or 0..30 | total, ceiling set by the ending |
| `closing_segment` | 0..1 | the segment after the last critical move |
| `everything_captured` | bool | draw only: all 30 taken, so no closing segment |
| `home_rank_opened` | bool | an enemy pawn was captured in block 0 |
| `resolved_files` | 0..8 | files resolved by a sideways pawn move |
| `pawn_captures` | 0..96 | moves that are both a pawn move and a capture |

Derived, never free: an event's actor, and hence the whole of `S`. That is the
observation the reduction rests on — only the opposing side can capture a
piece, and only a pawn's own colour can move it.

## Constraints, and which direction each is safe in

Sound means **every legal game maps to a solution**. A constraint merely
*implied* by legality is safe. One stronger than legality is not: it produces
UNSAT indistinguishable from a proof.

The table used to label most rows `equivalence`. That was the wrong word — none
of these is equivalent to anything, and reaching for it is how a necessary
condition got written down as a definition and the checkmate branch stopped
being a model of checkmate.

Every row below is a **necessary condition** — something every legal game
satisfies. None is an equivalence, and none needs to be: soundness only requires
that no legal game is excluded. The column says where each one comes from, since
that is what a reader has to check.

| constraint | why no legal game violates it |
|---|---|
| a pawn makes at most six moves, all in blocks of its colour | six ranks to promotion, one per move; a pawn move is a critical move of its colour |
| a captured pawn makes no moves in blocks at or after the one it dies in | a unit moves before it is taken |
| a piece is captured in a block of the *enemy* colour, or not at all | only the opponent can capture it |
| checkmate: the mating side keeps at least one non-king unit | a lone king cannot mate, and the mating side *is* the last block's colour because shapes are endpoint sequences and the mate is the last endpoint. **This is all checkmate implies** — the mated side may keep most of its army |
| a draw taking all 30 leaves king against king, so no closing segment | K vs K is dead under FIDE 5.2.2, so the game ends on that move |
| a pawn's first-block moves ≤ 4 unless an enemy pawn was captured there | the home-rank lemma, proved in `bound.invariant` |
| `pawn_moves ≤ 80 + 2·resolved` and `pawn_captures ≥ resolved` | the origin-pair cap and the file lemma, both in `bound.pawns` |
| `pawn_captures ≤ pawn_moves` and `pawn_captures ≤ captures` | a pawn capture is a pawn move *and* a capture |
| `pawn_moves + captures − pawn_captures + closing = K` | the definition of `K`, by inclusion–exclusion |
| `ending` must be `checkmate` or `draw` | not a constraint — a `ValueError`, because falling through to the draw branch relaxed the model silently |

That checkmate row read "the mated side loses all 15; the mating side keeps
exactly one" until it was found to be **stronger than legality**. Losing all 15
is what `K = 118` implies, not what checkmate implies: Scholar's mate is a legal
checkmate leaving Black's army almost intact, and the model rejected it. The
verdicts at `K = 118` were unaffected — the constraint is derivable there — but
the claim below that *every legal game maps to a solution* was false for every
other `K`. Pinned by
`tests/test_defects.py::TestCheckmateBranchWasNotAModel`.

`resolved_files` is a **free** variable, which is what makes the coupling safe:
every legal game satisfies both rows at its own true `f`, so the solver only has
to find one value that works, and it may find a smaller one. Pinning it, or
asserting `pawn_captures ≥ 8` outright, would be stronger than legality.

That row read `pawn_moves ≤ 32 + 8·resolved` until the unresolved cap of 4 it
came from was found to be false — it ignored the case where one of the two pawns
is captured by a third piece and the other runs on. Pinned by
`tests/test_defects.py::TestTheUnresolvedPairCapWasFalse`.
The replacement is weaker at every `f`, as a correction in that direction must
be.

## A correction: which sequence the shapes are shapes of

This document used to pose the question over "critical events", and the
checkmate branch is sound only under a different reading that was written down
nowhere. The two diverge at exactly one place: the branch reads `colours[-1]`
as the mating side.

Over critical-move sequences that attribution is false. A quiet mate can be
delivered by the colour that made no critical move last, and the game is not
even exotic: Black captures all fifteen White units while White shuffles a
knight, the bare White king captures one Black pawn — White's only critical
move — and Black mates the lone king quietly. Its critical actors are `(B, W)`
and the mater is Black. Pinning that game's profile into shape `(B, W)` under
checkmate returns INFEASIBLE: read that way, the model rejects a legal game,
which is an over-constraint of exactly the class the two corrections above
record. Over endpoint sequences the game's shape is `(B, W, B)`, the profile
is feasible there, and the attribution is a fact rather than an assumption:
the mate is the game's last endpoint, so it sits in the last block by
construction.

The shapes were always endpoint sequences everywhere else in the project —
`observe()` folds the mate into `phases()`, and `S` is measured over endpoints
in `bound.blocks`, with `check_dropping_terminal_endpoint_never_adds_a_switch`
bridging to critical-move statements. So the enumeration's coverage is
unchanged: every
legal game's endpoint shape is an alternating block sequence, a game with
`S ≤ 2` has one of the same five, and all five are refuted. No verdict moves.
What was wrong was the sentence defining the question, plus the fact that the
convention it contradicted existed only as an unstated habit. It is now stated
in `abstract.py`, and the game above — legal under one reading, rejected under
the other — is pinned with both readings in
`tests/test_defects.py::TestMatingSideIsTheLastEndpoint`.

Had the convention genuinely been critical-moves-only, the verdicts would
still not have moved: the draw branch imposes no mating cap, its feasible set
contains everything the checkmate branch minus the cap allows, and it is
INFEASIBLE for the same six shapes. What the cap carried was never a verdict
at `K = 118` — it was the claim that every legal game maps to a solution,
which is the claim this model exists to keep.

## What the sketch proposed and the model does not have

All of these were in the original design and none is implemented. Each omission
loosens the model:

- **which piece captures which** (`captured_by`). Only *whether* and *in which
  block* is tracked. The capturer's own precedence constraints are therefore
  absent.
- **promotion files** per pawn, and with them the geometry of pawns crossing.
  Replaced by the aggregate `resolved_files` coupling.
- **which piece delivers mate** (`mater`). Only the aggregate survivor counts.
- **per-piece event ordering** beyond pawns. A promoted rook's captures are not
  ordered against its promotion; only pawn moves are ordered against capture.
- **a capture's victim being alive at that point**, beyond the pawn case above.

Also absent, and absent on purpose from the start: squares, reachability,
whether a capture is physically available, and whether the quiet bridges between
events exist.

Dead positions are absent with **one exception**: taking all 30 capturable
pieces leaves king against king, and the model forbids a closing segment after
that. It is the one dead-position case where the material test and FIDE agree,
and it is a true statement about legal games, so imposing it excludes none of
them. Every other dead position is ignored, which loosens the model — see
[verification.md](verification.md).

## The soundness test, and what it cannot do

Before any UNSAT is believed, the model must accept the games we already have.

**Built, and worth having.** `long_chess.model.validate` maps the published
17,697-ply game to an assignment and insists the model calls it feasible —
`P=96, C=29, O=8, T=1`, shape `B W B W`, `K=118`. If it did not, the model would
already be too tight and every result from it would be void.
*(`tests/test_model.py::TestSoundness`)*

**But passing it is not soundness, and twice now it has passed while the model
was unsound.** A test built from one game can only catch constraints that game
violates:

- the false unresolved cap of 4 gave `pawn_moves ≤ 32 + 8f`, which agrees with
  `80 + 2f` exactly at `f = 8` — and the published game resolves all eight
  files, so it sailed through;
- the checkmate branch forced the mated side to lose all fifteen units, which
  the published game does, so that sailed through too.

Soundness has to be argued constraint by constraint — that is what the table
above is for — and both defects were found by argument, not by this test. The
right way to read it is as a *necessary* condition that has caught nothing so
far, kept because the day it fires it will have caught something fatal.

One further check was listed here as though it existed. It does not, and this
section used to read as if it did:

- **The scheduling analysis's precedence graph as an independent oracle**, so that any solution the
  model emits is a topological order of it. Not built. It only bites on a
  *feasible* answer with a candidate to inspect, and every `S ≤ 2` shape came
  back infeasible, so there has never been a solution to test. It is the same
  gap as the unbuilt concretiser below.

That absence does not touch the upper bound. The proof's source of truth is the
counting in `long_chess.bound.blocks`, not this model. What the check would have
bought is more confidence in a *feasible* verdict, and the result does not rest
on one.

## What comes back from the concretiser

If the abstract model emits a candidate, the concretiser tries to build it on a
real board — using the macro-state search and the quiet-bridge planner carried
over from the scheduling analysis. Failures return as no-goods, and each one carries the reason it
is impossible, because a no-good that is generalised past what was actually
shown is the same false-UNSAT failure by another route.

Expected shapes, from what the counting already suggests is tight:

- *this Black piece cannot reach that White piece to capture it while White has
  no legal quiet reply* — the block-3 condition is the sharp one.
- *this pawn cannot promote before that one*.
- *this piece cannot get out before the block it is needed in*.

## Status

Built and run, over every block shape and both endings. The answer came back
INFEASIBLE for every shape with `S ≤ 2`, so the concretiser and the CEGAR loop
described above were never exercised — there was no candidate to realise.

Three guards stand in for them, and all three matter more than the concretiser
would have:

- `long_chess.bound.blocks` decides the same question by counting, with no
  solver and no model. That is the proof; this is the cross-check.
- `long_chess.model.validate` feeds the published 17,697-ply game to the model
  and insists it is accepted. A model that rejects a game that exists is
  describing its own constraints, not chess.
- `long_chess.model.independent` decides the same question with no solver. It
  declares its own constants but reads the same `Shape` and works in the same
  numbers, so it is an **independent arithmetic cross-check**, not a second
  proof. It caught two real defects the solver could not have.

And the solver is no longer allowed to be vague: `UNKNOWN` raises
`Inconclusive` rather than being reported as infeasible. A timeout is not a
refutation.
