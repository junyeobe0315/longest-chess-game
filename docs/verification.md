# What the machine checks, and what it is worth

> The proof is in [paper/main.tex](../paper/main.tex) and is checkable by
> hand. This document is the audit record for the code that backs it:
> what each check establishes, what it measurably does not, and where the
> honest limits are. [CLAIMS.md](../CLAIMS.md) maps paper statements to
> code; this explains the checks themselves.

Three things run here, and they answer different questions.

| | question | code |
|---|---|---|
| the finite checks | do the paper's case analyses actually exhaust? | `src/long_chess/bound/` |
| the witness verifier | is the 17,697-ply game legal, and does it end in mate? | `src/long_chess/verifier/` |
| the second move generator | does any of that depend on one chess library? | `checker/longest_check.c` |

A fourth, the CP-SAT and arithmetic cross-checks on the central case
analysis, has its own document: [abstract-model.md](abstract-model.md).

## The witness verifier

`src/long_chess/verifier/` imports nothing else in the package. A move
sequence counts as a result only when this judge passes it, and a judge
sharing code with a producer of games would not be independent evidence.
The reference game itself was produced by someone else
([Murphy VII, SIGBOVIK 2020](https://tom7.org/chess/longest.pdf)), which
separates producer from judge a second time.

Two implementation notes worth repeating, because both are the kind of
error that passes silently:

- **Checkmate outranks the 75-move draw.** The witness's final ply is
  simultaneously the 150th quiet ply of its segment and mate (FIDE
  9.6.2's precedence clause). A verifier that tests the clock first
  scores it a draw — same length, wrong result.
- **Do not compare whole FENs for repetition.** The halfmove clock and
  the move number play no part in position identity, and raw
  `ep_square` / `castling_rights` both over-distinguish. Use
  `has_legal_en_passant()` and `clean_castling_rights()` (FIDE 9.2.2).
  Comparing whole FENs fails in the worst way: the clock makes every
  position look new, so nothing ever repeats, so the fivefold rule
  silently never fires.

Tom 7's `longest.cc` currently has `static constexpr int MOVE_RULE = 50;`
directly beneath a comment saying 75 is the correct value. That reference
implementation is not an oracle — which is the whole reason the verifier
here is independent.

## Dead positions: why the witness needs no decision procedure

FIDE Article 5.2.2 ends the game immediately when a position is *dead* —
when no series of legal moves can lead to checkmate for either side.
python-chess's `is_insufficient_material()` decides something narrower:
whether the **material on the board** could ever mate, ignoring how it is
arranged. The verifier uses it as a cheap first-pass check. It is not,
and must not be presented as, a decision procedure for Article 5.2.2.

The gap, measured against python-chess 1.11.2: in
`7k/8/8/p1p1p1p1/P1P1P1P1/8/8/K7 w - - 0 1` every pawn is blocked by the
pawn in front of it and has no diagonal contact with any other, so no
pawn can ever move again. Only the kings can move and neither can ever be
mated — the position is dead — but the material-only test sees eight
pawns and says nothing. The error is one-sided, which is the useful part:

> `is_insufficient_material() == True` implies dead.
> Dead does **not** imply `is_insufficient_material() == True`.

So our verifier ends games **later** than FIDE. That means the
*construction* is the exposed side: if a dead position occurred at, say,
ply 9,000, FIDE says the game ended there and our count is inflated.
Missing detections make a claimed length too large, which is exactly the
wrong direction for a lower bound. (The *upper* bound is the safe side:
the model ignores dead positions, so it permits games FIDE would have cut
short, and bounding a superset bounds the subset. Omitting constraints
only ever loosens a model, and a looser model refutes less, not more.)

The construction is nevertheless safe, by a short argument rather than
that one:

> **A game that ends in checkmate contains no dead position.** Take any
> position at ply *i*. The remaining moves of the game are a series of
> legal moves ending in checkmate, so mate is reachable from it, so it is
> not dead.

The witness ends in checkmate — verified end to end — so the gap is not
exercised anywhere in it.

The upper-bound model ignores every dead position **except king against
king**, and that one exception is worth stating precisely because it
points the other way. `C + T ≤ 30` is proved by cases, and one case is:
30 captures leaves the two kings alone, which is dead, so the game ends
there and `T = 0`. That is a dead-position rule being used to *shorten* a
game — the tightening direction, the one that can invent a false UNSAT.
It is safe because it is simply true: `is_insufficient_material()` and
Article 5.2.2 agree on K vs K, and no legal game continues past it. A
constraint every legal game already satisfies excludes none of them. The
locked-pawn gap above is never appealed to in either direction.

## The second move generator

Two things are on the list of what a sceptical reader has to trust: the
summary of the FIDE termination rules, and — for the
mechanical checks only — move generation. The second item covers a lot of
ground: the verifier pushes 17,697 moves through python-chess and asks it
at every ply what is legal and whether the game has ended. If
python-chess generated a move it should not, the failure would propagate
silently through all of it and look exactly like success, because there
would be nothing to disagree with.

[`checker/longest_check.c`](../checker/longest_check.c) is that
disagreeing party: one C99 file, 0x88 mailbox where python-chess uses
bitboards, parsing the PGN and resolving its SAN for itself, written
against the Laws without reading python-chess. See
[checker/README.md](../checker/README.md) for the build and the flags.

### What replaying the witness alone proves — measured

Not as much as it looks like. The 17,697-ply game contains **0** castling
moves, **0** en passant captures, **0** pawn double pushes, and **0**
positions where an en passant capture was legal at all. A game built for
length wastes no tempo, and a pawn that advances two squares has spent a
move it could have spent twice. No double push means no en passant offer,
ever. So a program implementing no castling rule and no en passant rule
whatsoever would replay this game correctly, ply for ply, to mate.

That is not hypothetical. Deliberately breaking the C file three ways and
re-running every check gives:

| check | en passant removed | castling over-restricted | bishop clause missing |
|---|---|---|---|
| replay the witness | no | no | no |
| per-ply trace differential | no | no | no |
| legal-move dump differential | no | **yes** (ply 1,755) | no |
| corpus obligations | no | no | no |
| perft against published counts | **yes** | **yes** | no |
| hand-written rule cases | **yes** | **yes** | no |
| material scan | no | no | **yes** (10 of 5,103) |

("yes" = the check catches the defect.) The third column is not a
mutation at all: it is the state the file was actually in until the
review that added `--material-scan`, and the column is what every check
said at the time. Each check covers something the others do not, and the
two with an external standard are the only ones that catch a defect the
witness never exercises.

### Perft: what depth is enough

Perft counts leaf nodes of the legal-move tree and compares against
numbers published outside this project (the Chess Programming Wiki's
"Perft Results", cross-checked by many engines over many years). Depth is
not a free parameter. With en passant deleted entirely, from the starting
array:

| depth | correct | en passant removed | difference |
|---|---|---|---|
| 4 | 197,281 | 197,281 | **0** |
| 5 | 4,865,609 | 4,865,351 | **−258** |

Depth 4 catches nothing, and the reason is a counting argument rather
than luck: for White to capture en passant a White pawn must reach the
fifth rank (plies 1 and 3) and a Black pawn must double-push alongside it
(ply 4), so the capture is ply 5. This is why the suite is seven
positions and not one — in Kiwipete a Black pawn already stands on b4, so
the same defect shows at depth 2, off by exactly one node. The default is
depth 5; CI runs depth 6.

**The oracle is external, and a typo in it is self-announcing.** A
wrongly transcribed number fails loudly rather than passing quietly,
unless the typo happens to coincide with this program's own wrong output.
A number in that table is never edited to match this program.

### The independence criteria

Stated plainly, so a reviewer can check each one rather than take
"independent" on trust:

1. **Different language and toolchain.** C99 against Python 3.13. Satisfied.
2. **Different board representation.** 0x88 mailbox against bitboards. Satisfied.
3. **Different legality strategy.** make / attacked / unmake against bitboard pin and check masks. Satisfied.
4. **No shared code or data structures.** The C file imports nothing from this repository and nothing from python-chess. Satisfied.
5. **Independent input parsing.** The C reads the PGN and resolves the SAN itself. `Nge4` names a destination and leaves the reader to work out which knight can legally get there, so resolving SAN *is* move generation; taking a move list from another program would put that program's generator back inside the trusted chain. Satisfied.
6. **An external oracle for at least one check.** The perft table. Satisfied — and the only criterion that speaks to *both* implementations being wrong at once.
7. **Independent author.** **Not satisfied, and not satisfiable here.**

The last one is the important one. Both implementations were written by
the same person from the same reading of the FIDE Laws. If that reading
is wrong, both programs are wrong in the same direction, agree perfectly,
and every check passes.

> This work reduces trust item 2 — the move generator. It does **not**
> reduce trust item 1 — the summary of the Laws.

Two places where item 1 is doing real work and item 2 is not: the
precedence of mate over the 75-move draw, and position identity under
Art. 9.2.2. Both implementations apply the same reading of each, because
both were written by someone who had read the same clause. A reader who
disagrees about the clause gets no help from their agreement.

## Honest limits

- **Author independence is absent.** Criterion 7. Everything else is subordinate to it.
- **The ending rules have no external oracle.** Perft's published counts cover move generation and nothing else. Fivefold repetition, the 75-move rule, the precedence of mate, and Art. 5.2.2 are pinned only by hand-written rule cases and by agreement between two programs that share an author. This is the weakest part of the artefact and should be read as such.
- **Both programs approximate Art. 5.2.2 by material.** Neither decides dead positions. `--material-scan` establishes only that the two implement the *same* approximation over all 5,103 inventories, not that the approximation is right. It is still worth running: the two disagreed until recently, and every other check passed while they did.
- **The corpus walk is random.** Fixed seeds make a run reproducible; they do not make it exhaustive. Zero exceptions over 20,000 positions is evidence, not proof.
- **The differentials cover one game.** 17,698 positions is a lot, but they are the positions of a single, extremely unusual game. Perft and the corpus are what reach the rest of chess.
- **The PGN dialect is narrow.** The C reader accepts the movetext of the files in `data/` and refuses a `[FEN]` tag rather than skipping it. It is a reader for this repository's games, not a general PGN library.
- **`-Werror` is a build-time contract, not a proof of anything.**

## Running it

```bash
make verify
```

Runs the witness replay, the counting proof, the test suite, the second
move generator and the CP-SAT cross-check. Two steps degrade rather than
fail: without a C compiler the move-generator checks skip, and without
OR-Tools (`uv sync --extra solver`) the CP-SAT cross-check skips. Both
are cross-checks on a proof that stands without them, and a check that
cries wolf gets disabled.
