# `checker/` — the second move generator

`longest_check.c` is an independent implementation of the FIDE Laws of Chess:
one C99 file, standard library only, no dynamic allocation. It reads
`data/longest.pgn`, resolves its SAN for itself, replays it under its own
reading of the ending rules, and reports how long the game is and how it ends.

It exists to make one item of this project's trusted base smaller.

## What it is for

[`docs/verification.md`](../docs/verification.md) states what a sceptical
reader has to trust. Two things are on that
list: the summary of the FIDE termination rules, and the move generation of
python-chess, which every mechanical check in this repository went through.

That second item is a library, and a library is the kind of thing a second
implementation can speak to. **It does not shrink the first item** — both
implementations were written by the same person from the same reading of the
Laws, so what is established is *implementation* independence, not *author*
independence. [`docs/verification.md`](../docs/verification.md) sets out the
independence criteria in full, and what each does and does not buy.

## Build

```bash
gcc -std=c99 -O2 -Wall -Wextra -Werror -pedantic -o /tmp/lc checker/longest_check.c
```

Under a second, and it must be silent: `-Werror` is part of the deliverable, not
a convenience. Any C99 compiler will do — CI builds it with both gcc and clang
and requires both to agree, and with `-fsanitize=address,undefined` over the
witness.

Everything below is also run in one step, with the compiler located
automatically:

```bash
uv run python scripts/check_movegen.py          # ~20 s
uv run python scripts/check_movegen.py --deep   # perft to depth 6, ~30 s
```

That script skips cleanly, returning 0, when no C compiler is installed, the way
the CP-SAT cross-check skips when OR-Tools is absent. `make verify` includes it.

## The modes, and what each establishes

Exit status is 0 for accepted, 1 for rejected or for an expectation the replay
did not meet, 2 for a bad command line.

### `--perft-suite [--max-depth D]`

Counts leaf nodes to a fixed depth from seven positions and compares against a
table of published counts compiled into the file. The table is the **oracle**
and comes from outside this project — the Chess Programming Wiki's "Perft
Results", cross-checked by many engines over many years. A number there is never
edited to match this program.

This is the only check here that can catch both implementations being wrong in
the same direction, which is why it comes first. Agreement between two
generators that both drop en passant is agreement about nothing.

```bash
/tmp/lc --perft-suite --max-depth 5    # 42 checks, ~19 s
/tmp/lc --perft-suite --max-depth 6    # 44 checks, ~25 s
```

`--perft "<FEN>" <depth>` counts one position, and `--perft-divide` splits the
count per root move — the two tools you actually use to localise a disagreement
once the suite reports one.

### `--rule-cases`

Thirty-three hand-written positions, each pinning one Law by article number:
en passant including the rank-pin case that a generator handling pins by ray
rather than by make/test/unmake gets wrong (Art. 3.7.3.1–3.7.3.2, 3.9.2),
castling in eight variations including the one where b1 is attacked and
castling is still legal (Art. 3.8.2), promotion and underpromotion
(Art. 3.7.3.3), pins and double check (Art. 3.9), checkmate and stalemate
(Art. 5.1.1, 5.2.1), and eleven material combinations (Art. 5.2.2).

Several cases are stated as a complete move list rather than as "this move is
legal", so a move that should be missing is an absence the reader can see rather
than one they have to trust.

```bash
/tmp/lc --rule-cases    # 33 cases, instant
```

### `<file.pgn> [--expect-plies N] [--expect-termination NAME]`

Reads the PGN, resolves the SAN, replays the game, and applies the rules that
end a game on their own after every ply: checkmate, stalemate, insufficient
material, fivefold repetition (Art. 9.6.1) and the 75-move rule (Art. 9.6.2).

Nothing about the game is compiled in. The length and the ending are *claims*,
supplied on the command line and compared against what the replay found:

```bash
/tmp/lc data/longest.pgn --expect-plies 17697 --expect-termination checkmate
```

```
plies              17697
termination        checkmate
critical segments  118
final fen          3k4/3Q4/4K3/8/8/8/8/8 b - - 150 8849
```

Reading the SAN is part of the independence claim and not a convenience. `Nge4`
says where a knight is going and leaves the reader to work out which knight can
legally get there, so resolving SAN *is* move generation. Handing this program a
move list produced by something else would put that something else's generator
back inside the chain of things a reader has to trust.

### `--trace FILE`

Writes the same per-ply TSV the Python verifier writes: FEN, move, whether the
ply was critical, halfmove clock, repetition count, termination verdict. The two
files are compared with `cmp`, and they are byte-identical for all 17,698 rows.

Agreement row by row is agreement about the *ending* rules, not only about
legality — including the two places this repository has already been bitten:
that checkmate outranks the 75-move draw on the final ply, and that position
identity under Art. 9.2.2 excludes the clock and counts an en passant right only
when the capture really exists.

### `--dump-moves FILE`

Writes every legal move at every position of the game, one line per ply, sorted.
Compared against `scripts/dump_legal_moves.py`, which does the same with
python-chess: 17,698 positions, 730,845 moves, identical.

This is the sharper of the two differentials, and the reason is measurable. The
witness plays no castling move and no en passant capture — not one, in 17,697
plies — so a replay of it exercises neither rule. The legal-move dump does:
1,420 of its positions offer a castling move that was never played. Deliberately
breaking castling in this file leaves the replay and the trace passing and is
caught by the dump at ply 1,755. [`docs/verification.md`](../docs/verification.md)
records that experiment and its companions.

### `--corpus <positions> [--seed S]`

Walks random legal games and checks, at every position, over every legal move,
the four claims about the rules of chess that the home-rank lemma leans on —
[H1] [H2] [H5] [H6] of `src/long_chess/bound/invariant.py`.

Those four are corpus-checked on the Python side too, which is exactly why they
are here: passing there leaves python-chess inside the trusted base of
Lemma 4.5. The walk is biased towards pawn moves and captures, because an
unbiased walk almost never produces the promotions, double pushes and en passant
captures the obligations would break on; the run prints how many of each it
actually saw, so the bias can be judged rather than assumed.

```bash
/tmp/lc --corpus 20000 --seed 1    # ~0.1 s
```

### `--moves "<FEN>"` and `--fen "<FEN>"`

One position's legal moves, and a FEN round-trip. Debugging tools; the suite
above is what actually establishes anything.

## The constraints the file is written under

They are all in service of auditability, and a reviewer should hold the file to
them:

- **One file, C99, standard library only.** No second translation unit, no
  header of our own, no external library. `gcc -std=c99 -pedantic` is the whole
  toolchain.
- **No dynamic allocation.** No `malloc`, no `free`, anywhere. Every buffer is a
  fixed-size static array: 256 moves per position, 65,536 plies, 131,072
  repetition slots.
- **The answer is not compiled in.** Neither 17,697 nor 118 appears as a
  constant in the source. `MAX_GAME_PLIES` is 65,536 — the size of an array and
  nothing more, set far above any plausible game precisely so that it cannot be
  mistaken for knowledge of the result.
- **0x88 mailbox, not bitboards**, with pseudo-legal generation filtered by
  make / king-attacked / unmake. python-chess is bitboard-based. Sharing a
  representation is how two implementations come to share a bug.
- **Written without reading python-chess.** The rules come from the Laws, and
  the governing article is cited in a comment wherever one is subtle.

## Where to read next

- [`docs/verification.md`](../docs/verification.md) — the audit record: the
  independence criteria, the mutation experiments that measure what each check
  is worth, and the honest limits.
- [`CLAIMS.md`](../CLAIMS.md) — what this establishes, mapped against the
  paper's numbered statements.
