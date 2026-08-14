# The maximum length of a chess game is 17,697 plies

[![tests](https://github.com/junyeobe0315/longest-chess-game/actions/workflows/tests.yml/badge.svg)](https://github.com/junyeobe0315/longest-chess-game/actions/workflows/tests.yml)
![python](https://img.shields.io/badge/python-3.13-blue)
![c99](https://img.shields.io/badge/C-C99-blue)
![category](https://img.shields.io/badge/category-combinatorics_(math.CO)-blueviolet)
![reviewed](https://img.shields.io/badge/peer%20reviewed-no-orange)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21828025-blue)](https://doi.org/10.5281/zenodo.21828025)

Companion repository for the paper

> **The maximum length of a chess game under the 2023 FIDE Laws**
> — Junyeop Yim.
> [paper/main.pdf](paper/main.pdf) · source: [paper/](paper/)

**The upper-bound proof lives in the paper, and it is a hand proof.**
François Labelle and Tom Murphy VII constructed legal games of 17,697
plies ([Labelle 2015](https://wismuth.com/chess/longest-game.html),
[SIGBOVIK 2020](https://tom7.org/chess/longest.pdf)), and Murphy's
scheduling analysis gave an arithmetic ceiling of 17,699, leaving a
two-ply gap. The paper closes it: partitioning play at pawn moves and
captures yields at most 118 segments, each segment has at most 150 plies,
and a game with all 118 segments must change the colour of successive
segment endpoints at least three times — so no legal game exceeds
150·118 − 3 = 17,697 plies, and the known constructions are optimal.
Moreover, in every maximum-length game all sixteen pawns make six
one-rank moves and promote.

This repository is the supporting evidence. It holds the move-by-move
replay verification of Murphy's 17,697-ply witness that the paper's
sharpness proposition cites — performed twice, under two independently
implemented rule sets — machine-checks the finite claims behind the
paper's lemmas, and re-derives the central segment-scheduling bound by
CP-SAT and arithmetic cross-checks. None of these computations enters
the upper-bound proof.

## Verify

The whole result, replayed and judged in about a second:

```bash
make witness
```

Everything (~35 s):

```bash
make verify
```

Two steps degrade rather than fail: without a C compiler the second move
generator skips, and without OR-Tools (`uv sync --extra solver`) the CP-SAT
cross-check skips. Both are cross-checks on a proof that stands without them.

## What is checked, and what is trusted

[CLAIMS.md](CLAIMS.md) maps each statement of the paper to the code that
decides it and the test that pins it.

The mechanical checks are not the upper-bound proof — the paper's argument
is a hand argument and is checkable without running anything here. The one
place the paper cites this repository is the sharpness proposition, for the
replay verification of the witness. What a sceptical reader must trust
here: this project's summary of the FIDE termination rules, and, for the
mechanical checks only, move generation. The second item is not a single library:
`checker/` re-verifies the witness in C99 without python-chess, so what
remains is the proposition that two independently implemented generators do
not fail identically. Both were written by the same author from the same
reading of the Laws — this is implementation independence, not author
independence. [docs/verification.md](docs/verification.md) states the
criteria, the mutation experiments that measure what each check is worth, and
the limits.

## Layout

```
paper/                     the manuscript (main artifact)
CLAIMS.md                  paper statement -> code -> test map
src/long_chess/verifier/   independent FIDE judge; imports nothing else here
src/long_chess/bound/      the finite checks behind the proof's lemmas
src/long_chess/model/      CP-SAT + arithmetic cross-checks (outside the proof)
src/long_chess/skeleton/   critical-segment representation of the witness
src/long_chess/search/     critical-event scheduling analysis
checker/                   a second move generator: one C99 file, no python-chess
tests/                     the ~5 s suite
scripts/                   one entry point per check
data/                      witness and skeletons (provenance: data/README.md)
docs/                      the audit record for the mechanical checks
```

`verifier/` deliberately depends on nothing else in the package: a move
sequence counts as a result only when this judge passes it, and a judge
sharing code with the search would not be independent evidence.

## Citing

Cite the **paper**, not the repository; [CITATION.cff](CITATION.cff) carries
this preference machine-readably. The manuscript is a draft and has not been
peer reviewed.

## License

The repository's own code, documentation and generated data are
[MIT-licensed](LICENSE). Two exceptions: `data/longest.pgn` and
`data/skeleton_reference.txt` are Tom Murphy VII's published artefacts,
redistributed with attribution (see [data/README.md](data/README.md)); and
the manuscript under [paper/](paper/) is not covered by the code license —
its license is chosen at submission.

## Attribution

`data/longest.pgn` and `data/skeleton_reference.txt` are Tom Murphy VII's —
the published game and the skeleton inside
[`longest.cc`](https://sourceforge.net/p/tom7misc/svn/HEAD/tree/trunk/chess/longest.cc)
respectively. They are included so the results reproduce offline.

## Acknowledgements

As in the paper: Tom Murphy VII's construction and question motivated this
work, and he kindly commented on a draft, as did Alexis Langlois-Rémillard.
The author is deeply grateful to Jinwan Park for generously taking the time
to discuss this work and for valuable advice and encouragement, and thanks
François Labelle for his detailed historical account of the longest-game
problem.

The author first ran into the problem through the YouTube videos of
[잉체스 (Ingchess)](https://www.youtube.com/channel/UCTNbJ4fyXuIXd_ppmPXyPoQ),
a chess YouTuber and the developer of
[Augment Chess](https://augmentchess.org/) (증강체스) —
[the short](https://www.youtube.com/shorts/ta6hvZS34ro) ·
[the full video](https://www.youtube.com/watch?v=198K9TPT7KI) — whose
description links Labelle's page.

## References

- Murphy VII, [*Is this the longest chess game?*](https://tom7.org/chess/longest.pdf) (SIGBOVIK 2020)
- Labelle, [*The longest possible chess game, and bounds on the number of possible chess games*](https://wismuth.com/chess/longest-game.html) (2015, updated 2020)
- [FIDE Laws of Chess](https://handbook.fide.com/chapter/e012023), Articles 5.2.2, 9.6.1, 9.6.2
- Tromp, [*The longest chess game*](https://tromp.github.io/chess/longest.html) (summary note)
- [python-chess](https://python-chess.readthedocs.io/en/latest/core.html) ·
  [OR-Tools CP-SAT](https://developers.google.com/optimization/cp/cp_solver)
