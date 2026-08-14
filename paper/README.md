# The paper

`main.tex` is the manuscript — the main artifact this repository exists
to support. The committed `main.pdf` is its build output, kept so the
paper is readable without a TeX toolchain; regenerate it after any edit.

## Build

Any of:

```bash
tectonic main.tex
```

```bash
latexmk -pdf main.tex
```

Plain `pdflatex main.tex` twice also works — the bibliography is inline
(`thebibliography`), so no BibTeX pass is needed.

`make paper`, from the repository root, builds with
`SOURCE_DATE_EPOCH=0`, which pins the PDF's embedded timestamps: the
committed PDF reproduces byte for byte from a clean checkout.

## Slides

The talk decks live outside this repository, so that editing a slide does
not mean cutting a new release of the paper's companion code. They need
`data/longest.pgn` from here to regenerate their board diagrams.
