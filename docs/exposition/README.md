# Munchausen numbers: the exposition

This directory holds a readable account of everything in `docs/library`,
typeset with [Typst](https://typst.app). The library records results in the
order they were found. The exposition sorts them by theme, marks the status
of each one, and points back to the library section that has the details.

## Build

The build needs Typst 0.15 or later. It uses only the fonts that ship with
Typst (New Computer Modern and DejaVu Sans Mono) and no packages. From the
repository root:

```sh
typst compile docs/exposition/main.typ docs/exposition/munchausen.pdf
```

The build must finish without warnings. Commit `munchausen.pdf` together
with the source.

To look at single pages while you write:

```sh
typst compile --format png --ppi 110 --pages 12 docs/exposition/main.typ /tmp/page.png
```

## Layout

| path | contents |
|---|---|
| `main.typ` | title page, contents, the order of chapters and appendices, bibliography |
| `template.typ` | page style, statement boxes, badges, tables, the index of results |
| `lean-status.typ` | which statements are formalized in Lean, and their Lean names |
| `chapters/` | the main text, one file per chapter |
| `appendices/` | primers on the tools used, tables, software, index, notation |
| `bib/main.yml` | the bibliography, in Hayagriva format |
| `data/` | CSV copies of the solution lists, read by the appendix tables |
| `tools/gen_data.py` | rebuilds `data/` from `output/` and `analysis/data/` |

## Statements

Every result sits in a box that says what kind of claim it is. Use the
environments of `template.typ`:

| environment | default status | use for |
|---|---|---|
| `#theorem`, `#proposition`, `#lemma`, `#corollary` | `proven` | results with a proof in the library |
| the same with `status: "cited"` | `cited` | published theorems used without proof |
| the same with `status: "conditional"` | `conditional` | results that assume a conjecture, such as abc |
| `#computation` | `computed` | exhaustive computations; always state the range |
| `#heuristic` | `heuristic` | predictions of the probabilistic model or the root heuristic |
| `#conjecture` | `conjecture` | conjectures |
| `#problem` | `open` | open problems |
| `#definition`, `#remark`, `#example` | none | no claim to mark |

Each environment takes named arguments:

```typst
#theorem(
  id: "thm-binomial",          // label; cite it as @thm-binomial
  title: "Binomial families",   // short name for the header and the index
  src: "22.3",                  // library section, or ("15.7", "18.2")
)[
  Statement.
]
#proof[ ... ]        // or #sketch[ ... ] for a proof sketch
```

`src` prints a badge such as `L22.3`, which means section 22.3 of the
library, `docs/library/22-blocks-families.md`. In running text, write
`#lib("22.3")` for the same pointer and `#q(64)` for question 64 of
`docs/library/questions.md`.

Statements are numbered per chapter and share one counter: Theorem 2.6,
Remark 2.7, and so on. The appendix "Index of results" lists every statement
with its status, library section, page and Lean name. It builds itself.

## Adding a new result

1. Find the chapter whose theme fits. The chapters are listed in `main.typ`.
   Add a section if no section fits, with a label `<sec-...>`.
2. Write the statement with the right environment, `src` and `id`. Keep the
   proof short or give a sketch. Point to the library for the rest.
3. If the result corrects an earlier one, change the earlier statement to the
   current state and add a remark or footnote on the correction.
4. If the result settles or raises an open problem, update chapter 8.
5. If it adds solutions, rerun `tools/gen_data.py` (after the library data
   changes) or edit the hand-written tables in `appendices/k-tables.typ`.
6. Add new references to `bib/main.yml` and cite them with `@key`.
7. Update `version` in `main.typ`, build, check the pages you changed, and
   commit the source with the PDF.

A new chapter is a new file in `chapters/`, included from `main.typ`, that
starts with `#import "../template.typ": *` and a level-1 heading with a label
`<ch-...>`.

## Lean

`lean/` in the repository formalizes results of the library. When a
statement is formalized, add its id and the Lean declaration to
`lean-status.typ`:

```typst
#let lean-names = (
  "thm-length": "Munchausen.length_le_base",
)
```

The box then shows a Lean badge and the name, and the index of results lists
it. `lean/STATUS.md` is the source of truth; keep this file in sync with it.

## Style

- Short sentences and plain words. No em dashes. Sentence-case headings.
- Keep the source ASCII where practical. Typst math turns `<=`, `>=`, `!=`
  and `->` into the right symbols. Escape `#` in text as `\#`.
- Write for a mathematics undergraduate. Tools beyond a first course get a
  primer in an appendix; refer to it.
- Present the current state of knowledge. Mention a corrected claim only
  where the correction teaches something.
