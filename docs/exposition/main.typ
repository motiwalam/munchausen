// Munchausen numbers: an exposition of the library in docs/library.
// Build from the repository root:
//   typst compile docs/exposition/main.typ docs/exposition/munchausen.pdf
// README.md explains how to add material.

#import "template.typ": *

// Update this date when the content changes.
#let version = "19 October 2026"

#show: conf.with(
  title: "Munchausen numbers",
  author: "Mustafa Motiwala",
  version: version,
)

// Title page
#page(header: none, footer: none)[
  #v(4cm)
  #align(center)[
    #text(size: 28pt, weight: "bold")[Munchausen numbers]
    #v(0.6cm)
    #text(size: 14pt)[What is known about numbers equal to the sum \ of their digits raised to themselves]
    #v(1.6cm)
    #text(size: 11pt)[
      $3435 = 3^3 + 4^4 + 3^3 + 5^5$
    ]
    #v(2.4cm)
    #text(size: 12pt)[Mustafa Motiwala]
    #v(0.3cm)
    #text(size: 10pt, fill: luma(80))[An exposition of the library in `docs/library`, \ written with Claude Code]
    #v(1fr)
    #text(size: 10pt, fill: luma(80))[Living document. Version of #version.]
  ]
]

#outline(depth: 2, indent: auto)

#include "chapters/00-preface.typ"
#include "chapters/01-basics.typ"
#include "chapters/02-constructions.typ"
#include "chapters/03-model.typ"
#include "chapters/04-search.typ"
#include "chapters/05-short.typ"
#include "chapters/06-diophantine.typ"
#include "chapters/07-worlds.typ"
#include "chapters/08-open.typ"

#show: appendices

#include "appendices/a-probability.typ"
#include "appendices/b-galois.typ"
#include "appendices/c-padic.typ"
#include "appendices/d-quadratic.typ"
#include "appendices/e-baker.typ"
#include "appendices/f-abc.typ"
#include "appendices/g-curves.typ"
#include "appendices/h-complexity.typ"
#include "appendices/i-numeration.typ"
#include "appendices/j-ffield.typ"
#include "appendices/k-tables.typ"
#include "appendices/l-software.typ"
#include "appendices/m-lean.typ"
#include "appendices/n-index.typ"
#include "appendices/o-notation.typ"

#bibliography(
  ("bib/main.yml", "bib/f1.yml", "bib/f2.yml", "bib/f3.yml", "bib/f4.yml", "bib/f5.yml"),
  title: "Bibliography",
  style: "springer-mathphys",
)
