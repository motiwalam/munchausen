#import "../template.typ": *

= Formalization in Lean <app-lean>

A formalization of the library in Lean 4 with Mathlib @lean4 is being built
in the directory `lean/` of the repository. Its record, `lean/STATUS.md`,
maps every proven result of the library to a Lean declaration or gives the
reason why it is not formalized: usually a heuristic statement, a large
computation, or a deep cited theorem such as Chebotarev's or Laurent's. A statement of this document
that has a formal proof carries a green Lean badge, and its box ends with the
name of the Lean declaration. The table below lists all of them, and the
index of results (@app-index) marks them.

== Status <sec-app-lean-status>

#context {
  let metas = query(<stmt-meta>).filter(m => m.value.lean != none)
  if metas.len() == 0 [
    As of this version no statement of the document is marked as formalized.
  ] else [
    #metas.len() statements of this document are formalized, some of them in part; the table names what a partial formalization covers. All Lean names live in the namespace `Munchausen`. The formalization also states several conjectures of the library as propositions and proves the negation of four refuted ones, among them the finiteness conjecture for short solutions under $0^0 = 1$ (@thm-every-length-m1).

    #set par(justify: false)
    #table(
      columns: (auto, 1fr, 1.6fr),
      stroke: none,
      inset: (x: 4pt, y: 2.6pt),
      table.hline(stroke: 0.8pt),
      table.header([*Statement*], [*Name*], [*Lean declaration*]),
      table.hline(stroke: 0.5pt),
      ..metas.map(m => {
        let v = m.value
        let num = chapter-prefix(m.location()) + "." + str(stmt-counter.at(m.location()).last())
        (
          if v.id != none { link(label(v.id), [#v.kind #num]) } else [#v.kind #num],
          if v.title != none { v.title } else [],
          text(font: font-mono, size: 7.5pt, v.lean),
        )
      }).flatten(),
      table.hline(stroke: 0.8pt),
    )
  ]
}

== How the marks are kept up to date <sec-app-lean-update>

`lean/STATUS.md` in the repository is the record of what is formalized. The
file `docs/exposition/lean-status.typ` maps the id of each statement of this
document to its Lean declaration. When a result is formalized, add a line
such as

```typst
"thm-length": "Munchausen.length_le_base",
```

and rebuild. The badge, the name in the box and the tables of this appendix
and of @app-index follow from that one line.

A formal proof covers exactly the statement in Lean, which can be narrower
than the statement in the box: for example one convention, or a bound with
explicit constants. Where the two differ, the box should say so in a remark.
