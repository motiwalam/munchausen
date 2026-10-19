#import "../template.typ": *

= Formalization in Lean <app-lean>

A formalization of the library in Lean 4 with Mathlib @lean4 is being built
in the directory `lean/` of the repository. A statement of this document
that has a formal proof carries a green Lean badge, and its box ends with the
name of the Lean declaration. The index of results (@app-index) lists all of
them.

== Status <sec-app-lean-status>

#context {
  let metas = query(<stmt-meta>).filter(m => m.value.lean != none)
  if metas.len() == 0 [
    As of this version no statement of the document is marked as formalized.
    The Lean project contains the Mathlib setup and no Munchausen results
    yet. This section updates itself when `lean-status.typ` names a Lean
    declaration for a statement.
  ] else [
    #metas.len() statements are formalized. They are:

    #table(
      columns: (auto, 1fr, auto),
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
          raw(v.lean),
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
