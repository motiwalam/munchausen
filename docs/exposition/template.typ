// Shared styling and environments for the exposition.
//
// Every chapter and appendix starts with
//   #import "../template.typ": *
// and uses the environments below. README.md explains how to add material.

#import "lean-status.typ": lean-names

// ---------------------------------------------------------------------------
// Colours and fonts

#let font-text = "New Computer Modern"
#let font-math = "New Computer Modern Math"
#let font-mono = "DejaVu Sans Mono"

#let col-proven = rgb("#1f4e79")
#let col-cited = rgb("#5b3a8c")
#let col-computed = rgb("#1d6b5f")
#let col-heuristic = rgb("#8a5a00")
#let col-conjecture = rgb("#a8322d")
#let col-conditional = rgb("#4a5560")
#let col-definition = rgb("#555555")
#let col-lean = rgb("#2e7d32")
#let col-link = rgb("#1f4e79")

// The status of a statement decides the colour of its box and its badge.
#let statuses = (
  proven: (name: "Proven", color: col-proven),
  cited: (name: "Cited", color: col-cited),
  computed: (name: "Computation", color: col-computed),
  heuristic: (name: "Heuristic", color: col-heuristic),
  conjecture: (name: "Conjecture", color: col-conjecture),
  conditional: (name: "Conditional", color: col-conditional),
  open: (name: "Open", color: col-conjecture),
)

// ---------------------------------------------------------------------------
// Library pointers. lib("8.3") prints "L8.3": section 8.3 of the library in
// docs/library. Several arguments print "L8.3, L22.3".

#let lib-files = (
  "1": "1-basics.md", "2": "2-constructions.md", "3": "3-lengths.md",
  "4": "4-counts.md", "5": "5-model.md", "6": "6-search.md", "7": "7-open.md",
  "8": "8-barriers.md", "9": "9-inexact.md", "10": "10-limits.md",
  "11": "11-local.md", "12": "12-polynomial.md", "13": "13-complexity.md",
  "14": "14-other-bases.md", "15": "15-dynamics.md", "16": "16-algebra.md",
  "17": "17-weights.md", "18": "18-number-theory.md",
  "19": "19-sieve-spectra.md", "20": "20-multisets-residues.md",
  "21": "21-five-systems.md", "22": "22-blocks-families.md",
  "23": "23-factorions-negative.md", "24": "24-ffield-gap.md",
)

#let lib(..secs) = {
  let items = secs.pos().map(s => text(fill: col-link, [L#s]))
  items.join(", ")
}

// Question numbers of docs/library/questions.md: q(64) prints "Q64".
#let q(n) = text(fill: col-link, [Q#n])

// ---------------------------------------------------------------------------
// Badges

#let badge(label, color, light: false) = box(
  inset: (x: 3.5pt, y: 1.5pt),
  outset: (y: 1pt),
  radius: 2pt,
  fill: if light { color.lighten(85%) } else { color },
  text(
    size: 7.5pt,
    weight: "bold",
    fill: if light { color.darken(10%) } else { white },
    font: font-text,
    upper(label),
  ),
)

#let status-badge(status) = {
  let s = statuses.at(status)
  badge(s.name, s.color)
}

// ---------------------------------------------------------------------------
// Numbering. Chapters are numbered 1, 2, ...; appendices A, B, ...
// Statements share one counter per chapter: Theorem 2.1, Remark 2.2, ...

#let appendix-state = state("in-appendix", false)
#let stmt-kind = "stmt"
#let stmt-counter = counter(figure.where(kind: stmt-kind))

#let chapter-prefix(loc) = {
  let h = counter(heading).at(loc)
  let ch = if h.len() > 0 { h.first() } else { 0 }
  if appendix-state.at(loc) { numbering("A", calc.max(ch, 1)) } else { str(ch) }
}

#let stmt-numbering = (..n) => context {
  let prefix = chapter-prefix(here())
  prefix + "." + str(n.pos().last())
}

// ---------------------------------------------------------------------------
// Statements
//
// kind:     the printed name ("Theorem", "Computation", ...)
// status:   a key of `statuses`, or none for definitions and remarks
// id:       a label name such as "thm-length"; references use @thm-length
// title:    a short name, shown in the header and in the index of results
// src:      library sections, a string or an array: "8.3" or ("15.7", "18.2")
// lean:     a Lean declaration; auto looks the id up in lean-status.typ
// style:    "box" (coloured box) or "plain" (remarks, examples)

#let statement(
  kind,
  body,
  status: none,
  id: none,
  title: none,
  src: none,
  lean: auto,
  style: "box",
) = {
  // A string title may contain math such as "$0^0 = 0$".
  let title = if type(title) == str { eval(title, mode: "markup") } else { title }
  let srcs = if src == none { () } else if type(src) == array { src } else { (src,) }
  let lean-name = if lean == auto {
    if id != none { lean-names.at(id, default: none) } else { none }
  } else { lean }
  let color = if status != none { statuses.at(status).color } else { col-definition }

  let badges = {
    if status != none { status-badge(status) }
    for s in srcs { h(3pt); badge("L" + s, col-proven, light: true) }
    if lean-name != none { h(3pt); badge("Lean", col-lean) }
  }

  let header = context {
    let num = stmt-counter.display(stmt-numbering)
    block(below: 0.75em, sticky: true, grid(
      columns: (1fr, auto),
      column-gutter: 6pt,
      align: (left + bottom, right + bottom),
      [#strong[#kind #num]#if title != none [ (#title)].],
      badges,
    ))
  }

  let meta = metadata((
    kind: kind,
    status: status,
    id: id,
    title: title,
    src: srcs,
    lean: lean-name,
  ))

  let inner = if style == "box" {
    block(
      width: 100%,
      breakable: true,
      inset: (left: 9pt, right: 8pt, top: 7pt, bottom: 8pt),
      fill: color.lighten(93%),
      stroke: (left: 2.5pt + color),
      radius: (right: 2pt),
      {
        set par(first-line-indent: 0pt)
        [#meta <stmt-meta>]
        header
        body
        if lean-name != none {
          v(3pt, weak: true)
          align(right, text(size: 7.5pt, fill: col-lean)[Lean: #raw(lean-name)])
        }
      },
    )
  } else {
    block(
      width: 100%,
      breakable: true,
      inset: (left: 9pt, y: 3pt),
      stroke: (left: 0.6pt + luma(160)),
      {
        set par(first-line-indent: 0pt)
        [#meta <stmt-meta>]
        header
        body
      },
    )
  }

  let fig = figure(
    kind: stmt-kind,
    supplement: kind,
    numbering: stmt-numbering,
    outlined: false,
    inner,
  )
  if id != none [#fig#label(id)] else { fig }
}

#let theorem(body, status: "proven", ..args) = statement("Theorem", body, status: status, ..args)
#let proposition(body, status: "proven", ..args) = statement("Proposition", body, status: status, ..args)
#let lemma(body, status: "proven", ..args) = statement("Lemma", body, status: status, ..args)
#let corollary(body, status: "proven", ..args) = statement("Corollary", body, status: status, ..args)
#let computation(body, status: "computed", ..args) = statement("Computation", body, status: status, ..args)
#let heuristic(body, status: "heuristic", ..args) = statement("Heuristic", body, status: status, ..args)
#let conjecture(body, status: "conjecture", ..args) = statement("Conjecture", body, status: status, ..args)
#let problem(body, status: "open", ..args) = statement("Problem", body, status: status, ..args)
#let definition(body, ..args) = statement("Definition", body, ..args)
#let remark(body, ..args) = statement("Remark", body, style: "plain", ..args)
#let example(body, ..args) = statement("Example", body, style: "plain", ..args)

// Proofs. #proof[...] ends with a square; #sketch[...] is a proof sketch.
#let qed = h(1fr) + box(width: 0.5em, height: 0.5em, stroke: 0.5pt)

#let proof(body, name: "Proof") = block(
  width: 100%,
  breakable: true,
  inset: (left: 0pt, y: 2pt),
  {
    set par(first-line-indent: 0pt)
    [_#name._ ]
    body
    qed
  },
)
#let sketch(body) = proof(body, name: "Proof sketch")

// ---------------------------------------------------------------------------
// Tables: horizontal rules only.

#let rule = table.hline(stroke: 0.6pt)
#let midrule = table.hline(stroke: 0.4pt)

// btable(columns: 3, align: (left, right, right), [head], [head], [head], ..cells)
// The first `header-rows` rows form the header.
#let btable(columns: 1, align: auto, header-rows: 1, size: 9pt, ..cells) = {
  let n = if type(columns) == int { columns } else { columns.len() }
  let all = cells.pos()
  let head = all.slice(0, calc.min(all.len(), n * header-rows))
  let rest = all.slice(calc.min(all.len(), n * header-rows))
  set text(size: size)
  table(
    columns: columns,
    align: align,
    stroke: none,
    inset: (x: 5pt, y: 3.2pt),
    table.hline(stroke: 0.8pt),
    table.header(..head.map(c => strong(c))),
    table.hline(stroke: 0.5pt),
    ..rest,
    table.hline(stroke: 0.8pt),
  )
}

// A table with a caption, numbered per chapter as "Table 3.2".
#let tablefig(caption: none, id: none, body) = {
  let f = figure(body, caption: caption, kind: table, supplement: [Table])
  if id != none [#f#label(id)] else { f }
}

// Digit strings: #ds("3,4,3,5") prints (3, 4, 3, 5) in math.
#let ds(s) = {
  let parts = s.split(",").map(x => x.trim())
  $(#parts.join(", "))$
}

// ---------------------------------------------------------------------------
// The document

#let conf(
  title: none,
  subtitle: none,
  author: none,
  version: none,
  doc,
) = {
  set document(title: title, author: author)
  set text(font: font-text, size: 10.5pt, lang: "en")
  show math.equation: set text(font: font-math)
  show raw: set text(font: font-mono, size: 0.85em)
  set par(justify: true, leading: 0.62em, spacing: 1.05em, first-line-indent: 0pt)
  set list(indent: 0.8em)
  set enum(indent: 0.8em)
  set footnote.entry(separator: line(length: 30%, stroke: 0.5pt))
  show outline.entry.where(level: 1): it => {
    v(0.5em, weak: true)
    strong(it)
  }
  show link: set text(fill: col-link)
  show ref: set text(fill: col-link)
  // Numbers of figures, statements and equations carry the chapter of the
  // element, not of the reference, so build them at the element.
  show ref: it => {
    let el = it.element
    if el == none { return it }
    if el.func() == figure {
      let loc = el.location()
      let n = counter(figure.where(kind: el.kind)).at(loc).last()
      let num = chapter-prefix(loc) + "." + str(n)
      let sup = if it.supplement == auto { el.supplement } else { it.supplement }
      link(loc, [#sup~#num])
    } else if el.func() == math.equation and el.numbering != none {
      let loc = el.location()
      let n = counter(math.equation).at(loc).last()
      link(loc, "(" + chapter-prefix(loc) + "." + str(n) + ")")
    } else { it }
  }

  set heading(numbering: "1.1", supplement: [Section])
  show heading.where(level: 1): set heading(supplement: [Chapter])
  show heading: set text(weight: "bold")
  show heading.where(level: 2): set text(size: 13pt)
  show heading.where(level: 3): set text(size: 11pt)
  show heading.where(level: 2): set block(above: 1.6em, below: 0.9em)
  show heading.where(level: 3): set block(above: 1.3em, below: 0.7em)

  // Number equations per chapter, but only those with a label.
  set math.equation(numbering: (..n) => context {
    "(" + chapter-prefix(here()) + "." + str(n.pos().last()) + ")"
  })
  show math.equation.where(block: true): it => {
    if it.numbering != none and not it.has("label") {
      counter(math.equation).update(v => v - 1)
      math.equation(it.body, block: true, numbering: none)
    } else {
      it
    }
  }

  // Figures and tables are numbered per chapter.
  set figure(numbering: (..n) => context {
    chapter-prefix(here()) + "." + str(n.pos().last())
  })
  set figure.caption(separator: [. ])
  show figure.caption: set text(size: 9pt)
  show figure.where(kind: table): set figure.caption(position: top)
  show figure.where(kind: table): set block(breakable: true)
  show figure.where(kind: stmt-kind): set block(breakable: true)
  show figure.where(kind: stmt-kind): it => {
    set align(left)
    block(above: 1.1em, below: 1.1em, it.body)
  }

  // Chapters start on a new page and reset the per-chapter counters.
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    stmt-counter.update(0)
    counter(figure.where(kind: table)).update(0)
    counter(figure.where(kind: image)).update(0)
    counter(math.equation).update(0)
    set par(justify: false)
    v(1.5cm)
    if it.numbering != none {
      context {
        let label = if appendix-state.get() { "Appendix" } else { "Chapter" }
        text(size: 12pt, fill: luma(90), weight: "regular",
          smallcaps(label + " " + counter(heading).display(it.numbering)))
      }
      v(0.35cm)
    }
    text(size: 20pt, weight: "bold", it.body)
    v(0.9cm)
  }

  set page(
    paper: "a4",
    margin: (x: 2.6cm, top: 2.7cm, bottom: 2.6cm),
    header: context {
      let page = here().page()
      let starts = query(heading.where(level: 1)).filter(h => h.location().page() == page)
      if starts.len() > 0 or page <= 2 { return none }
      let before = query(heading.where(level: 1).before(here()))
      if before.len() == 0 { return none }
      let h = before.last()
      set text(size: 8.5pt, fill: luma(90))
      let num = if h.numbering != none {
        numbering(h.numbering, ..counter(heading).at(h.location())) + "  "
      } else { "" }
      grid(columns: (1fr, auto), [#smallcaps(title)], [#num#h.body])
      v(-6pt)
      line(length: 100%, stroke: 0.4pt + luma(170))
    },
    footer: context {
      if here().page() > 1 {
        align(center, text(size: 9pt, counter(page).display()))
      }
    },
  )

  doc
}

// Switch to appendix numbering: A, A.1, ...
#let appendices(body) = {
  appendix-state.update(true)
  counter(heading).update(0)
  set heading(numbering: "A.1")
  show heading.where(level: 1): set heading(supplement: [Appendix])
  body
}

// ---------------------------------------------------------------------------
// The index of results: every statement with its status, source and page.

#let results-index() = context {
  let metas = query(<stmt-meta>)
  let rows = ()
  for m in metas {
    let v = m.value
    if v.status == none { continue }
    let loc = m.location()
    let n = stmt-counter.at(loc).last()
    let num = chapter-prefix(loc) + "." + str(n)
    let name = if v.id != none { link(label(v.id), [#v.kind #num]) } else [#v.kind #num]
    rows.push((
      name,
      if v.title != none { v.title } else [],
      status-badge(v.status),
      v.src.map(s => [L#s]).join(", "),
      link(loc, str(loc.page())),
      if v.lean != none { raw(v.lean) } else [],
    ))
  }
  set text(size: 8.5pt)
  table(
    columns: (auto, 1fr, auto, auto, auto, auto),
    align: (left, left, left, left, right, left),
    stroke: none,
    inset: (x: 4pt, y: 2.6pt),
    table.hline(stroke: 0.8pt),
    table.header([*Statement*], [*Name*], [*Status*], [*Library*], [*Page*], [*Lean*]),
    table.hline(stroke: 0.5pt),
    ..rows.flatten(),
    table.hline(stroke: 0.8pt),
  )
}

// Count statements by status, for the summary in the index appendix.
#let results-summary() = context {
  let metas = query(<stmt-meta>)
  let counts = (:)
  let lean = 0
  for m in metas {
    let v = m.value
    if v.status == none { continue }
    counts.insert(v.status, counts.at(v.status, default: 0) + 1)
    if v.lean != none { lean += 1 }
  }
  let cells = ()
  for (k, s) in statuses {
    if counts.at(k, default: 0) > 0 {
      cells.push(status-badge(k))
      cells.push([#counts.at(k)])
    }
  }
  cells.push(badge("Lean", col-lean))
  cells.push([#lean])
  grid(columns: (auto, auto) * 4, column-gutter: 10pt, row-gutter: 6pt, align: (left + horizon, right + horizon) * 4, ..cells)
}
