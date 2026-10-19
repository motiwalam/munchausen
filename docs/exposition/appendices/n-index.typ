#import "../template.typ": *

= Index of results <app-index>

This index lists every statement of the document that makes a claim, in
order, with its status, the library sections that hold the details, and the
page. Definitions, remarks and examples are left out. The index builds
itself from the statement boxes, so it is always complete.

The statuses mean:

#btable(
  columns: (auto, 1fr),
  align: (left, left),
  [status], [meaning],
  [#status-badge("proven")], [a proof is in the library, and usually a proof or sketch is here],
  [#status-badge("cited")], [a published theorem, used without proof],
  [#status-badge("conditional")], [proven under a stated conjecture or assumption, such as abc],
  [#status-badge("computed")], [an exhaustive computation; the range is part of the statement],
  [#status-badge("heuristic")], [a prediction of the probabilistic model or the root heuristic, tested against data],
  [#status-badge("conjecture")], [a conjecture, with its evidence in the text],
  [#status-badge("open")], [an open problem],
)

Totals in this version:

#results-summary()

#v(0.8em)

#results-index()
