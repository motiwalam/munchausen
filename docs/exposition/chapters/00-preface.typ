#import "../template.typ": *

#set heading(numbering: none)

= Preface <ch-preface>

In base 10 the number 3435 has a curious property:
$ 3435 = 3^3 + 4^4 + 3^3 + 5^5. $
A number that equals the sum of its digits, each raised to its own power, is
a _Munchausen number_. This document collects what is known about them in
every base, and in some number systems that are not bases at all.

The material comes from a research library kept in the same repository, in
`docs/library`. The library grew in rounds of questions and answers, so its
28 chapters follow the order in which things were found, and later chapters
correct earlier ones. This document sorts the results by theme and states
each one in its current form. It is written for a mathematics undergraduate
who enjoys number theory and is willing to meet a few tools from beyond a
first course; the appendices introduce those tools.

== How to read the boxes

Every claim sits in a box with a coloured badge that says what kind of claim
it is.

#btable(
  columns: (auto, 1fr),
  align: (left, left),
  [badge], [meaning],
  [#status-badge("proven")], [the library has a proof; this document gives the proof or a sketch when it helps],
  [#status-badge("cited")], [a published theorem, used without proof, with a reference],
  [#status-badge("conditional")], [a proof that assumes a conjecture, such as abc],
  [#status-badge("computed")], [an exhaustive computation; its range is part of the statement],
  [#status-badge("heuristic")], [a prediction of a probabilistic model, with the data that test it],
  [#status-badge("conjecture")], [a conjecture, with its evidence],
  [#status-badge("open")], [an open problem],
)

A badge such as #badge("L8.3", col-proven, light: true), or a pointer
#lib("8.3") in the text, refers to section 8.3 of the library, in the file
`docs/library/8-barriers.md`. There the reader finds the full proof, the
script that made a computation, and its data. A pointer such as #q(64)
refers to question 64 of `docs/library/questions.md`.

The difference between the badges matters in this subject more than in most.
Many statements about Munchausen numbers can be checked by computer up to
enormous bounds and are still not theorems. One of the stories of the
library is a conjecture that looked safe: that under $0^0 = 1$ only finitely
many bases have a solution with three digits. Every base up to $10^51$ had
been searched, and a heuristic put the chance of a further solution below
$10^(-70)$. Then an algebraic family turned up with a 3-digit solution in a
base near $10^108942$ (@thm-binomial). The heuristic was right about random
coincidences and blind to identities. @ch-constructions tells this story.

== What is known, in brief

- A solution in base $b$ has at most $b$ digits, so every base has finitely
  many (@thm-length). The search over all digit multisets is exact and has
  found every solution in bases 2 to 41 and 43 (@sec-basics-data,
  @app-tables).
- Some solutions come from identities between powers: twins, self-paying
  digits, swaps, the two-digit families, the binomial families and a second family of power identities
  (@ch-constructions). Under either convention every length $k >= 3$ has
  infinitely many solutions (@thm-every-length-m0, @thm-every-length-m1).
- The other solutions behave like coincidences. A probabilistic model
  predicts about one solution per base and convention, a Poisson count, the
  length law 8/55/23%, and the doubling of odd bases under $0^0 = 0$
  (@ch-model). It fails in instructive ways in other number systems
  (@sec-worlds-ffield, @sec-worlds-factorial).
- The exact search costs about $1.9^b$. In the model no tree search can do
  better than about $1.64^b$, and a proof of any lower bound would settle
  P versus NP (@ch-search). The digit-sum identity still gives a constant
  factor, at the nodes that miss only one digit (@sec-search-residue).
- For a fixed number of digits the question becomes one polynomial equation
  in the base. Local obstructions, Galois groups and a root heuristic
  describe the short solutions, and almost all bases have none
  (@ch-short). For 3 digits, a 2-adic form of Baker's theorem excludes
  whole families with an even large digit (@sec-short-regimes).
- The 3-digit solution $(1, 7, 1)$ in base 904 leads to the equation
  $b(b + x) = x^x + 1$ and its relatives, which need quadratic fields,
  linear forms in logarithms and the abc conjecture (@ch-diophantine).
- Negative, complex, rational, Pisot, factorial and function-field bases
  show which laws are universal (@ch-worlds).
- Factorials behave differently from $x^x$. Since $x!$ is divisible by
  every prime up to $x$, congruences prove that 3-digit factorions with one
  large digit are finite, except for a case of Brocard's problem
  $n! + 1 = m^2$ (@sec-worlds-short-factorions). Since $x!$ is almost
  never a power, factorials have no identity families (@sec-cons-weights).
  Under abc, every 3-digit solution of $x^x$ with one dominant digit is a
  family member (@short-abc-three).
- Some of the questions connect to other fields: anti-concentration in
  probability, the map $x |-> x^x$ modulo a prime, and sums of two squares
  (@sec-open-connections).
- @ch-open lists the open problems.

== A living document

New results keep arriving in the library. Each chapter here is a separate
file, and every statement carries its own status and pointer, so a new
result goes into the chapter of its theme without changes elsewhere. The
file `docs/exposition/README.md` explains how. The index of results
(@app-index) builds itself from the boxes, and results that are formalized
in Lean are marked automatically (@app-lean).

The library and this exposition were written with Claude Code, an AI coding
agent, under the direction of the author. The computations were run on a
laptop with the programs described in @app-software.
