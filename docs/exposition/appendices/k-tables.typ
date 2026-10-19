#import "../template.typ": *

= Tables of solutions <app-tables>

This appendix lists every known solution in small bases, and the complete
lists of short solutions. The tables are read from the CSV files in
`docs/exposition/data`, which `tools/gen_data.py` copies from `output/` and
`analysis/data/`. Digit strings are written most significant first, with the
digits in decimal.

#let rows-of(path) = csv(path).slice(1)
#let digits(s) = "(" + s.replace(",", ", ") + ")"
#let base-disp(s) = if s.contains("^") {
  let (r, t) = s.split("^")
  $#r^#t$
} else { s }

== Counts per base <sec-app-tables-counts>

@tab-app-counts gives the number of nontrivial solutions in each base from 2
to 41 and in base 43, from the exhaustive search of `fast`
(#lib("4.2")). "Shared" counts the zero-free solutions, which are solutions
under both conventions (@thm-conventions). "Longest" is the largest number
of digits under either convention. Base 42 was searched only for 42-digit
numbers (none under either convention, #lib("8.6")).

#{
  let rows = rows-of("../data/counts-by-base.csv")
  let half = calc.ceil(rows.len() / 2)
  let first = rows.slice(0, half)
  let second = rows.slice(half)
  let cells = ()
  for i in range(half) {
    cells += first.at(i)
    cells.push([])
    if i < second.len() { cells += second.at(i) } else { cells += ([], [], [], [], []) }
  }
  tablefig(
    caption: [Nontrivial solutions per base. $N_0$ and $N_1$ count the solutions under $0^0 = 0$ and $0^0 = 1$.],
    id: "tab-app-counts",
    btable(
      columns: 11,
      align: (right,) * 5 + (center,) + (right,) * 5,
      [base], [$N_0$], [$N_1$], [shared], [longest], [],
      [base], [$N_0$], [$N_1$], [shared], [longest],
      ..cells,
    ),
  )
}

== All solutions in bases 2 to 43 <sec-app-tables-all>

@tab-app-sol1 and @tab-app-sol0 list every nontrivial solution in bases 2 to
41 and 43, from the exhaustive search (`output/b2-41-*.txt`,
`output/b43-*.txt`). Bases 2 to 35 under $0^0 = 1$ agree with OEIS A166623
@oeis-a166623. The lists end with three kinds of partial results, marked in
the last column:

- "inexact": base 44 was searched with the inexact rules
  `--deficit 2 --band 2.5`, which can miss solutions (#lib("9.3"));
- "$<= 30$": bases 44 to 127 were searched only for numbers with at most 30
  digits (`analysis/data/b39-127-d30.txt`), so the lists there are complete
  only up to that length;
- the self-paying and swap families of @ch-constructions add infinitely many
  solutions in perfect-power bases beyond these ranges.

#let solution-table(conv, caption, id) = {
  let rows = rows-of("../data/solutions-by-base.csv").filter(r => r.at(1) == str(conv))
  let cells = ()
  for r in rows {
    let note = if r.at(5) == "inexact" { "inexact" } else if r.at(5) == "upto30" { $<= 30$ } else { "" }
    cells.push(r.at(0))
    cells.push(r.at(2))
    cells.push(text(size: 7pt, digits(r.at(3))))
    cells.push(text(size: 7pt, note))
  }
  tablefig(
    caption: caption,
    id: id,
    btable(
      columns: (auto, auto, 1fr, auto),
      align: (right, right, left, left),
      size: 8pt,
      [base], [$k$], [digits], [],
      ..cells,
    ),
  )
}

#solution-table(1, [All known nontrivial solutions under $0^0 = 1$ in bases 2 to 127. Exhaustive for bases 2 to 41 and 43.], "tab-app-sol1")

#solution-table(0, [All known nontrivial solutions under $0^0 = 0$ in bases 2 to 127. Exhaustive for bases 2 to 41 and 43.], "tab-app-sol0")

== Short solutions in all bases <sec-app-tables-short>

The lists in this section come from `kdigit`, which fixes a digit string and
solves for the base (@sec-search-short). A list for $k$ digits with digits
up to $M$ is complete for every base $b$ with $b^k <= (M + 1)^(M + 1)$
(@thm-digit-bound). @tab-app-short-range gives the ranges. Beyond them,
the binomial families of @thm-binomial give solutions of every length in
very large bases.

#tablefig(
  caption: [Ranges of the complete lists of short solutions (#lib("3.1", "11.5", "19.1")).],
  id: "tab-app-short-range",
  btable(
    columns: 4,
    align: (right, right, right, left),
    [$k$], [digits up to], [complete for bases up to], [source],
    [3], [80], [$10^51.5$], [`analysis/data/k3.txt`],
    [4], [300], [$10^186.5$], [`analysis/data/k4.txt`],
    [5], [80], [$10^30.9$], [`analysis/data/k5.txt`],
    [6], [40], [$10^11.0$], [`analysis/data/k6.txt`],
    [7], [32], [$10^7.2$], [`analysis/data/r3c_k7_M32.txt`],
    [8], [24], [$10^4.4$ (base 23,364)], [`analysis/data/r3c_k8_M24.txt`],
  ),
)

Two-digit solutions are described completely by @thm-two-digit, so they are
not listed. Under $0^0 = 0$ the lists also contain the self-paying families
$(x, 0, dots, 0)$ and $(x, 0, dots, 0, 1)$ with $x^(x-1) = b^(k-1)$ (@sec-cons-every-length).
@tab-app-short1 lists everything under $0^0 = 1$. @tab-app-short0 lists the
solutions under $0^0 = 0$ that are not in these families, and gives the
number of family members in each list.

#let short-rows(conv) = rows-of("../data/short-solutions.csv").filter(r => r.at(1) == str(conv))

#{
  let cells = ()
  for r in short-rows(1) {
    cells.push(r.at(0))
    cells.push(base-disp(r.at(3)))
    cells.push(digits(r.at(4)))
  }
  tablefig(
    caption: [Every solution with 3 to 8 digits under $0^0 = 1$, in the ranges of @tab-app-short-range.],
    id: "tab-app-short1",
    btable(
      columns: 3,
      align: (right, right, left),
      [$k$], [base], [digits],
      ..cells,
    ),
  )
}

#{
  let rows = short-rows(0)
  let cells = ()
  for r in rows.filter(r => r.at(5) == "") {
    cells.push(r.at(0))
    cells.push(base-disp(r.at(3)))
    cells.push(digits(r.at(4)))
  }
  let fam = ()
  for k in range(3, 9) {
    let n = rows.filter(r => r.at(0) == str(k) and r.at(5) != "").len()
    fam.push([#k: #n])
  }
  tablefig(
    caption: [Every solution with 3 to 8 digits under $0^0 = 0$ that is not a self-paying family member $(x, 0, dots, 0, e)$, $e in {0, 1}$, in the ranges of @tab-app-short-range. Family members per length: #fam.join(", ").],
    id: "tab-app-short0",
    btable(
      columns: 3,
      align: (right, right, left),
      [$k$], [base], [digits],
      ..cells,
    ),
  )
}

== Negative bases <sec-app-tables-negative>

@tab-app-negative lists every nontrivial solution in the bases $-2$ to $-38$
(#lib("12.3", "14.3", "23.2")). A string $(s_(k-1), dots, s_0)$ is a
solution in base $-b$ when $sum_i s_i (-b)^i = F(s)$. The census is complete:
`worlds brute` and `worlds lanes` search every length allowed by the length
bound of negative bases (@sec-worlds-negative). Bases not in the table have
no solution under either convention: $-3$, $-6$, $-9$, $-15$, $-18$, $-20$,
$-30$, $-34$ and $-38$.

#{
  let rows = rows-of("../data/negative-bases.csv")
  let cells = ()
  for r in rows {
    cells.push(r.at(0))
    cells.push(if r.at(1) == "1" [$0^0 = 1$] else [$0^0 = 0$])
    cells.push(r.at(2))
    cells.push(text(size: 7pt, digits(r.at(3))))
  }
  tablefig(
    caption: [All nontrivial solutions in the bases $-2$ to $-38$.],
    id: "tab-app-negative",
    btable(
      columns: (auto, auto, auto, 1fr),
      align: (right, left, right, left),
      size: 8pt,
      [base], [convention], [$k$], [digits],
      ..cells,
    ),
  )
}

== Other number systems <sec-app-tables-other>

The solutions in the other number systems of @ch-worlds are short lists. The
chapter states them where they are discussed:

- imaginary bases $c i$ and Gaussian bases $-n + i$: @sec-worlds-complex (#lib("14.4", "14.5", "23.4"));
- Eisenstein bases $-n + omega$: @sec-worlds-complex (#lib("21.3"));
- rational bases $p slash q$: @sec-worlds-rational (#lib("16.5", "21.2"));
- the Pisot bases $(x + sqrt(x^2 + 4)) slash 2$: @sec-worlds-pisot (#lib("21.4"));
- the factorial number system: @sec-worlds-factorial (#lib("21.5"));
- function fields $FF_q [T]$: @sec-worlds-ffield (#lib("21.1", "24.3")).
