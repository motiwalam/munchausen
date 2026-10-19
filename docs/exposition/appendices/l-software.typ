#import "../template.typ": *

= Software and data <app-software>

Every computation in this document can be repeated with the programs in the
repository. This appendix says what each program does, how the results were
checked, and where the data lives. The library cites the script behind each
number; the badges $L x.y$ lead to it.

== The repository <sec-app-software-layout>

#tablefig(
  caption: [The parts of the repository.],
  id: "tab-app-software-layout",
  btable(
    columns: (auto, 1fr),
    align: (left, left),
    [path], [contents],
    [`src/`], [the original Python search over digit multisets, and the output format (`formatutil.py`)],
    [`fast/`], [the Rust programs: the exact search `fast`, `kdigit` for short solutions, and engines for other number systems],
    [`output/`], [the exhaustive lists of solutions: `b2-41-0.txt`, `b2-41-1.txt`, `b43-*.txt`],
    [`analysis/`], [Python, PARI/GP, Sage and C scripts for the model, the number theory and the experiments],
    [`analysis/data/`], [the output of every script, cited by file name in the library],
    [`docs/algorithm.md`], [the search algorithm in detail],
    [`docs/library/`], [the library: 24 chapters and the open questions],
    [`docs/exposition/`], [this document],
    [`lean/`], [the Lean 4 formalization (@app-lean)],
  ),
)

== The exact search <sec-app-software-fast>

`fast search` finds every solution in a base under both conventions in one
run. It is the prefix-pruned tree of @sec-search-tree: it fixes the counts of
the digits from the largest down, keeps an interval for the sum, and uses the
leading digits that the interval shares. Numbers are stored as one byte per
base-$b$ digit in AVX2 registers, so the program needs no big-number library
and handles bases up to 127 and numbers up to 62 digits. A carry-lookahead
identity on bit masks adds two such vectors in about 15 instructions.

Large runs are split into about $10^5$ work units in a fixed order. With
`--journal` the program records each finished unit and each solution at once,
so a stopped run resumes where it stopped. `--shard i/n` splits a base over
machines, and `fast merge` combines the outputs. A GPU path (Vulkan) gives
the same results and node counts.

Other options change the weights for experiments on the model:
`--zero`, `--shift`, `--factorial`, `--power`, `--perturb`,
`--keep-residues` and `--set-residue` (@sec-model-tests,
@sec-worlds-weights). The inexact rules `--cap`, `--band`, `--deficit`,
`--ratio` and `--zscore` skip nodes that the model calls unlikely, and print
the expected number of missed solutions (@sec-search-inexact). With
`--offset D` the search counts the near-solutions $n - F(n) = D$
(@sec-model-defects).

Base 37 takes about 205 seconds on an 8-thread laptop, and each further base
costs about 1.9 times more.

== Short solutions <sec-app-software-kdigit>

`fast/target/release/kdigit k M` lists every $k$-digit solution in every base
$b$ with $b^k <= (M+1)^(M+1)$. It enumerates digit strings, tests the
polynomial $Q_s$ for a root modulo a list of prime powers (default 32, 27,
25, 49 and the primes 11 to 127), and solves $P_s (b) = F(s)$ exactly for the
few strings that pass (@sec-search-short, @sec-short-local). Options:
`--offset D`, `--moduli`, `--stats`, `--survivors`. The Python version
`analysis/kdigit.py` is the slow reference.

== Engines for other systems <sec-app-software-worlds>

#tablefig(
  caption: [The engines in `fast/src/bin/`.],
  id: "tab-app-software-engines",
  btable(
    columns: (auto, 1fr, auto),
    align: (left, left, left),
    [program], [what it does], [used in],
    [`worlds`], [negative bases ($-2$ to $-38$), imaginary bases, factorions; engines `brute`, `tree`, `lanes`], [@sec-worlds-negative],
    [`gauss`], [Gaussian bases $-n + i$], [@sec-worlds-complex],
    [`r3t_eisen`], [Eisenstein bases $-n + omega$, with a Gaussian control], [@sec-worlds-complex],
    [`r3t_afs`], [rational bases $p slash q$ by a tree of parents], [@sec-worlds-rational],
    [`r3t_pisot`], [the Pisot bases $(x + sqrt(x^2 + 4)) slash 2$ in exact arithmetic of $ZZ[epsilon]$], [@sec-worlds-pisot],
    [`r3t_factorial`], [the factorial number system up to $34!$], [@sec-worlds-factorial],
    [`r3t_ffield`, `r4f_ffield`], [function fields $FF_q [T]$; the second uses the Frobenius blocks], [@sec-worlds-ffield],
    [`dyn_cycles`, `r2c_cycles2`], [cycles and near-2-cycles of $n |-> F(n)$ on digit multisets], [@sec-model-cycles],
  ),
)

== Analysis scripts <sec-app-software-analysis>

The scripts in `analysis/` carry a prefix for the round of work that wrote
them. Each library chapter ends with a table of its scripts and data files.

#tablefig(
  caption: [Prefixes of the analysis scripts.],
  id: "tab-app-software-prefixes",
  btable(
    columns: (auto, 1fr, auto),
    align: (left, left, left),
    [prefix], [topic], [library],
    [(none)], [model, counts, tree measurements, inexact rules, defects, local tests], [L1 to L12],
    [`thy_`], [the NP-completeness reduction and the Poisson theorem], [L13],
    [`wld_`], [negative, imaginary and Gaussian bases, factorions], [L14],
    [`dyn_`], [cycles, two-digit bases, coverings, constructions, several bases], [L15],
    [`alg_`], [Aurifeuillian factors, reducibility, Galois groups, rational roots], [L16],
    [`wgt_`], [other weights], [L17],
    [`r2nt_`], [the equation $b(b + x) = x^n + 1$], [L18],
    [`r3c_`], [the prime-power sieve, short-string spectra, narcissistic numbers], [L19],
    [`r3nt_`], [multisets, residues of $x^x - x$, the even case, $c = 3, 25$], [L20],
    [`r3t_`], [five more number systems], [L21],
    [`r4b_`], [blocks and binomial families], [L22],
    [`r2c_`], [factorions, empty negative bases, cycles, scatter], [L23],
    [`r4f_`], [function fields: why the model misses], [L24],
  ),
)

The number theory uses PARI/GP @pari2024 for class groups (`bnfinit`, with
`bnfcertify` where a result must not depend on GRH), regulators and integral
points, and Sage @sagemath for elliptic curves.

== How the results were checked <sec-app-software-checks>

- `fast` recomputes $F(n)$ with arbitrary-precision integers before it prints
  a solution. `cargo test` compares it with a brute force (bases 2 to 9) and
  with a plain `u128` reference search (bases 10 to 22).
- The lists of bases 2 to 41 agree with the older Python search for bases 2
  to 19, and with OEIS A166623 for bases 2 to 35 under $0^0 = 1$.
- Every option for other weights is tested against a brute force over all
  digit multisets in bases 2 to 8.
- `kdigit` reproduces the Python lists line for line, and the prime-power
  sieve reproduces the prime sieve.
- The engines for other systems agree with each other and with brute force
  where both run, as the library records for each one.
- The script `analysis/verify_constructions.py` checks the families of
  @ch-constructions with exact integers.

== Data in this directory <sec-app-software-data>

`docs/exposition/data/` holds CSV copies of the lists that @app-tables
prints: `counts-by-base.csv`, `solutions-by-base.csv`,
`short-solutions.csv` and `negative-bases.csv`. Run

```sh
python3 docs/exposition/tools/gen_data.py
```

after the lists in `output/` or `analysis/data/` change, then rebuild the
document.
