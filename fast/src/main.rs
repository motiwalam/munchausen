mod digits;
mod journal;
mod port;
mod reference;
mod search;
#[cfg(feature = "gpu")]
mod vk;

use num_bigint::{BigInt, BigUint};
use std::time::Instant;

const USAGE: &str = "\
usage: fast <engine> <base> [<last base>] [options]

engines:
  search      fast prefix-pruned digit-count search (bases 2..=127, at most 62 digits)
  port        faithful port of the python algorithm (bases 2..=26)
  reference   simple u128 version of the search, for validation (bases 2..=27)
  brute       check every n up to the upper bound (tiny bases only)

options:
  -m, --mode <0|1|both>   value of 0^0 (default: both)
  -j, --threads <n>       worker threads (default: all cores)
  --journal <file>        (search) record finished work units and solutions in
                          <file> and resume from it if it exists; \"{base}\"
                          in the name is replaced by the base
  --progress              (search) report progress every 10 seconds
  --max-digits <n>        (search) only look for numbers with at most n digits
  --min-digits <n>        (search) only look for numbers with at least n digits
  --cap <c>               (search, inexact) skip numbers in which a digit 2 or more
                          occurs more than c times
  --band <z>              (search, inexact) skip numbers whose count of digits >= k
                          is more than z standard deviations from a random
                          number's, at any k >= 2
  --deficit <z>           (search, inexact) skip nodes whose known leading digits
                          hold z standard deviations fewer digits >= k than a
                          random arrangement would
  --epsilon <e>           (search, inexact) skip subtrees in which the model expects
                          fewer than e solutions; the total expected number of
                          skipped solutions is reported
  --ratio <r>             (search, inexact) skip a child whose expected number of
                          solutions is below r times its parent's
  --perturb <seed>        (experiment) replace each weight w(x), x >= 2, by w(x)
                          plus a pseudo-random amount below w(x)/4
  --keep-residues         (experiment) with --perturb, keep the weights modulo 2(b-1)
  --offset <D>            (experiment) find the numbers n with n = F(n) + D instead;
                          output is not checked
  --zero <m>              (experiment) weight of the digit 0 in the second
                          convention (default 1); the first keeps 0^0 = 0
  --shift <t>             (experiment) weights x^(x+t) for x >= 1, t >= -1
  --factorial             (experiment) weights x! for x >= 1
  --set-residue <r>       (experiment) raise each weight w(x), x >= 1, by the
                          least amount that makes it x + r modulo b-1; it acts
                          after --perturb
  --zscore <z>            (search, inexact) skip a node whose expected number of
                          solutions is more than z standard deviations below its
                          mean for a random suffix (typical-set test)
  --uniform               (search, inexact) measure --band and --deficit on the
                          scale of the whole random walk instead of pointwise
  --unit-depth <n>        (search) tree depth at which the search is cut into
                          resumable units (default: 4)
  --par-depth <n>         (search) further depth below a unit down to which
                          work is split into parallel tasks (default: 4)
  --gpu                   (search, exact only) run the search on the GPU through
                          Vulkan; needs a build with --features gpu
  --hybrid                (search, exact only) like --gpu, but the CPU threads
                          search units too
  --gpu-subgroups <n>     (with --gpu) number of subgroups that search in
                          parallel (default: 2048)

Results go to stdout in the same format as ../output/*.txt; timing and
search statistics go to stderr.";

struct Opts {
    engine: String,
    b0: u32,
    b1: u32,
    modes: Vec<u32>,
    threads: usize,
    par_depth: u32,
    unit_depth: u32,
    min_digits: u32,
    max_digits: u32,
    prune: search::Prune,
    journal: Option<String>,
    progress: bool,
    // read only in builds with the gpu feature
    #[cfg_attr(not(feature = "gpu"), allow(dead_code))]
    gpu: bool,
    #[cfg_attr(not(feature = "gpu"), allow(dead_code))]
    hybrid: bool,
    #[cfg_attr(not(feature = "gpu"), allow(dead_code))]
    gpu_subgroups: u32,
}

fn parse_args() -> Opts {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let die = |msg: &str| -> ! {
        eprintln!("{msg}\n\n{USAGE}");
        std::process::exit(2)
    };
    let mut pos = vec![];
    let mut modes = vec![0, 1];
    let mut threads = 0;
    let mut par_depth = 4;
    let mut unit_depth = 4;
    let mut min_digits = 1;
    let mut prune = search::Prune::NONE;
    let mut max_digits = u32::MAX;
    let mut journal = None;
    let mut progress = false;
    let mut gpu = false;
    let mut hybrid = false;
    let mut gpu_subgroups = 2048;
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let mut val = || {
            i += 1;
            args.get(i).cloned().unwrap_or_else(|| die(&format!("missing value for {a}")))
        };
        match a {
            "-h" | "--help" => die(""),
            "-m" | "--mode" => {
                modes = match val().as_str() {
                    "0" => vec![0],
                    "1" => vec![1],
                    "both" => vec![0, 1],
                    m => die(&format!("bad mode {m}")),
                }
            }
            "-j" | "--threads" => threads = val().parse().unwrap_or_else(|_| die("bad thread count")),
            "--par-depth" => par_depth = val().parse().unwrap_or_else(|_| die("bad depth")),
            "--unit-depth" => unit_depth = val().parse().unwrap_or_else(|_| die("bad depth")),
            "--journal" => journal = Some(val()),
            "--max-digits" => max_digits = val().parse().unwrap_or_else(|_| die("bad digit count")),
            "--min-digits" => min_digits = val().parse().unwrap_or_else(|_| die("bad digit count")),
            "--cap" => prune.cap = val().parse().unwrap_or_else(|_| die("bad cap")),
            "--band" => prune.z = val().parse().unwrap_or_else(|_| die("bad band")),
            "--deficit" => prune.deficit = val().parse().unwrap_or_else(|_| die("bad deficit")),
            "--epsilon" => prune.epsilon = val().parse().unwrap_or_else(|_| die("bad epsilon")),
            "--ratio" => prune.ratio = val().parse().unwrap_or_else(|_| die("bad ratio")),
            "--uniform" => prune.uniform = true,
            "--perturb" => prune.perturb = val().parse().unwrap_or_else(|_| die("bad seed")),
            "--keep-residues" => prune.keep_residues = true,
            "--offset" => prune.offset = val().parse().unwrap_or_else(|_| die("bad offset")),
            "--zero" => prune.zero = val().parse().unwrap_or_else(|_| die("bad weight for 0")),
            "--shift" => prune.shift = val().parse().ok().filter(|&t| t >= -1).unwrap_or_else(|| die("bad shift: use an integer t >= -1")),
            "--factorial" => prune.factorial = true,
            "--set-residue" => prune.set_residue = Some(val().parse().unwrap_or_else(|_| die("bad residue"))),
            "--zscore" => prune.zscore = val().parse().unwrap_or_else(|_| die("bad z-score")),
            "--progress" => progress = true,
            "--gpu" => gpu = true,
            "--hybrid" => {
                gpu = true;
                hybrid = true
            }
            "--gpu-subgroups" => gpu_subgroups = val().parse().unwrap_or_else(|_| die("bad subgroup count")),
            _ => pos.push(a.to_string()),
        }
        i += 1;
    }
    if pos.len() < 2 || pos.len() > 3 {
        die("expected an engine and one or two bases");
    }
    let b0: u32 = pos[1].parse().unwrap_or_else(|_| die("bad base"));
    let b1: u32 = pos.get(2).map(|s| s.parse().unwrap_or_else(|_| die("bad base"))).unwrap_or(b0);
    if b0 < 2 || b1 < b0 {
        die("bases must satisfy 2 <= first <= last");
    }
    if gpu && (journal.is_some() || prune.offset != 0 || prune.custom_weights()) {
        die("--gpu works only with the true weights, without --journal and --offset");
    }
    if prune.shift != 0 && prune.factorial {
        die("--shift and --factorial exclude each other");
    }
    if gpu && !cfg!(feature = "gpu") {
        die("--gpu needs a build with --features gpu");
    }
    if gpu_subgroups == 0 {
        die("--gpu-subgroups must be positive");
    }
    Opts { engine: pos[0].clone(), b0, b1, modes, threads, par_depth, unit_depth, min_digits, max_digits, prune, journal, progress, gpu, hybrid, gpu_subgroups }
}

// big-endian digits of every Munchausen number found, for 0^0 = 0 and 0^0 = 1
type Found = [Vec<Vec<u32>>; 2];

fn from_u128(v: Vec<u128>, b: u32) -> Vec<Vec<u32>> {
    v.into_iter()
        .map(|n| {
            let mut d = reference::digits_le(n, b);
            if d.is_empty() {
                d.push(0);
            }
            d.reverse();
            d
        })
        .collect()
}

fn run_search(b: u32, o: &Opts) -> Found {
    // the widest number searched has min(max_len, max_digits) digits, plus two
    // lanes for carries, and one more lane when t can be negative
    match search::max_len(b, &o.prune).min(o.max_digits) + (o.prune.zero < 0) as u32 {
        0..=30 => run_search_n::<1>(b, o),
        31..=62 => run_search_n::<2>(b, o),
        _ => {
            eprintln!("The search engine handles at most 62 digits. Add --max-digits 62 or less.");
            std::process::exit(2)
        }
    }
}

fn lanes_to_digits(d: u32, lanes: &[u8; 64]) -> Vec<u32> {
    (0..d as usize).rev().map(|i| lanes[i] as u32).collect()
}

fn run_search_n<const N: usize>(b: u32, o: &Opts) -> Found {
    // one-digit numbers: w(x) == x, which for x^x holds for x = 1, and for
    // x = 0 when 0^0 = 0
    let mut out: Found = [vec![], vec![]];
    if o.min_digits <= 1 && o.prune.offset == 0 {
        let (w, zw) = search::weights(b, &o.prune);
        for mode in 0..2 {
            out[mode].extend((0..b).filter(|&x| if x == 0 { zw[mode] == 0 } else { w[x as usize] == BigUint::from(x) }).map(|x| vec![x]));
        }
    }
    let t0 = Instant::now();
    let mut sr = search::Search::<N>::new(b, o.min_digits, o.max_digits, o.par_depth, o.prune);
    let t1 = Instant::now();
    let units = sr.units(o.unit_depth);
    if o.progress {
        eprintln!("  base {b}: {:.3} s for the tables, {:.3} s for {} units", (t1 - t0).as_secs_f64(), t1.elapsed().as_secs_f64(), units.len());
    }
    let total = units.len();

    let journal = o.journal.as_ref().map(|path| {
        let path = path.replace("{base}", &b.to_string());
        journal::Journal::open(&path, b, total, o.unit_depth)
    });
    let skip: Vec<bool> = match &journal {
        Some(j) => {
            for (mode, digits) in &j.found {
                out[*mode as usize].push(digits.clone());
            }
            (0..total).map(|i| j.done.contains(&i)).collect()
        }
        None => vec![false; total],
    };
    let already = skip.iter().filter(|&&x| x).count();
    if already > 0 {
        eprintln!("  resuming: {already} of {total} units already done");
    }
    let journal = journal.map(std::sync::Mutex::new);
    let journal = std::sync::Arc::new(journal);
    if journal.is_some() {
        let j = journal.clone();
        sr.on_found = Some(Box::new(move |mode, d, lanes| {
            if let Some(j) = &*j {
                j.lock().unwrap().found(mode, &lanes_to_digits(d, lanes));
            }
        }));
    }

    let start = Instant::now();
    let progress = std::sync::Mutex::new((Instant::now(), already));
    #[cfg(feature = "gpu")]
    if o.gpu {
        let go = search::gpu::GpuOptions { subgroups: o.gpu_subgroups, cpu: o.hybrid, verbose: o.progress };
        if let Err(e) = sr.run_gpu(b, &units, &go) {
            eprintln!("GPU search failed: {e}");
            std::process::exit(1);
        }
        return finish(b, &sr, out);
    }
    sr.run_units(
        &units,
        |i| skip[i],
        |i| {
            if let Some(j) = &*journal {
                j.lock().unwrap().done(i);
            }
            let mut p = progress.lock().unwrap();
            p.1 += 1;
            if o.progress && p.0.elapsed().as_secs_f64() >= 10.0 {
                p.0 = Instant::now();
                // unit sizes vary wildly, so this is not a reliable fraction of the work
                eprintln!("  base {b}: {}/{total} units done, {:.0}s elapsed", p.1, start.elapsed().as_secs_f64());
            }
        },
    );
    finish(b, &sr, out)
}

fn finish<const N: usize>(b: u32, sr: &search::Search<N>, mut out: Found) -> Found {
    eprintln!("  base {b}: {} nodes, {} interval evaluations", sr.nodes(), sr.evals());
    let skipped = sr.skipped();
    if skipped > 0.0 {
        eprintln!("  base {b}: expected number of solutions in skipped subtrees {skipped:.4}");
    }
    let found = std::mem::take(&mut *sr.found.lock().unwrap());
    for (mode, d, lanes) in found {
        out[mode as usize].push(lanes_to_digits(d, &lanes));
    }
    for v in out.iter_mut() {
        v.sort();
        v.dedup();
    }
    out
}

fn value(digits: &[u32], b: u32) -> BigUint {
    digits.iter().fold(BigUint::ZERO, |acc, &x| acc * b + x)
}

// independent check with arbitrary precision arithmetic: n = F(n) + offset,
// with the weights of the experiment (x^x by default)
fn verify(digits: &[u32], b: u32, mode: u32, prune: &search::Prune) -> bool {
    let (w, zw) = search::weights(b, prune);
    let sum: BigInt = digits
        .iter()
        .map(|&x| if x == 0 { BigInt::from(zw[mode as usize]) } else { BigInt::from(w[x as usize].clone()) })
        .sum();
    (digits.len() == 1 || digits[0] != 0) && sum + BigInt::from(prune.offset) == BigInt::from(value(digits, b))
}

fn tuple(v: &[u32]) -> String {
    let inner: Vec<String> = v.iter().map(|x| x.to_string()).collect();
    if v.len() == 1 { format!("({},)", inner[0]) } else { format!("({})", inner.join(",")) }
}

fn main() {
    let o = parse_args();
    if o.threads > 0 {
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
    }
    // port computes b^d in u128, which overflows from base 27; reference stays within u128 up to 27
    let max_base = match o.engine.as_str() {
        "port" => 26,
        "reference" | "brute" => 27,
        _ => search::MAX_BASE as u32,
    };
    if o.b1 > max_base {
        eprintln!("The {} engine supports bases up to {max_base}. Choose a smaller last base.", o.engine);
        std::process::exit(2);
    }
    for b in o.b0..=o.b1 {
        let t = Instant::now();
        let mut res: Found = match o.engine.as_str() {
            "search" => run_search(b, &o),
            "port" => [0, 1].map(|m| if o.modes.contains(&m) { from_u128(port::search(b, m).0, b) } else { vec![] }),
            "reference" => {
                [0, 1].map(|m| if o.modes.contains(&m) { from_u128(reference::dfs_search(b, m).0, b) } else { vec![] })
            }
            "brute" => [0, 1].map(|m| if o.modes.contains(&m) { from_u128(reference::brute(b, m), b) } else { vec![] }),
            e => {
                eprintln!("unknown engine {e}\n\n{USAGE}");
                std::process::exit(2)
            }
        };
        let secs = t.elapsed().as_secs_f64();
        for &mode in &o.modes {
            let res = &mut res[mode as usize];
            res.sort_by(|x, y| x.len().cmp(&y.len()).then(x.cmp(y)));
            for r in res.iter() {
                assert!(verify(r, b, mode, &o.prune), "base {b}: {} is not a Munchausen number", tuple(r));
            }
            let strs: Vec<String> = res.iter().map(|r| tuple(r)).collect();
            println!("{}:{}:{}: {}", b, mode, res.len(), strs.join(", "));
        }
        eprintln!("base {b} done in {secs:.3}s");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sorted(mut v: Vec<Vec<u32>>) -> Vec<Vec<u32>> {
        v.sort();
        v
    }

    fn test_opts() -> Opts {
        Opts {
            engine: "search".into(),
            b0: 2,
            b1: 2,
            modes: vec![0, 1],
            threads: 0,
            par_depth: 3,
            unit_depth: 2,
            min_digits: 1,
            max_digits: u32::MAX,
            prune: search::Prune::NONE,
            journal: None,
            progress: false,
            gpu: false,
            hybrid: false,
            gpu_subgroups: 2048,
        }
    }

    fn check_against_reference<const N: usize>(bases: std::ops::RangeInclusive<u32>) {
        for b in bases {
            let got = run_search_n::<N>(b, &test_opts());
            for mode in 0..2 {
                let want = from_u128(if b <= 9 { reference::brute(b, mode) } else { reference::dfs_search(b, mode).0 }, b);
                assert_eq!(sorted(got[mode as usize].clone()), sorted(want), "base {b} mode {mode} N={N}");
            }
        }
    }

    #[test]
    fn narrow_vectors_match_reference() {
        check_against_reference::<1>(2..=22);
    }

    #[test]
    fn wide_vectors_match_reference() {
        check_against_reference::<2>(2..=22);
    }

    // the GPU search, alone and with the CPU, must find the same numbers and
    // visit the same nodes
    #[cfg(feature = "gpu")]
    fn check_gpu<const N: usize>(bases: std::ops::RangeInclusive<u32>) {
        for b in bases {
            let run = |gpu: bool, cpu: bool| {
                let sr = search::Search::<N>::new(b, 1, u32::MAX, 3, search::Prune::NONE);
                let units = sr.units(2);
                if gpu {
                    let go = search::gpu::GpuOptions { subgroups: 64, cpu, verbose: false };
                    sr.run_gpu(b, &units, &go).unwrap();
                } else {
                    sr.run_units(&units, |_| false, |_| {});
                }
                let mut f = std::mem::take(&mut *sr.found.lock().unwrap());
                f.sort();
                f.dedup();
                (f, sr.nodes(), sr.evals())
            };
            let want = run(false, false);
            assert!(run(true, false) == want, "base {b} N={N}");
            assert!(run(true, true) == want, "base {b} N={N} with the CPU");
        }
    }

    #[cfg(feature = "gpu")]
    #[test]
    fn gpu_matches_cpu() {
        check_gpu::<1>(2..=26);
        check_gpu::<2>(2..=24);
    }

    // every solution for the weights of `prune`, by trying every digit multiset
    fn brute_multisets(b: u32, prune: &search::Prune) -> Found {
        let (w, zw) = search::weights(b, prune);
        let mut out: Found = [vec![], vec![]];
        fn rec(b: u32, x: u32, left: u32, cnt: &mut Vec<u32>, w: &[BigUint], zw: [i64; 2], offset: u64, out: &mut Found) {
            if x == 0 {
                cnt[0] = left;
                for mode in 0..2 {
                    let mut s = BigInt::from(offset) + BigInt::from(zw[mode]) * cnt[0];
                    for y in 1..b as usize {
                        s += BigInt::from(w[y].clone()) * cnt[y];
                    }
                    let Some(s) = s.to_biguint() else { continue };
                    let digits: Vec<u32> = s.to_radix_be(b).into_iter().map(u32::from).collect();
                    let mut h = vec![0u32; b as usize];
                    digits.iter().for_each(|&v| h[v as usize] += 1);
                    if h == *cnt {
                        out[mode].push(digits);
                    }
                }
                return;
            }
            for c in 0..=left {
                cnt[x as usize] = c;
                rec(b, x - 1, left - c, cnt, w, zw, offset, out);
            }
            cnt[x as usize] = 0;
        }
        for d in 1..=search::max_len(b, prune) {
            rec(b, b - 1, d, &mut vec![0; b as usize], &w, zw, prune.offset, &mut out);
        }
        out
    }

    fn weight_options() -> Vec<search::Prune> {
        let n = search::Prune::NONE;
        let mut v = vec![n];
        v.extend([-3, -2, -1, 0, 2, 3, 7].map(|m| search::Prune { zero: m, ..n }));
        v.extend([-1, 1, 2, 3].map(|t| search::Prune { shift: t, ..n }));
        v.push(search::Prune { factorial: true, ..n });
        v.push(search::Prune { factorial: true, zero: 2, ..n });
        v.push(search::Prune { shift: 1, zero: -1, offset: 5, ..n });
        v.push(search::Prune { perturb: 3, keep_residues: true, ..n });
        for r in 0..3 {
            v.push(search::Prune { set_residue: Some(r), ..n });
            for seed in 1..3 {
                v.push(search::Prune { perturb: seed, set_residue: Some(r), ..n });
            }
        }
        v
    }

    #[test]
    fn weight_tables_are_right() {
        for b in 2..=12u32 {
            let n = search::Prune::NONE;
            let big = |x: u32| BigUint::from(x);
            for t in -1..=3 {
                let (w, zw) = search::weights(b, &search::Prune { shift: t, ..n });
                assert_eq!(zw, [0, 1]);
                for x in 1..b {
                    assert_eq!(w[x as usize], big(x).pow((x as i32 + t) as u32), "base {b} shift {t}");
                }
            }
            let (w, _) = search::weights(b, &search::Prune { factorial: true, ..n });
            for x in 1..b {
                assert_eq!(w[x as usize], (1..=x).map(big).product::<BigUint>(), "base {b} factorial");
            }
            for r in 0..4 {
                for seed in 0..3 {
                    let (w, _) = search::weights(b, &search::Prune { perturb: seed, set_residue: Some(r), ..n });
                    for x in 1..b {
                        let (w, x0) = (&w[x as usize], big(x).pow(x));
                        assert_eq!(w % (b - 1), big((x + r) % (b - 1)), "base {b} residue {r} seed {seed}");
                        // the perturbation adds below x^x / 4 + 1, the residue below b - 1
                        assert!(*w >= x0 && *w < &x0 + &x0 / 4u32 + b, "base {b} residue {r} seed {seed}");
                    }
                }
            }
        }
    }

    #[test]
    fn weight_options_match_brute_force() {
        for prune in weight_options() {
            for b in 2..=8 {
                let o = Opts { prune, ..test_opts() };
                let want = brute_multisets(b, &prune).map(sorted);
                let got = run_search_n::<1>(b, &o).map(sorted);
                let what = format!("base {b}: zero {} shift {} factorial {} perturb {} residue {:?} offset {}", prune.zero, prune.shift, prune.factorial, prune.perturb, prune.set_residue, prune.offset);
                assert_eq!(got, want, "{what}");
                assert_eq!(run_search_n::<2>(b, &o).map(sorted), want, "{what}, N=2");
                for mode in 0..2 {
                    for r in &want[mode] {
                        assert!(verify(r, b, mode as u32, &prune), "{what}");
                    }
                }
            }
        }
    }

    #[test]
    fn port_matches_reference() {
        for b in 2..=13 {
            for mode in 0..2 {
                let mut want = reference::dfs_search(b, mode).0;
                // the python code never finds 10 (base 2) since testbd0 rejects it
                if b == 2 {
                    want.retain(|&n| n != 2);
                }
                assert_eq!(port::search(b, mode).0, want, "base {b} mode {mode}");
            }
        }
    }
}
