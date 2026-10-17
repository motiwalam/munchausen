mod digits;
mod port;
mod reference;
mod search;

use num_bigint::BigUint;
use std::time::Instant;

const USAGE: &str = "\
usage: fast <engine> <base> [<last base>] [options]

engines:
  search      fast prefix-pruned digit-count search (bases 2..=62)
  port        faithful port of the python algorithm (bases 2..=27)
  reference   simple u128 version of the search, for validation (bases 2..=27)
  brute       check every n up to the upper bound (tiny bases only)

options:
  -m, --mode <0|1|both>   value of 0^0 (default: both)
  -j, --threads <n>       worker threads (default: all cores)
  --par-depth <n>         tree depth down to which work is split into tasks (default: 6)

Results go to stdout in the same format as ../output/*.txt; timing and
search statistics go to stderr.";

struct Opts {
    engine: String,
    b0: u32,
    b1: u32,
    modes: Vec<u32>,
    threads: usize,
    par_depth: u32,
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
    let mut par_depth = 6;
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
    Opts { engine: pos[0].clone(), b0, b1, modes, threads, par_depth }
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

fn run_search(b: u32, par_depth: u32) -> Found {
    match b {
        2..=30 => run_search_n::<1>(b, par_depth),
        31..=62 => run_search_n::<2>(b, par_depth),
        _ => {
            eprintln!("the search engine supports bases 2..=62");
            std::process::exit(2)
        }
    }
}

fn run_search_n<const N: usize>(b: u32, par_depth: u32) -> Found {
    // one-digit numbers: x^x == x only for x = 1, and x = 0 when 0^0 = 0
    let mut out: Found = [vec![vec![0], vec![1]], vec![vec![1]]];
    let sr = search::Search::<N>::new(b, par_depth);
    sr.run();
    eprintln!("  base {b}: {} nodes, {} interval evaluations", sr.nodes.into_inner(), sr.evals.into_inner());
    for (mode, d, lanes) in sr.found.into_inner().unwrap() {
        out[mode as usize].push((0..d as usize).rev().map(|i| lanes[i] as u32).collect());
    }
    out
}

fn value(digits: &[u32], b: u32) -> BigUint {
    digits.iter().fold(BigUint::ZERO, |acc, &x| acc * b + x)
}

// independent check with arbitrary precision arithmetic
fn verify(digits: &[u32], b: u32, mode: u32) -> bool {
    let sum: BigUint = digits
        .iter()
        .map(|&x| if x == 0 { BigUint::from(mode) } else { BigUint::from(x).pow(x) })
        .sum();
    (digits.len() == 1 || digits[0] != 0) && sum == value(digits, b)
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
    for b in o.b0..=o.b1 {
        let t = Instant::now();
        let mut res: Found = match o.engine.as_str() {
            "search" => run_search(b, o.par_depth),
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
                assert!(verify(r, b, mode), "base {b}: {} is not a Munchausen number", tuple(r));
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

    fn check_against_reference<const N: usize>(bases: std::ops::RangeInclusive<u32>) {
        for b in bases {
            let got = run_search_n::<N>(b, 3);
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
