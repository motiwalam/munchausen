// Combine the outputs of `search --shard i/n` runs. A shard prints the line
// "# shard i/n base b" before its result lines for base b, with " by size"
// at the end under --shard-by size. A result line without such a line
// before it counts as a full run, shard 0/1.
use std::collections::{BTreeMap, BTreeSet};

pub fn shard_line(b: u32, (i, n): (u32, u32), by_size: bool) -> String {
    format!("# shard {i}/{n} base {b}{}", if by_size { " by size" } else { "" })
}

fn parse_shard(line: &str) -> Option<(u32, u32, u32, bool)> {
    let rest = line.strip_prefix("# shard ")?;
    let (s, b) = rest.split_once(" base ")?;
    let (b, by_size) = match b.trim().strip_suffix(" by size") {
        Some(b) => (b, true),
        None => (b.trim(), false),
    };
    let (i, n) = s.split_once('/')?;
    Some((b.parse().ok()?, i.parse().ok()?, n.parse().ok()?, by_size))
}

// "b:m:count: (x,y), (z,)" -> (b, m, numbers)
fn parse_result(line: &str) -> Option<(u32, u32, Vec<Vec<u32>>)> {
    let mut f = line.splitn(4, ':');
    let b = f.next()?.parse().ok()?;
    let m = f.next()?.parse().ok()?;
    let count: usize = f.next()?.parse().ok()?;
    let list = f.next()?;
    let mut out = vec![];
    for t in list.split('(').skip(1) {
        let inner = t.split(')').next()?;
        let v: Option<Vec<u32>> = inner.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().ok()).collect();
        out.push(v?);
    }
    (out.len() == count).then_some((b, m, out))
}

struct Part {
    shards: u32,
    by_size: bool,
    seen: BTreeSet<u32>,
    found: Vec<Vec<u32>>,
}

/// Print the merged result lines of the given files. Returns false, after a
/// message on stderr, if a file is unreadable or a shard is missing.
pub fn run(files: &[String]) -> bool {
    let mut parts: BTreeMap<(u32, u32), Part> = BTreeMap::new();
    for path in files {
        let text = match std::fs::read_to_string(path) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("Cannot read {path}: {e}.");
                return false;
            }
        };
        let mut cur = None;
        for (no, line) in text.lines().enumerate() {
            if line.starts_with('#') {
                cur = parse_shard(line);
                continue;
            }
            if line.trim().is_empty() {
                continue;
            }
            let Some((b, m, found)) = parse_result(line) else {
                eprintln!("{path}:{}: this is not a result line. Pass only the stdout of search runs.", no + 1);
                return false;
            };
            let (i, n, by_size) = match cur {
                Some((cb, i, n, s)) if cb == b => (i, n, s && n > 1),
                _ => (0, 1, false),
            };
            let p = parts.entry((b, m)).or_insert(Part { shards: n, by_size, seen: BTreeSet::new(), found: vec![] });
            if p.shards != n {
                eprintln!("{path}:{}: base {b} was split into {} shards elsewhere and into {n} here.", no + 1, p.shards);
                return false;
            }
            if p.by_size != by_size {
                let rule = |s: bool| if s { "by size" } else { "by index" };
                eprintln!("{path}:{}: base {b} was split {} elsewhere and {} here. Rerun the shards with one --shard-by rule.", no + 1, rule(p.by_size), rule(by_size));
                return false;
            }
            p.seen.insert(i);
            p.found.extend(found);
        }
    }
    let mut ok = true;
    for ((b, m), p) in &parts {
        let missing: Vec<String> = (0..p.shards).filter(|i| !p.seen.contains(i)).map(|i| format!("{i}/{}", p.shards)).collect();
        if !missing.is_empty() {
            eprintln!("Base {b}, 0^0 = {m}: shards {} are missing. Add their output files.", missing.join(", "));
            ok = false;
        }
    }
    if !ok {
        return false;
    }
    for ((b, m), mut p) in parts {
        p.found.sort_by(|x, y| x.len().cmp(&y.len()).then(x.cmp(y)));
        p.found.dedup();
        let strs: Vec<String> = p.found.iter().map(|r| crate::tuple(r)).collect();
        println!("{}:{}:{}: {}", b, m, p.found.len(), strs.join(", "));
    }
    true
}
