// Append-only record of a long search so that it can be interrupted and
// resumed. Format (one record per line):
//
//   # munchausen journal v1 base=<b> units=<n> unit_depth=<k>
//   done <unit index>
//   found <0^0 convention> <digits, most significant first, comma separated>
//
// Solutions are written the moment they are found; a unit is only marked
// done once its whole subtree has been searched.
use std::collections::HashSet;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};

pub struct Journal {
    file: File,
    pub done: HashSet<usize>,
    pub found: Vec<(u32, Vec<u32>)>,
}

fn header(b: u32, units: usize, unit_depth: u32) -> String {
    format!("# munchausen journal v1 base={b} units={units} unit_depth={unit_depth}")
}

impl Journal {
    pub fn open(path: &str, b: u32, units: usize, unit_depth: u32) -> Journal {
        let die = |msg: String| -> ! {
            eprintln!("journal {path}: {msg}");
            std::process::exit(1)
        };
        let want = header(b, units, unit_depth);
        let mut done = HashSet::new();
        let mut found = vec![];
        let exists = std::path::Path::new(path).exists();
        if exists {
            let f = File::open(path).unwrap_or_else(|e| die(e.to_string()));
            let mut lines = BufReader::new(f).lines();
            match lines.next() {
                Some(Ok(h)) if h == want => {}
                Some(Ok(h)) => die(format!("written by a different search ({h:?}, expected {want:?})")),
                _ => die("missing header".into()),
            }
            for line in lines {
                let line = line.unwrap_or_else(|e| die(e.to_string()));
                let parts: Vec<&str> = line.split_whitespace().collect();
                match parts.as_slice() {
                    ["done", i] => {
                        done.insert(i.parse().unwrap_or_else(|_| die(format!("bad line {line:?}"))));
                    }
                    ["found", m, digits] => {
                        let m = m.parse().unwrap_or_else(|_| die(format!("bad line {line:?}")));
                        let v = digits.split(',').map(|x| x.parse().unwrap_or_else(|_| die(format!("bad line {line:?}"))));
                        found.push((m, v.collect()));
                    }
                    // a torn final line from an interrupted write is harmless
                    _ => {}
                }
            }
        }
        let mut file = OpenOptions::new().create(true).append(true).open(path).unwrap_or_else(|e| die(e.to_string()));
        if !exists {
            writeln!(file, "{want}").unwrap_or_else(|e| die(e.to_string()));
        }
        Journal { file, done, found }
    }

    fn write(&mut self, line: String) {
        // one write per record keeps lines intact; flush so a crash loses nothing
        self.file.write_all(line.as_bytes()).and_then(|_| self.file.flush()).expect("cannot write journal");
    }

    pub fn done(&mut self, unit: usize) {
        self.write(format!("done {unit}\n"));
    }

    pub fn found(&mut self, mode: u32, digits: &[u32]) {
        let s: Vec<String> = digits.iter().map(|x| x.to_string()).collect();
        self.write(format!("found {mode} {}\n", s.join(",")));
    }
}
