"""Round 6, search 2: dynamic instruction counts by kind (question 125).

From a callgrind --dump-instr=yes profile and objdump of the same binary.
Run valgrind on a build without GFNI (RUSTFLAGS="-C target-cpu=native -C
target-feature=-gfni"), which valgrind 3.25 does not decode.

Usage: r6s2_bykind.py <binary> <callgrind.out> [<binary2> <callgrind2.out>]"""
import collections
import re
import subprocess
import sys


def disasm(binary):
    out = subprocess.run(['objdump', '-d', '--no-show-raw-insn', binary], capture_output=True, text=True).stdout
    ins = {}
    for line in out.splitlines():
        m = re.match(r'^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$', line)
        if m:
            ins[int(m.group(1), 16)] = (m.group(2), m.group(3))
    return ins


def costs(path):
    c = collections.Counter()
    addr = 0
    in_calls = False
    for line in open(path):
        line = line.rstrip('\n')
        if not line or line[0].isalpha() and '=' in line:
            in_calls = line.startswith('calls=')
            continue
        parts = line.split()
        if not parts:
            continue
        a = parts[0]
        if a.startswith('0x'):
            addr = int(a, 16)
        elif a.startswith('+'):
            addr += int(a[1:])
        elif a.startswith('-'):
            addr -= int(a[1:])
        elif a == '*':
            pass
        else:
            continue
        if in_calls:
            # the line after calls= is the call cost (inclusive): skip it
            in_calls = False
            continue
        if len(parts) >= 3:
            c[addr] += int(parts[2])
    return c


def kind(mn, ops):
    stack = 'rsp' in ops
    if mn.startswith('v'):
        k = 'vector'
        if stack:
            k += ' (stack)'
        return k
    if mn.startswith('j'):
        return 'branch'
    if mn.startswith('cmov') or mn.startswith('set'):
        return 'cmov/set'
    if mn.startswith('mov'):
        if stack:
            return 'mov (stack)'
        if '(' in ops:
            return 'mov (memory)'
        return 'mov (register)'
    if '(' in ops:
        return 'alu (memory)'
    return 'alu'


def summary(binary, path):
    ins = disasm(binary)
    c = costs(path)
    out = collections.Counter()
    miss = 0
    for a, n in c.items():
        if a in ins:
            out[kind(*ins[a])] += n
        else:
            miss += n
    out['(unknown address)'] = miss
    return out


a = summary(sys.argv[1], sys.argv[2])
b = summary(sys.argv[3], sys.argv[4]) if len(sys.argv) > 4 else None
for k in sorted(set(a) | set(b or {})):
    if b is None:
        print(f'{k:20s} {a[k]:>14,}')
    else:
        print(f'{k:20s} {a[k]:>14,} {b[k]:>14,} {b[k] - a[k]:>+14,}')
print(f'{"total":20s} {sum(a.values()):>14,}' + (f' {sum(b.values()):>14,} {sum(b.values()) - sum(a.values()):>+14,}' if b else ''))
