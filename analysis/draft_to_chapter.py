"""Turn a draft in docs/library/drafts/ into a numbered library chapter.

Renumbers the draft's own headings as N.1, N.2, ... (sub-headings N.i.j) and
its own lemmas, theorems and so on as N.1, N.2, ... in order of definition.
References to library results (chapters below N) are left alone. Lines whose
"section a.b" references point inside the draft are listed with --internal.

usage: draft_to_chapter.py draft.md N "Title" out.md [--internal line,line,...]
"""
import re
import sys

KINDS = r"(Lemma|Theorem|Proposition|Corollary|Assumption|Remark|Conjecture|Heuristic|Definition)"


def convert(text, N, title, internal_lines, single=False):
    lines = text.split('\n')
    # headings
    hmap, top, sub = {}, 0, 0
    out = []
    for i, l in enumerate(lines):
        m2 = re.match(r'^## (\d+)\.?(\s.*)$', l)
        m3 = re.match(r'^### (\d+)\.(\d+)(\s.*)$', l)
        if i == 0 and l.startswith('# '):
            out.append(f'# {N}. {title}')
            continue
        if m2:
            top += 1
            sub = 0
            hmap[m2.group(1)] = f'{N}.{top}'
            l = f'## {N}.{top}{m2.group(2)}'
        elif m3:
            sub += 1
            hmap[f'{m3.group(1)}.{m3.group(2)}'] = f'{N}.{top}.{sub}'
            l = f'### {N}.{top}.{sub}{m3.group(3)}'
        elif l.startswith('## ') and not re.match(r'^## \d', l):
            pass
        out.append(l)
    lines = out
    # definitions of results, in order. A definition is numbered inside the
    # draft (its first part is a draft section) and is followed by a status
    # in parentheses or a period; library results and forward references can
    # also start a line.
    ids, k = {}, 0
    for l in lines:
        m = re.match(r'^(\*\*)?' + KINDS + r' (\d+\.\d+)(\*\*)?(\s*\(|\.(\*\*)?(\s|$))', l)
        if m and m.group(3) not in ids and m.group(3).split('.')[0] in hmap:
            k += 1
            ids[m.group(3)] = f'{N}.{k}'
    def rep_id(m):
        return f'{m.group(1)} {ids.get(m.group(2), m.group(2))}' if m.group(2) in ids else m.group(0)
    if single:
        # results numbered 1, 2, ... per kind: prefix the chapter
        lines = [re.sub(KINDS + r' (\d+)(?![\d.])', lambda m: f'{m.group(1)} {N}.{m.group(2)}', l) for l in lines]
    res = []
    for i, l in enumerate(lines):
        if single:
            l = l
        else:
            l = re.sub(KINDS + r' (\d+\.\d+)(?!\d)', lambda m: f'{m.group(1)} \x00{m.group(2)}\x00', l)
        l = re.sub(r'(\w+) \x00(\d+\.\d+)\x00', lambda m: f'{m.group(1)} {ids.get(m.group(2), m.group(2))}', l)
        if i + 1 in internal_lines:
            l = re.sub(r'(sections?|Section) (\d+(?:\.\d+)?)', lambda m: f'{m.group(1)} {hmap.get(m.group(2), m.group(2))}', l)
        res.append(l)
    return '\n'.join(res), hmap, ids


if __name__ == '__main__':
    src, N, title, dst = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
    internal = set()
    if '--internal' in sys.argv:
        internal = {int(x) for x in sys.argv[sys.argv.index('--internal') + 1].split(',') if x}
    text, hmap, ids = convert(open(src).read(), N, title, internal, '--single' in sys.argv)
    open(dst, 'w').write(text)
    print('headings', hmap)
    print('results', ids)
