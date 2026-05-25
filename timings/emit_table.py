#!/usr/bin/env python3
"""Emit table8.tex, magma_version.tex, and table8.sha256 from a timings TSV.

The TSV is produced by run_all.sh and has columns:
  label, D, alg, walltime_seconds, peak_memory_mb, status

The selected_polynomials.txt has columns:
  label, coefficient_list, g, q, |Pic|, |ICM|

Output (under the same directory as the input TSV by default):
  table8.tex       — \\begin{sidewaystable}...\\end{sidewaystable}
  magma_version.tex — \\newcommand{\\magmaVersion}{X.YY-Z}
  table8.sha256    — sha256 of table8.tex, for cross-repo sync verification
"""
import argparse
import hashlib
import os
import re
import sys
import unittest

D_VALUES = (4, 9, 12, 36, 100)
ALG_ORDER = ('IsogenyGraphBuilder', 'IsogenyOrbitBuilder', 'Polarization')
ALG_HEADER = {
    'IsogenyGraphBuilder': r'\texttt{IsogenyGraphBuilder}',
    'IsogenyOrbitBuilder': r'\texttt{IsogenyOrbitBuilder}',
    'Polarization': r'Polarizations',
}
NOISE_FLOOR = 0.1


def fmt_cell(walltime, status):
    """Render one timing cell as LaTeX."""
    if status in ('timeout', 'oom'):
        return r'\(-\)'
    if status == 'error':
        return r'?'
    try:
        t = float(walltime)
    except (TypeError, ValueError):
        return r'?'
    if t < NOISE_FLOOR:
        return r'\(<0.1\)'
    if t < 100:
        return f'{t:.1f}'
    return f'{int(round(t))}'


def parse_header(tsv_lines):
    out = {}
    for line in tsv_lines:
        if not line.startswith('#'):
            break
        m = re.match(r'^#\s*([A-Za-z_]+)=(.+)$', line.rstrip('\n'))
        if m:
            out[m.group(1)] = m.group(2)
    return out


def read_timings(path):
    with open(path) as f:
        lines = f.readlines()
    header = parse_header(lines)
    data = {}
    column_header_seen = False
    for line in lines:
        if line.startswith('#'):
            continue
        line = line.rstrip('\n')
        if not column_header_seen:
            column_header_seen = True
            continue
        parts = line.split('\t')
        if len(parts) != 6:
            continue
        label, D, alg, walltime, mem, status = parts
        data[(label, int(D), alg)] = (walltime, mem, status)
    return header, data


def read_selected(path):
    rows = []
    with open(path) as f:
        for line in f:
            line = line.rstrip('\n')
            if not line or line.startswith('#'):
                continue
            parts = line.split('\t')
            if len(parts) != 6:
                raise ValueError(f"bad selected line: {line!r}")
            rows.append({
                'label': parts[0],
                'coeffs': parts[1],
                'g': int(parts[2]),
                'q': int(parts[3]),
                'pic': int(parts[4]),
                'icm': int(parts[5]),
            })
    return rows


def short_label(row):
    """Compact, paper-friendly label for the table row."""
    if row['coeffs'] == '[ 81, 54, -9, -15, -8, -5, -1, 2, 1 ]':
        return r'\avlink{4.3.c\_ab\_af\_ai} / \(\F_3\)'
    if row['coeffs'] == '[ 6561, -4374, 405, 297, -122, 33, 5, -6, 1 ]':
        return r'\avlink{4.3.c\_ab\_af\_ai} / \(\F_9\)'
    return r'$' + f'g{row["g"]}, q{row["q"]}, |\\Pic|{{=}}{row["pic"]}' + r'$'


def emit_table(selected, timings):
    lines = []
    lines.append(r'\begin{sidewaystable}')
    lines.append(r'\centering')
    lines.append(r'\small')
    n_dcols = len(D_VALUES)
    col_spec = 'l c c c' + ('|' + 'r' * n_dcols) * len(ALG_ORDER)
    lines.append(r'\begin{tabular}{' + col_spec + r'}')
    lines.append(r'\toprule')
    top = ['', '', '', '']
    for alg in ALG_ORDER:
        top.append(r'\multicolumn{' + str(n_dcols) + r'}{c}{' + ALG_HEADER[alg] + r'}')
    lines.append(' & '.join(top) + r' \\')
    cmid = []
    start = 5
    for _ in ALG_ORDER:
        cmid.append(r'\cmidrule(lr){' + f'{start}-{start + n_dcols - 1}' + r'}')
        start += n_dcols
    lines.append(' '.join(cmid))
    sub = ['isogeny class', r'$g$', r'$q$', r'$|\Pic(R)|$']
    for _ in ALG_ORDER:
        for d in D_VALUES:
            sub.append(f'$D{{=}}{d}$')
    lines.append(' & '.join(sub) + r' \\')
    lines.append(r'\midrule')
    for row in selected:
        cells = [
            short_label(row),
            str(row['g']),
            str(row['q']),
            str(row['pic']),
        ]
        for alg in ALG_ORDER:
            for d in D_VALUES:
                key = (row['label'], d, alg)
                wt, _mem, status = timings.get(key, ('', '-', 'error'))
                cells.append(fmt_cell(wt, status))
        lines.append(' & '.join(cells) + r' \\')
    lines.append(r'\bottomrule')
    lines.append(r'\end{tabular}')
    lines.append(
        r'\caption{Wall-clock seconds per cell on a single P-core of an Intel '
        r'i9-13900KS (188\,GB RAM), Magma \magmaVersion. Each cell is a single '
        r'cold run; \(-\) = timeout or OOM; \(?\) = Magma-level error; \(<0.1\) '
        r'is below the single-run noise floor. The \emph{Polarizations} column '
        r'group times \texttt{NonPrincipalPolarizationsOfDegreeDividing}, which '
        r'internally calls \texttt{IsogenyGraphBuilder}; the reported cost '
        r'therefore includes that cold graph build. See \texttt{public/timings/} '
        r'in the accompanying repository for the full data and methodology.}'
    )
    lines.append(r'\label{tab:section8-timings}')
    lines.append(r'\end{sidewaystable}')
    return '\n'.join(lines) + '\n'


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('-t', '--timings', help='timings.tsv')
    parser.add_argument('-s', '--selected', help='selected_polynomials.txt')
    parser.add_argument('-o', '--out-dir', help='directory to write table8.tex etc.')
    args = parser.parse_args(argv)

    if args.self_test:
        unittest.main(argv=[sys.argv[0]] + ['-v'], exit=False, module=__name__)
        return

    if not (args.timings and args.selected and args.out_dir):
        parser.error("--timings, --selected, --out-dir required unless --self-test")

    header, timings = read_timings(args.timings)
    selected = read_selected(args.selected)
    table = emit_table(selected, timings)

    os.makedirs(args.out_dir, exist_ok=True)
    out_table = os.path.join(args.out_dir, 'table8.tex')
    out_ver = os.path.join(args.out_dir, 'magma_version.tex')
    out_sha = os.path.join(args.out_dir, 'table8.sha256')

    with open(out_table, 'w') as f:
        f.write(table)

    magma_version = header.get('magma_version', 'unknown')
    with open(out_ver, 'w') as f:
        f.write(r'\newcommand{\magmaVersion}{' + magma_version + r'}' + '\n')

    digest = hashlib.sha256(table.encode('utf-8')).hexdigest()
    with open(out_sha, 'w') as f:
        f.write(f'{digest}  table8.tex\n')

    print(f'Wrote {out_table}, {out_ver}, {out_sha} (magma_version={magma_version})')


class TestFmtCell(unittest.TestCase):
    def test_ok_under_noise(self):
        self.assertEqual(fmt_cell('0.05', 'ok'), r'\(<0.1\)')

    def test_ok_one_decimal(self):
        self.assertEqual(fmt_cell('0.5', 'ok'), '0.5')
        self.assertEqual(fmt_cell('12.34', 'ok'), '12.3')
        self.assertEqual(fmt_cell('99.95', 'ok'), '100.0')

    def test_ok_integer_above_100(self):
        self.assertEqual(fmt_cell('100', 'ok'), '100')
        self.assertEqual(fmt_cell('125.7', 'ok'), '126')

    def test_timeout(self):
        self.assertEqual(fmt_cell('3600', 'timeout'), r'\(-\)')

    def test_oom(self):
        self.assertEqual(fmt_cell('3600', 'oom'), r'\(-\)')

    def test_error(self):
        self.assertEqual(fmt_cell('anything', 'error'), r'?')

    def test_unparseable_walltime(self):
        self.assertEqual(fmt_cell('bogus', 'ok'), r'?')


class TestReadFixtures(unittest.TestCase):
    def setUp(self):
        here = os.path.dirname(os.path.abspath(__file__))
        self.sel_path = os.path.join(here, 'tests', 'fixtures', 'tiny_selected.txt')
        self.tsv_path = os.path.join(here, 'tests', 'fixtures', 'tiny_timings.tsv')

    def test_selected_round_trip(self):
        rows = read_selected(self.sel_path)
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[0]['g'], 4)
        self.assertEqual(rows[0]['q'], 3)
        self.assertEqual(rows[1]['pic'], 3)

    def test_timings_round_trip(self):
        header, data = read_timings(self.tsv_path)
        self.assertEqual(header.get('magma_version'), '2.29-7')
        self.assertEqual(len(data), 30)
        key = ('4.3.[81,54,-9,-15,-8,-5,-1,2,1]', 12, 'IsogenyGraphBuilder')
        self.assertEqual(data[key][2], 'timeout')


class TestEmitTable(unittest.TestCase):
    def setUp(self):
        here = os.path.dirname(os.path.abspath(__file__))
        self.sel_path = os.path.join(here, 'tests', 'fixtures', 'tiny_selected.txt')
        self.tsv_path = os.path.join(here, 'tests', 'fixtures', 'tiny_timings.tsv')

    def test_emits_sidewaystable(self):
        selected = read_selected(self.sel_path)
        _, timings = read_timings(self.tsv_path)
        out = emit_table(selected, timings)
        self.assertIn(r'\begin{sidewaystable}', out)
        self.assertIn(r'\end{sidewaystable}', out)
        self.assertIn(r'\caption{', out)
        self.assertIn(r'\magmaVersion', out)

    def test_renders_all_status_values(self):
        selected = read_selected(self.sel_path)
        _, timings = read_timings(self.tsv_path)
        out = emit_table(selected, timings)
        self.assertIn(r'\(-\)', out)
        self.assertIn(r'?', out)
        self.assertIn(r'\(<0.1\)', out)

    def test_row_count(self):
        selected = read_selected(self.sel_path)
        _, timings = read_timings(self.tsv_path)
        out = emit_table(selected, timings)
        data_lines = [l for l in out.splitlines()
                     if l.strip().endswith(r'\\') and 'sidewaystable' not in l]
        self.assertEqual(len(data_lines), 4)


if __name__ == '__main__':
    main(sys.argv[1:])
