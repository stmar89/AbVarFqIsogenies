#!/usr/bin/env python3
r"""Emit the portrait Section 8 timings artifacts from a timings TSV.

Outputs (under --out-dir):
  tables_section8.tex      single \begin{table} float with three stacked
                           tabulars (Graph, Orbit, Polarization filter
                           overhead) sharing one caption.
  magma_version.tex        \newcommand{\magmaVersion}{X.YY-Z}
  tables_section8.sha256   sha256 of tables_section8.tex for cross-repo
                           sync verification.

Inputs:
  --timings   timings.tsv produced by run_all.sh; columns:
              label, D, alg, walltime_seconds, peak_memory_mb, status.
  --selected  selected_polynomials.txt; columns:
              label, coefficient_list, g, q, |Pic|, |ICM|.
"""
import argparse
import hashlib
import os
import re
import sys
import unittest

D_VALUES = (4, 9, 12, 36, 100)
NOISE_FLOOR = 0.1

# Map row-label (first column of selected_polynomials.txt) to
# (LMFDB label, is_base_change_marker). The F9 anchor is the base
# change of the F3 anchor; LMFDB stores its canonical label in the
# twists list of 4.3.c_ab_af_ai but has no page for it, so we render
# it as plain sans-serif text (not a hyperlink) with an asterisk
# pointing at the caption note.
LABELS = {
    '4.3.[ 81, 54, -9, -15, -8, -5, -1, 2, 1 ]':
        ('4.3.c_ab_af_ai', False),
    '4.9.[ 6561, -4374, 405, 297, -122, 33, 5, -6, 1 ]':
        ('4.9.ag_f_bh_aes', True),
    '1.101.[ 101, 13, 1 ]':
        ('1.101.n', False),
    '3.5.[ 125, 0, -5, 11, -1, 0, 1 ]':
        ('3.5.a_ab_l', False),
    '2.101.[ 10201, -2323, 326, -23, 1 ]':
        ('2.101.ax_mo', False),
    '2.101.[ 10201, -1010, 36, -10, 1 ]':
        ('2.101.ak_bk', False),
    '2.101.[ 10201, 1010, 102, 10, 1 ]':
        ('2.101.k_dy', False),
    '3.16.[ 4096, -512, 32, -27, 2, -2, 1 ]':
        ('3.16.ac_c_abb', False),
}

BC_MARK = r'\(^*\)'
F3_ANCHOR_TEX = r'\avlink{4.3.c\_ab\_af\_ai}'


def fmt_cell(walltime, status):
    """Render one timing cell as LaTeX (single seconds value)."""
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


def fmt_delta_cell(pol_w, pol_s, graph_w, graph_s):
    """Polarization wall time minus graph wall time, with status fallback.

    Both legs must be ok for the subtraction to be meaningful; otherwise
    we fall back to the worse status (timeout/oom > error > ok).
    """
    if pol_s in ('timeout', 'oom') or graph_s in ('timeout', 'oom'):
        return r'\(-\)'
    if pol_s == 'error' or graph_s == 'error':
        return r'?'
    try:
        d = float(pol_w) - float(graph_w)
    except (TypeError, ValueError):
        return r'?'
    if d < 0:
        d = 0.0
    if d < NOISE_FLOOR:
        return r'\(<0.1\)'
    if d < 100:
        return f'{d:.1f}'
    return f'{int(round(d))}'


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


def render_label_cell(row):
    """LMFDB label for the row, marking the F9 base change with an asterisk."""
    try:
        lmfdb, is_bc = LABELS[row['label']]
    except KeyError as e:
        raise KeyError(
            f"no LMFDB label override for row {row['label']!r}; "
            "add it to LABELS in emit_table.py"
        ) from e
    escaped = lmfdb.replace('_', r'\_')
    if is_bc:
        return r'\textsf{' + escaped + r'}' + BC_MARK
    return r'\avlink{' + escaped + r'}'


def sort_by_pic(selected):
    return sorted(selected, key=lambda r: r['pic'])


_COL_SPEC = 'l c c r ' + 'r' * len(D_VALUES)


def _header_row():
    cells = ['isogeny class', r'\(g\)', r'\(q\)', r'\(|\Pic(R)|\)']
    for d in D_VALUES:
        cells.append(r'\(D{=}' + str(d) + r'\)')
    return ' & '.join(cells) + r' \\'


def _data_row(row, cell_values):
    leading = [
        render_label_cell(row),
        str(row['g']),
        str(row['q']),
        str(row['pic']),
    ]
    return ' & '.join(leading + cell_values) + r' \\'


def _tabular_for_alg(selected, timings, alg):
    lines = [r'\begin{tabular}{' + _COL_SPEC + r'}',
             r'\toprule', _header_row(), r'\midrule']
    for row in selected:
        cells = []
        for d in D_VALUES:
            wt, _mem, status = timings.get(
                (row['label'], d, alg), ('', '-', 'error'))
            cells.append(fmt_cell(wt, status))
        lines.append(_data_row(row, cells))
    lines.append(r'\bottomrule')
    lines.append(r'\end{tabular}')
    return '\n'.join(lines)


def _tabular_for_overhead(selected, timings):
    lines = [r'\begin{tabular}{' + _COL_SPEC + r'}',
             r'\toprule', _header_row(), r'\midrule']
    for row in selected:
        cells = []
        for d in D_VALUES:
            pol = timings.get((row['label'], d, 'Polarization'),
                              ('', '-', 'error'))
            graph = timings.get((row['label'], d, 'IsogenyGraphBuilder'),
                                ('', '-', 'error'))
            cells.append(fmt_delta_cell(pol[0], pol[2], graph[0], graph[2]))
        lines.append(_data_row(row, cells))
    lines.append(r'\bottomrule')
    lines.append(r'\end{tabular}')
    return '\n'.join(lines)


def emit_combined_table(selected, timings):
    """Single \\begin{table} float with three stacked tabulars and one caption."""
    graph_tab = _tabular_for_alg(selected, timings, 'IsogenyGraphBuilder')
    orbit_tab = _tabular_for_alg(selected, timings, 'IsogenyOrbitBuilder')
    pol_tab = _tabular_for_overhead(selected, timings)
    caption = (
        r'Wall-clock seconds per cell, single-threaded on an Intel '
        r'i9-13900KS (Ubuntu 24.04 LTS, 192~GB RAM), Magma~\magmaVersion. '
        r'\(<0.1\) is below the '
        r'noise floor. Rows ordered by \(|\Pic(R)|\); '
        + BC_MARK + r' marks the base change to \(\F_9\) of '
        + F3_ANCHOR_TEX + r'.'
    )
    out = [
        r'\begin{table}[!ht]',
        r'\centering',
        r'\small',
        '',
        r'\textbf{(a)}~\texttt{IsogenyGraphBuilder} (\ref{alg:compositions})',
        '',
        graph_tab,
        '',
        r'\medskip',
        '',
        r'\textbf{(b)}~\texttt{IsogenyOrbitBuilder} (\ref{alg:GST_orbits})',
        '',
        orbit_tab,
        '',
        r'\medskip',
        '',
        r'\textbf{(c)}~Polarization filter overhead, i.e.\ (\ref{alg:pols_from_dualiso}) $-$ (\ref{alg:compositions})',
        '',
        pol_tab,
        '',
        r'\caption{' + caption + r'}',
        r'\label{tab:section8-timings}',
        r'\end{table}',
    ]
    return '\n'.join(out) + '\n'


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('-t', '--timings', help='timings.tsv')
    parser.add_argument('-s', '--selected', help='selected_polynomials.txt')
    parser.add_argument('-o', '--out-dir',
                        help='directory to write tables_section8.tex etc.')
    args = parser.parse_args(argv)

    if args.self_test:
        unittest.main(argv=[sys.argv[0]] + ['-v'], exit=False, module=__name__)
        return

    if not (args.timings and args.selected and args.out_dir):
        parser.error("--timings, --selected, --out-dir required unless --self-test")

    header, timings = read_timings(args.timings)
    selected = sort_by_pic(read_selected(args.selected))
    table = emit_combined_table(selected, timings)

    os.makedirs(args.out_dir, exist_ok=True)
    out_table = os.path.join(args.out_dir, 'tables_section8.tex')
    out_ver = os.path.join(args.out_dir, 'magma_version.tex')
    out_sha = os.path.join(args.out_dir, 'tables_section8.sha256')

    with open(out_table, 'w') as f:
        f.write(table)

    magma_version = header.get('magma_version', 'unknown')
    with open(out_ver, 'w') as f:
        f.write(r'\newcommand{\magmaVersion}{' + magma_version + r'}' + '\n')

    digest = hashlib.sha256(table.encode('utf-8')).hexdigest()
    with open(out_sha, 'w') as f:
        f.write(f'{digest}  tables_section8.tex\n')

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


class TestFmtDeltaCell(unittest.TestCase):
    def test_positive_delta(self):
        self.assertEqual(fmt_delta_cell('1.5', 'ok', '0.5', 'ok'), '1.0')

    def test_negative_delta_clamped_to_zero(self):
        # Pol < Graph (measurement noise); clamp to zero, render as sub-noise.
        self.assertEqual(fmt_delta_cell('0.4', 'ok', '0.5', 'ok'), r'\(<0.1\)')

    def test_timeout_propagates(self):
        self.assertEqual(fmt_delta_cell('3600', 'timeout', '0.5', 'ok'), r'\(-\)')
        self.assertEqual(fmt_delta_cell('0.5', 'ok', '3600', 'oom'), r'\(-\)')

    def test_error_propagates(self):
        self.assertEqual(fmt_delta_cell('1.0', 'error', '0.5', 'ok'), r'?')


class TestRenderLabelCell(unittest.TestCase):
    def test_avlink_for_non_bc_row(self):
        row = {'label': '4.3.[ 81, 54, -9, -15, -8, -5, -1, 2, 1 ]'}
        self.assertEqual(render_label_cell(row),
                         r'\avlink{4.3.c\_ab\_af\_ai}')

    def test_textsf_with_asterisk_for_bc_row(self):
        row = {'label': '4.9.[ 6561, -4374, 405, 297, -122, 33, 5, -6, 1 ]'}
        self.assertEqual(render_label_cell(row),
                         r'\textsf{4.9.ag\_f\_bh\_aes}' + BC_MARK)

    def test_missing_label_raises(self):
        row = {'label': 'unknown.poly'}
        with self.assertRaises(KeyError):
            render_label_cell(row)


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
        self.assertEqual(rows[1]['pic'], 2)

    def test_timings_round_trip(self):
        header, data = read_timings(self.tsv_path)
        self.assertEqual(header.get('magma_version'), '2.29-7')
        self.assertEqual(len(data), 30)
        key = ('4.3.[ 81, 54, -9, -15, -8, -5, -1, 2, 1 ]',
               12, 'IsogenyGraphBuilder')
        self.assertEqual(data[key][2], 'timeout')


class TestEmitCombinedTable(unittest.TestCase):
    def setUp(self):
        here = os.path.dirname(os.path.abspath(__file__))
        self.sel_path = os.path.join(here, 'tests', 'fixtures', 'tiny_selected.txt')
        self.tsv_path = os.path.join(here, 'tests', 'fixtures', 'tiny_timings.tsv')

    def test_emits_single_table_float(self):
        selected = sort_by_pic(read_selected(self.sel_path))
        _, timings = read_timings(self.tsv_path)
        out = emit_combined_table(selected, timings)
        self.assertEqual(out.count(r'\begin{table}'), 1)
        self.assertEqual(out.count(r'\end{table}'), 1)
        self.assertEqual(out.count(r'\caption{'), 1)
        self.assertEqual(out.count(r'\label{tab:section8-timings}'), 1)

    def test_three_tabulars_with_subheadings(self):
        selected = sort_by_pic(read_selected(self.sel_path))
        _, timings = read_timings(self.tsv_path)
        out = emit_combined_table(selected, timings)
        self.assertEqual(out.count(r'\begin{tabular}'), 3)
        self.assertIn(r'\textbf{(a)}', out)
        self.assertIn(r'\textbf{(b)}', out)
        self.assertIn(r'\textbf{(c)}', out)

    def test_renders_all_status_values(self):
        selected = sort_by_pic(read_selected(self.sel_path))
        _, timings = read_timings(self.tsv_path)
        out = emit_combined_table(selected, timings)
        self.assertIn(r'\(-\)', out)  # timeout/oom from fixtures
        self.assertIn(r'?', out)       # error from fixtures
        self.assertIn(r'\(<0.1\)', out)


if __name__ == '__main__':
    main(sys.argv[1:])
