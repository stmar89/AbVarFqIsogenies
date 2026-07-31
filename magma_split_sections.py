"""
Split magma_gen_all_plots.m output into per-section data files.

Usage:
    python3 magma_split_sections.py all_plots_raw.txt plot_data/
"""
import sys
import os
import re

def split_sections(input_file, output_dir):
    os.makedirs(output_dir, exist_ok=True)
    with open(input_file) as f:
        content = f.read()

    pattern = re.compile(r'==SECTION (\w+)==')
    parts = pattern.split(content)
    # parts = [before_first, name1, body1, name2, body2, ...]
    sections = {}
    for i in range(1, len(parts), 2):
        name = parts[i]
        body = parts[i + 1].strip()
        if name in sections:
            raise ValueError("duplicate section: " + name)
        sections[name] = body

    for name, body in sections.items():
        out_path = os.path.join(output_dir, name + '.txt')
        with open(out_path, 'w') as f:
            f.write(body + '\n')
        print("Wrote %s (%d chars)" % (out_path, len(body)))

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    split_sections(sys.argv[1], sys.argv[2])
