#!/usr/bin/env python3
import csv
import sys

from bs4 import BeautifulSoup

soup = BeautifulSoup(sys.stdin, 'html.parser')

output = csv.writer(sys.stdout, lineterminator='\n')
output.writerow(('variant', 'id', 'pattern', 'dir', 'great', 'name', 'parse'))

for section in soup.main('section', recursive=False):
    section_title = section.h2.get_text().strip()
    section_first = True
    for subsection in section('div', recursive=False):
        if subsection.h3 is None:
            continue
        subsection_title = subsection.h3.get_text().strip()
        subsection_first = True

        # for pattern in subsection('h4'):
        for pattern in subsection('h4', class_='pattern-title'):
            pattern_title = pattern.get_text().split('(')[0].strip()
            pattern_title = pattern_title.replace('Rfln.', 'Reflection')
            pattern_title = pattern_title.replace('Prfn.', 'Purification')
            pattern_title = pattern_title.replace('Dstl.', 'Distillation')
            pattern_title = pattern_title.replace('Tan.', 'Tangent')
            if '.' in pattern_title:
                print(pattern_title)
                raise RuntimeError()

            pattern = pattern.parent

            data = pattern.canvas
            if data is None:
                continue
            output.writerow((
                ''.join(c for c in pattern_title if c.isalpha()),
                pattern['id'].split('@')[-1],
                data['data-string'],
                data['data-start'],
                1 if data['data-per-world'] == 'True' else 0,
                pattern_title,
                pattern_title.lower(),
            ))
