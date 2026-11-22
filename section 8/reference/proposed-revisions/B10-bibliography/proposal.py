"""Batch B10: bibliography (R159, R160, R161).

The two publication records were checked against the Crossref records of the
DOIs given by the referee (2026-11-20): J. Eur. Math. Soc. 24 (2022), no. 5,
1617-1678 (online 2021); Algebraic Geometry 8 (2021), no. 2, 196-230.
arXiv:1006.1393 has an identifier of June 2010, so the year 2009 was wrong.
"""

TITLE = 'Section 8 review B10: bibliography'
ANCHORS = ['Motivic integration and Milnor fiber', 'Quantifier elimination and minimality conditions']

EDITS = [
    (r'arXiv:1810.03561, 2018.',
     r'arXiv:1810.03561, 2018.',
     r'''{\em Journal of the European Mathematical Society} \textbf{24} (2022), no.~5, 1617--1678.'''),

    (r'arXiv:1912.11638, 2019',
     r'arXiv:1912.11638, 2019',
     r'''{\em Algebraic Geometry} \textbf{8} (2021), no.~2, 196--230.'''),

    (r'arXiv:1006.1393v1, 2009.',
     r'arXiv:1006.1393v1, 2009.',
     r'''arXiv:1006.1393v1, 2010.'''),
]

RESOLUTIONS = {
    '159': r'The entry now gives the published version: J. Eur. Math. Soc. \textbf{24} (2022), no.~5, 1617--1678.',
    '160': r'The entry now gives the published version, Algebraic Geometry \textbf{8} (2021), no.~2, 196--230, with its final full stop.',
    '161': r'The year is corrected to 2010.',
}
