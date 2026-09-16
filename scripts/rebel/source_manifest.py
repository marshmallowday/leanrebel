"""Reproduce a review manifest; visual-review assertions are recorded, not inferred."""
import json, sys
from pathlib import Path
from compare_papers import compare
meta = {
    'schema': 1,
    'acquired_at_utc': '2026-09-16T19:42:13Z',
    'acquisition': {'repo': 'marshmallowday/leanrebel', 'commit': '996fb5d8f544e36e5c0167e06db6cf93444b9ba2', 'workflow_run': 35142130023, 'artifact': 10465482068},
    'pdfs': [
        {'id': 'main', 'file': 'main.pdf', 'url': 'https://papers.nips.cc/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Paper.pdf', 'sha256': '9b1fd933a38471a3867e8cac492f54e535e4a48c5c38fd418b5598465e56d909', 'bytes': 1475532, 'pages': 13, 'printed_page_offset': 0},
        {'id': 'supp', 'file': 'supp.pdf', 'url': 'https://papers.nips.cc/paper_files/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Supplemental.pdf', 'sha256': '4c5181bd9e637e772b6a866ded14f1cd36bfe85d0fa565c0a6a75920e5f4b3ff', 'bytes': 660850, 'pages': 12, 'printed_page_offset': 13},
        {'id': 'arxiv', 'file': 'arxiv-v2.pdf', 'url': 'https://arxiv.org/pdf/2007.13544v2', 'sha256': '69322b213028142bccd9fa5531623cca0b19666bab56015b589e84a43913eb44', 'bytes': 1918684, 'pages': 25, 'printed_page_offset': 0}],
    'official_commit': '7960a42750f3407ea9eb2c3333d4c2a7961f6df4',
    'official_archive_sha256': 'a536271e7379667a4959c9814d3926cb4baa66373ce50747546a3e8358fe52f7',
    'visual_review': {
        'publication_pages': list(range(1, 26)),
        'arxiv_different_renderings_inspected': [1, 7, 9, 10, 11, 12, 13, 14, 16, 17, 24],
        'arxiv_other_pages': 'Pixel-identical to inspected publication renderings at the recorded renderer settings.',
        'differences': {'1': 'arXiv version/date stamp', '7,9': 'typographic reflow with same extracted words', '10,11,12,13': 'reference reflow; same reference identifiers 1..61', '14,16,17,24': 'bullet glyph changes'},
        'mathematical_result': 'No mathematical amendment found between these fixed editions; this is a human review, not a formal equivalence theorem.'}}
meta['edition_comparison'] = compare(Path(sys.argv[1]))
Path(sys.argv[2]).write_text(json.dumps(meta, ensure_ascii=False, indent=2)+'\n')
