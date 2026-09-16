#!/usr/bin/env python3
"""Reproduce the pinned ReBeL PDF edition comparison; no OCR or source copying.

PyMuPDF==1.26.7 (MuPDF 1.26.12), RGB, alpha=False, scale=1.2.
The manifest records hashes of both normalized text and raster bytes per page.
Equal extracted text alone is NOT evidence that mathematics/images are equal.
The separate human visual review covers all publication pages and every
nonidentical arXiv rendering; this program does not certify that review.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

PDFS = {
    "main": (13, "9b1fd933a38471a3867e8cac492f54e535e4a48c5c38fd418b5598465e56d909"),
    "supp": (12, "4c5181bd9e637e772b6a866ded14f1cd36bfe85d0fa565c0a6a75920e5f4b3ff"),
    "arxiv-v2": (25, "69322b213028142bccd9fa5531623cca0b19666bab56015b589e84a43913eb44"),
}

def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def compare(folder: Path) -> dict:
    import fitz
    if fitz.version[:2] != ("1.26.7", "1.26.12"):
        raise ValueError("renderer version differs from audited comparison")
    docs = {}
    records = {}
    for name, (pages, expected) in PDFS.items():
        path = folder / (name + ".pdf")
        if sha(path.read_bytes()) != expected:
            raise ValueError(f"PDF byte hash differs: {name}")
        doc = fitz.open(path)
        if len(doc) != pages:
            raise ValueError("page count differs")
        docs[name] = doc
        records[name] = []
        for page in doc:
            text = re.sub(r"\s+", " ", page.get_text()).strip().encode()
            pix = page.get_pixmap(matrix=fitz.Matrix(1.2, 1.2), colorspace=fitz.csRGB, alpha=False)
            records[name].append({"text_sha256": sha(text), "rgb_sha256": sha(pix.samples),
                                  "size": [pix.width, pix.height]})
    pairs = []
    for i in range(25):
        source, p = ("main", i) if i < 13 else ("supp", i - 13)
        first, second = records[source][p], records["arxiv-v2"][i]
        pairs.append({"printed_page": i + 1, "publication": source,
                      "pdf_page": p + 1,
                      "same_text": first["text_sha256"] == second["text_sha256"],
                      "same_pixels": first["rgb_sha256"] == second["rgb_sha256"]
                                     and first["size"] == second["size"]})
    for doc in docs.values():
        doc.close()
    return {"pymupdf": "1.26.7", "mupdf": "1.26.12", "scale": 1.2,
            "color": "RGB", "alpha": False, "pages": records, "comparison": pairs}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--pdf-dir", required=True, type=Path)
    p.add_argument("--manifest", required=True, type=Path)
    a = p.parse_args()
    try:
        expected = json.loads(a.manifest.read_text())["edition_comparison"]
        actual = compare(a.pdf_dir)
        if actual != expected:
            raise ValueError("edition comparison differs")
        print("PAPER_COMPARISON_PASS 50 page records, 25 edition pairs; not semantic verification")
    except (OSError, ValueError, KeyError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
