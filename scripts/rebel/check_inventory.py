#!/usr/bin/env python3
"""Validate inventory membership/provenance and pinned candidate source ranges.

This rejects detectable omissions and stale data, not all possible semantic
omissions. Paper decomposition and scope classification remain human-reviewed.
Use --lean after lake build to ask the actual compiler for every candidate type.
"""
from __future__ import annotations
import argparse
import csv
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from collections import Counter
from coverage_inventory import expand
from check_coverage import validate, safe_path


def check_source(root: Path, item: dict) -> None:
    """Pin the complete source and exact reviewed span, including reexport definitions."""
    path = item["module"]
    if not safe_path(path) or not path.endswith(".lean"):
        raise ValueError("unsafe candidate source path")
    raw = (root / path).read_bytes()
    if hashlib.sha256(raw).hexdigest() != item["sha256"]:
        raise ValueError("candidate source changed without renewed premise review: " + path)
    start, end = item["lines"]
    if not (isinstance(start, int) and isinstance(end, int) and 1 <= start <= end):
        raise ValueError("invalid candidate source range: " + path)
    if "\n".join(raw.decode().splitlines()[start-1:end]) + "\n" != item["source_excerpt"]:
        raise ValueError("candidate source range differs: " + path)


def check(root: Path, data: dict | None = None) -> tuple[dict, dict]:
    base = root / "docs/rebel"
    if data is None:
        data = json.loads((base / "coverage.json").read_text())
    ledger = expand(data, root)
    errors = validate(ledger, root)
    if errors:
        raise ValueError("; ".join(errors))
    with (base / "inventory/paper.tsv").open(encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    ids = {row["id"] for row in rows}
    required = {f"P-EQ-{i:02}" for i in range(1, 19)}
    required |= {"P-FN-STAR"} | {f"P-FN-{i}" for i in range(2, 11)}
    required |= {f"P-ALG{a}-{i:02}" for a in (1, 2) for i in range(1, 19)}
    required |= {f"P-LEAF-{i:02}" for i in range(1, 8)}
    required |= {f"P-SAMPLE-{i:02}" for i in range(1, 14)}
    required |= {f"P-REF-{i:02}" for i in range(1, 62)}
    required |= {f"P-LEM{i}" for i in range(1, 4)}
    required |= {f"P-THM{i}-{s}" for i in range(1, 4) for s in ("M", "S")}
    required |= {"P-THM4", "P-THM5"}
    if not required <= ids:
        raise ValueError("missing mandatory paper members: " + str(sorted(required - ids)))
    sources = json.loads((base / "inventory/sources.json").read_text())
    if [p["pages"] for p in sources["pdfs"]] != [13, 12, 25]:
        raise ValueError("PDF page membership differs")
    if sources["visual_review"]["publication_pages"] != list(range(1, 26)):
        raise ValueError("publication visual-review coverage differs")
    pairs = sources["edition_comparison"]["comparison"]
    if [p["printed_page"] for p in pairs] != list(range(1, 26)):
        raise ValueError("edition page comparison is incomplete")
    differing = [p["printed_page"] for p in pairs if not p["same_pixels"]]
    if differing != sources["visual_review"]["arxiv_different_renderings_inspected"]:
        raise ValueError("nonidentical arXiv images need explicit review")
    tree = (base / "inventory/official-tree.txt").read_bytes()
    official = json.loads(gzip.decompress((base / "inventory/official.json.gz").read_bytes()))
    if hashlib.sha256(tree).hexdigest() != official["tree_sha256"]:
        raise ValueError("official tree hash differs")
    expected = {}
    for line in tree.decode().splitlines():
        meta, path = line.split("\t", 1)
        mode, kind, sha, size = meta.split()
        expected[path] = (mode, sha, kind)
    actual = {f["path"]: (f["mode"], f["git_sha"], "commit" if f["kind"] == "gitlink" else "blob")
              for f in official["files"]}
    if actual != expected or len(actual) != len(official["files"]):
        raise ValueError("official file membership differs from pinned tree")
    reuse = json.loads((base / "inventory/reuse.json").read_text())
    covered = set()
    for item in reuse["items"]:
        path = item["module"]
        check_source(root, item)
        if "definition_source" in item:
            definition = item["definition_source"]
            check_source(root, definition)
            # A reexport may not silently redirect to an unrelated module.
            imported = definition["module"][:-5].replace("/", ".")
            imports = re.findall(r"^import (.+)$", (root / path).read_text(), re.MULTILINE)
            if not any(imported in line.split() for line in imports):
                raise ValueError("candidate reexport no longer imports its pinned definition: " + path)
        if not re.fullmatch(r"[\w'.]+", item["declaration"]):
            raise ValueError("unsafe candidate declaration")
        covered.add(path)
    candidates = {p for item in data["items"] for p in item["candidates"]}
    if not candidates <= covered:
        raise ValueError("candidate module not premise-reviewed: " + str(candidates - covered))
    return ledger, reuse


def check_lean(root: Path, reuse: dict) -> None:
    folder = root / ".lake/rebel"
    folder.mkdir(parents=True, exist_ok=True)
    lean = folder / "ReuseTypes.lean"
    imports = sorted({x["module"][:-5].replace("/", ".") for x in reuse["items"]})
    text = "\n".join("import " + p for p in imports) + "\n\n"
    text += "\n".join("#check " + x["declaration"] for x in reuse["items"]) + "\n"
    lean.write_text(text)
    subprocess.run(["lake", "env", "lean", str(lean)], cwd=root, check=True)
    print(f"REUSE_COMPILER_TYPES_PASS declarations={len(reuse['items'])}; applicability not proved")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    p.add_argument("--lean", action="store_true")
    a = p.parse_args()
    try:
        ledger, reuse = check(a.root)
        if a.lean:
            check_lean(a.root, reuse)
        print("INVENTORY_STRUCTURE_PASS", len(ledger["items"]), dict(Counter(x["status"] for x in ledger["items"])))
        print("No claim of Lean applicability, complete semantic decomposition, or C++ equivalence.")
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print("ERROR:", exc, file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
