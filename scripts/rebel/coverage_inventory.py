#!/usr/bin/env python3
"""Expand the versioned child ledgers referenced by coverage.json (stdlib only).

A source occurrence is a pending proof obligation, never an automatic proof.
Official syntax rows include declarations/bindings, not just distinct functions.
The compressed snapshot is data; it is never imported or executed.
"""
from __future__ import annotations
import copy
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath

MAX_BYTES = 4_000_000
PAPER_COLUMNS = ["id", "parent", "source", "locator", "kind", "obligation"]
OFFICIAL_COLUMNS = ["line", "column", "end_line", "kind", "label"]
KINDS = {"context", "definition", "claim", "setting", "experiment", "footnote",
         "equation", "theorem", "lemma", "operation", "dependency", "audit"}


def read_checked(root: Path, spec: dict) -> bytes:
    path = PurePosixPath(spec["path"])
    if path.is_absolute() or ".." in path.parts or "\\" in str(path):
        raise ValueError("unsafe inventory path")
    raw = (root / path).read_bytes()
    if len(raw) > MAX_BYTES or hashlib.sha256(raw).hexdigest() != spec["sha256"]:
        raise ValueError(f"inventory hash/size mismatch: {path}")
    if spec["format"] == "official-json-gzip-v1":
        with gzip.GzipFile(fileobj=io.BytesIO(raw)) as f:
            raw = f.read(MAX_BYTES + 1)
        if len(raw) > MAX_BYTES:
            raise ValueError("decompressed inventory exceeds size limit")
    return raw


def child(ident: str, parent: dict, source: str, locator: str,
          obligation: str, context: bool = False) -> dict:
    return {"id": ident, "parent_id": parent["id"], "source": source,
            "locator": locator, "obligation": obligation,
            "milestone": parent["milestone"], "reuse": "new", "candidates": [],
            "status": "context_indexed" if context else "pending",
            "evidence": [{"source_review": "docs/rebel/M01-B.md",
                          "scope": "provenance/context only; not a proved behavior"}] if context else []}


def expand(data: dict, root: Path) -> dict:
    result = copy.deepcopy(data)
    seeds = {item["id"]: item for item in result["items"]}
    children = []
    formats = []
    for spec in result.get("child_ledgers", []):
        raw = read_checked(root, spec)
        fmt = spec["format"]
        formats.append(fmt)
        start = len(children)
        if fmt == "paper-tsv-v1":
            reader = csv.DictReader(io.StringIO(raw.decode()), delimiter="\t")
            if reader.fieldnames != PAPER_COLUMNS:
                raise ValueError("paper inventory columns differ")
            for row in reader:
                if set(row) != set(PAPER_COLUMNS) or None in row.values() or row["kind"] not in KINDS:
                    raise ValueError("malformed paper row")
                children.append(child(row["id"], seeds[row["parent"]], row["source"],
                                      row["locator"], row["obligation"], row["kind"] == "context"))
        elif fmt == "official-json-gzip-v1":
            inv = json.loads(raw)
            if (inv["schema"] != 1 or inv["commit"] != result["official_commit"]
                    or inv["columns"] != OFFICIAL_COLUMNS):
                raise ValueError("official schema/commit/columns differ")
            paths = set()
            for num, file in enumerate(inv["files"], 1):
                path = file["path"]
                if path in paths:
                    raise ValueError("duplicate official file")
                paths.add(path)
                base = child(f"O-F{num:03}", seeds[file["parent"]], "official",
                             f"{path}@{inv['commit']} git-object={file['git_sha']}",
                             "Index pinned " + file["kind"] + "; external gitlink contents are not inspected.", True)
                children.append(base)
                if file["kind"] == "gitlink" and file["rows"]:
                    raise ValueError("gitlink must not claim inspected occurrences")
                for idx, row in enumerate(file["rows"], 1):
                    if len(row) != 5:
                        raise ValueError("malformed official row")
                    line, col, end, kind, label = row
                    if not (isinstance(line, int) and isinstance(end, int) and isinstance(col, int)
                            and 1 <= line <= end <= file["lines"] and col >= 0
                            and isinstance(kind, str) and isinstance(label, str) and label):
                        raise ValueError("invalid official source span")
                    context = kind == "context-line"
                    text = ("Index source context: " if context else
                            "Specify and refine this source occurrence, including its calls, parameter and numeric contracts: ")
                    children.append(child(f"{base['id']}-{idx:04}", base, "official",
                                          f"{path}:L{line}-L{end},column0={col}; {kind}@{inv['commit']}",
                                          text + label, context))
        else:
            raise ValueError("unknown child ledger format")
        if len(children) - start != spec["child_count"]:
            raise ValueError(f"child count differs: {spec['path']}")
    if len(formats) != len(set(formats)):
        raise ValueError("duplicate child ledger format")
    if result.get("inventory_status", "").startswith("M01_B_") and set(formats) != {
            "paper-tsv-v1", "official-json-gzip-v1"}:
        raise ValueError("M01-B closure requires both complete child ledgers")
    by_id = {item["id"]: item for item in children}
    overrides = result.get("child_overrides", {})
    for ident, fields in overrides.items():
        if ident not in by_id or not set(fields) <= {"status", "evidence", "candidates", "reuse"}:
            raise ValueError("invalid child override; source identity cannot be overridden")
        by_id[ident].update(fields)
    result["items"].extend(children)
    return result
