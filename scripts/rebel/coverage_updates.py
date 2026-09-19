#!/usr/bin/env python3
"""Apply audited, append-only status updates after expanding the pinned ledger.

The historical coverage.json and its source inventory stay byte-for-byte intact.
This is bookkeeping, not a substitute for compiling or reviewing Lean proofs.
"""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

from coverage_inventory import expand

MAX_BYTES = 4_000_000
PROOF_FIELDS = {
    "commit", "module", "declaration", "source_blob", "build_command", "build_log",
    "axioms_log", "semantic_review", "assumptions", "source_reading",
}


def blob_hash(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON field in coverage update")
        result[key] = value
    return result


def read_update(path: Path) -> dict:
    if path.is_symlink():
        raise ValueError("coverage update must not be a symlink")
    raw = path.read_bytes()
    if len(raw) > MAX_BYTES:
        raise ValueError("coverage update exceeds size limit")
    data = json.loads(raw, object_pairs_hook=unique_object)
    if not isinstance(data, dict):
        raise ValueError("coverage update must be an object")
    return data


def apply_updates(ledger: dict, root: Path) -> dict:
    """Return a new ledger, rejecting stale anchors, identity edits and lost evidence."""
    result = copy.deepcopy(ledger)
    paths = sorted((root / "docs/rebel/coverage-updates").glob("*.json"))
    if not paths:
        return result
    base_raw = (root / "docs/rebel/coverage.json").read_bytes()
    base_blob = blob_hash(base_raw)
    rows = {item["id"]: item for item in result["items"]}
    if len(rows) != len(result["items"]):
        raise ValueError("duplicate source identity before coverage updates")
    touched = set()
    for path in paths:
        update = read_update(path)
        if set(update) != {"schema_version", "base_blob", "milestone", "updates"}:
            raise ValueError("unknown coverage update fields")
        if type(update["schema_version"]) is not int or update["schema_version"] != 1:
            raise ValueError("unsupported coverage update schema")
        if update["base_blob"] != base_blob:
            raise ValueError("coverage update base blob differs; rebase must be explicit")
        entries = update["updates"]
        if not isinstance(entries, list) or not entries:
            raise ValueError("coverage update entries must be a nonempty list")
        for entry in entries:
            if not isinstance(entry, dict) or set(entry) != {
                    "id", "from_status", "status", "evidence"}:
                raise ValueError("coverage update cannot edit source identity or omit fields")
            ident = entry["id"]
            if not isinstance(ident, str) or ident not in rows or ident in touched:
                raise ValueError("unknown or duplicate coverage update identity")
            touched.add(ident)
            row = rows[ident]
            if row["milestone"] != update["milestone"]:
                raise ValueError("coverage update crosses milestone boundary")
            if entry["from_status"] != row["status"]:
                raise ValueError("stale coverage update status")
            if entry["status"] not in {"formalized", "verified", "qualified", "refuted"}:
                raise ValueError("invalid coverage update status")
            if row["status"] == "verified" and entry["status"] != "verified":
                raise ValueError("coverage update cannot downgrade verified evidence")
            evidence = entry["evidence"]
            if not isinstance(evidence, list) or not evidence:
                raise ValueError("coverage update requires new evidence")
            for proof in evidence:
                if not isinstance(proof, dict) or any(
                        not isinstance(proof.get(key), str) or not proof[key].strip()
                        for key in PROOF_FIELDS):
                    raise ValueError("coverage update has incomplete proof/scope evidence")
                if not re.fullmatch(r"[0-9a-f]{40}", proof["commit"]):
                    raise ValueError("coverage update requires a full proof commit")
                module = PurePosixPath(proof["module"])
                if (module.is_absolute() or ".." in module.parts or "\\" in str(module)
                        or module.suffix != ".lean"):
                    raise ValueError("unsafe coverage update module path")
                source = root / module
                if not source.resolve().is_relative_to(root.resolve()):
                    raise ValueError("coverage update module escapes repository")
                if blob_hash(source.read_bytes()) != proof["source_blob"]:
                    raise ValueError("coverage update proof source changed")
            row["status"] = entry["status"]
            row["evidence"].extend(copy.deepcopy(evidence))
    return result


def expand_with_updates(data: dict, root: Path) -> dict:
    """Canonical live ledger; expand() alone remains available for frozen fixtures."""
    return apply_updates(expand(data, root), root)
