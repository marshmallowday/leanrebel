#!/usr/bin/env python3
"""Check ReBeL ledger structure, NOT Lean proofs or truth of evidence claims.

Uses Python's standard library. Run from any working directory. By default the
repository root is inferred from this file; --root supports validation fixtures.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path, PurePosixPath
import re
import sys

from coverage_inventory import expand

REPOSITORY = "marshmallowday/leanrebel"
STATUSES = {"pending", "in_progress", "blocked", "formalized", "verified",
            "qualified", "refuted", "empirical_documented", "context_indexed"}
REUSE = {"existing_candidate", "bridge_candidate", "new"}
PROOF_FIELDS = {"commit", "module", "declaration", "build_command", "build_log",
                "axioms_log", "semantic_review"}


def safe_path(value: object) -> bool:
    if not isinstance(value, str) or not value or "\\" in value:
        return False
    p = PurePosixPath(value)
    return not p.is_absolute() and ".." not in p.parts


def validate(data: object, root: Path) -> list[str]:
    errors: list[str] = []
    if not isinstance(data, dict):
        return ["ledger must be an object"]
    if data.get("schema_version") != 1:
        errors.append("unsupported schema_version")
    if data.get("repository") != REPOSITORY:
        errors.append("repository must be marshmallowday/leanrebel")
    for key in ("baseline_commit", "official_commit"):
        if not re.fullmatch(r"[0-9a-f]{40}", str(data.get(key, ""))):
            errors.append(f"{key}: expected full commit SHA")
    sources = data.get("source_ids")
    milestones = data.get("milestones")
    if not isinstance(sources, list) or not all(isinstance(x, str) for x in sources):
        return errors + ["source_ids must be a list of strings"]
    if not isinstance(milestones, list) or not all(isinstance(x, str) for x in milestones):
        return errors + ["milestones must be a list of strings"]
    items = data.get("items")
    if not isinstance(items, list) or not items:
        return errors + ["items must be a nonempty list"]
    ids: set[str] = set()
    parents: dict[str, str] = {}
    for pos, item in enumerate(items):
        label = f"items[{pos}]"
        if not isinstance(item, dict):
            errors.append(f"{label}: expected object")
            continue
        name = item.get("id")
        if not isinstance(name, str) or not re.fullmatch(r"[A-Z0-9-]+", name):
            errors.append(f"{label}: invalid id")
            continue
        if name in ids:
            errors.append(f"{name}: duplicate id")
        ids.add(name)
        for key in ("locator", "obligation"):
            if not isinstance(item.get(key), str) or not item[key].strip():
                errors.append(f"{name}: missing {key}")
        for key, allowed in (("source", sources), ("milestone", milestones),
                             ("status", STATUSES), ("reuse", REUSE)):
            value = item.get(key)
            if not isinstance(value, str) or value not in allowed:
                errors.append(f"{name}: invalid {key}")
        candidates = item.get("candidates")
        if not isinstance(candidates, list) or not all(safe_path(p) for p in candidates):
            errors.append(f"{name}: invalid candidate paths")
        parent = item.get("parent_id")
        if parent is not None:
            if not isinstance(parent, str):
                errors.append(f"{name}: invalid parent_id")
            else:
                parents[name] = parent
        evidence = item.get("evidence")
        if not isinstance(evidence, list):
            errors.append(f"{name}: evidence must be a list")
            continue
        if item.get("status") == "verified":
            good = False
            for entry in evidence:
                if not isinstance(entry, dict):
                    continue
                if not all(isinstance(entry.get(k), str) and entry[k].strip()
                           for k in PROOF_FIELDS):
                    continue
                path = entry["module"]
                if (re.fullmatch(r"[0-9a-f]{40}", entry["commit"])
                        and safe_path(path) and path.endswith(".lean")
                        and (root / path).is_file()):
                    good = True
            if not good:
                errors.append(f"{name}: verified needs complete proof evidence and an existing Lean file")
        elif item.get("status") in {"qualified", "refuted", "empirical_documented", "context_indexed"}:
            if not evidence:
                errors.append(f"{name}: this status needs evidence, not just a label")
    for name, parent in parents.items():
        if parent not in ids:
            errors.append(f"{name}: unknown parent_id {parent}")
        seen = {name}
        node = parent
        while node in parents:
            if node in seen:
                errors.append(f"{name}: parent cycle")
                break
            seen.add(node)
            node = parents[node]
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--expanded-json", action="store_true",
                        help="print the complete normalized ledger instead of the summary")
    args = parser.parse_args()
    root = args.root.resolve()
    ledger = root / "docs/rebel/coverage.json"
    try:
        data = json.loads(ledger.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    try:
        data = expand(data, root)
    except (OSError, ValueError, KeyError, TypeError, UnicodeError) as exc:
        print(f"ERROR: child ledger: {exc}", file=sys.stderr)
        return 1
    errors = validate(data, root)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    if args.expanded_json:
        print(json.dumps(data, ensure_ascii=False, indent=2))
        return 0
    counts = Counter(item["status"] for item in data["items"])
    print(f"Ledger structure OK: {len(data['items'])} items; {dict(sorted(counts.items()))}")
    print("No Lean compilation, axiom audit, source-coverage completeness, or semantic verification performed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
