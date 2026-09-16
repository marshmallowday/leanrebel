"""Positive and hostile-fixture tests for inventory bookkeeping, not Lean proofs."""
from __future__ import annotations
import copy
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/rebel"))
from check_inventory import check
from coverage_inventory import expand
from check_coverage import validate


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        shutil.copytree(ROOT / "docs/rebel", self.root / "docs/rebel")
        reuse = json.loads((self.root / "docs/rebel/inventory/reuse.json").read_text())
        for item in reuse["items"]:
            path = self.root / item["module"]
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / item["module"], path)
        self.path = self.root / "docs/rebel/coverage.json"
        self.data = json.loads(self.path.read_text())

    def tearDown(self):
        self.temp.cleanup()

    def save(self):
        self.path.write_text(json.dumps(self.data))

    def rejected(self):
        self.save()
        with self.assertRaises((ValueError, KeyError, OSError, TypeError)):
            check(self.root)

    def update_hash(self, relative, count_delta=0):
        spec = next(s for s in self.data["child_ledgers"] if s["path"] == relative)
        spec["sha256"] = hashlib.sha256((self.root / relative).read_bytes()).hexdigest()
        spec["child_count"] += count_delta

    def modify_official(self, change, count_delta=0):
        relative = "docs/rebel/inventory/official.json.gz"
        path = self.root / relative
        official = json.loads(gzip.decompress(path.read_bytes()))
        change(official)
        path.write_bytes(gzip.compress(json.dumps(official).encode(), mtime=0))
        self.update_hash(relative, count_delta)

    def test_valid_complete_inventory(self):
        ledger, reuse = check(self.root)
        self.assertEqual(len(ledger["items"]), 3048)
        self.assertEqual(sum(x["status"] == "verified" for x in ledger["items"]), 1)
        self.assertEqual(len(reuse["items"]), 23)

    def test_seed_duplicate(self):
        self.data["items"].append(copy.deepcopy(self.data["items"][0]))
        self.rejected()

    def test_hash_changed(self):
        self.data["child_ledgers"][0]["sha256"] = "0" * 64
        self.rejected()

    def test_child_count_wrong(self):
        self.data["child_ledgers"][0]["child_count"] -= 1
        self.rejected()

    def test_missing_ledger(self):
        self.data["child_ledgers"].pop()
        self.rejected()

    def test_path_traversal(self):
        self.data["child_ledgers"][0]["path"] = "../paper.tsv"
        self.rejected()

    def test_missing_required_equation_even_with_rehashed_file(self):
        relative = "docs/rebel/inventory/paper.tsv"
        path = self.root / relative
        path.write_text("\n".join(s for s in path.read_text().splitlines()
                                  if not s.startswith("P-EQ-18\t")) + "\n")
        self.update_hash(relative, -1)
        self.rejected()

    def test_duplicate_paper_id_even_with_rehashed_file(self):
        relative = "docs/rebel/inventory/paper.tsv"
        path = self.root / relative
        path.write_text(path.read_text().replace("P-EQ-18\t", "P-EQ-17\t"))
        self.update_hash(relative)
        self.rejected()

    def test_official_wrong_commit(self):
        self.modify_official(lambda d: d.update(commit="0" * 40))
        self.rejected()

    def test_official_missing_file_even_with_rehashed_data(self):
        path = self.root / "docs/rebel/inventory/official.json.gz"
        d = json.loads(gzip.decompress(path.read_bytes()))
        delta = -(len(d["files"][-1]["rows"]) + 1)
        self.modify_official(lambda d: d["files"].pop(), delta)
        self.rejected()

    def test_official_invalid_span(self):
        self.modify_official(lambda d: d["files"][0]["rows"][0].__setitem__(0, 0))
        self.rejected()

    def test_official_duplicated_file(self):
        self.modify_official(lambda d: d["files"][1].update(path=d["files"][0]["path"]))
        self.rejected()

    def test_official_unknown_parent(self):
        self.modify_official(lambda d: d["files"][0].update(parent="NO-SUCH-PARENT"))
        self.rejected()

    def test_candidate_source_drift(self):
        p = self.root / "GameTheory/Analysis/Minimax.lean"
        p.write_text(p.read_text() + "\n-- stale review fixture\n")
        self.rejected()

    def test_candidate_range_drift(self):
        p = self.root / "docs/rebel/inventory/reuse.json"
        d = json.loads(p.read_text())
        d["items"][0]["lines"][0] += 1
        p.write_text(json.dumps(d))
        self.rejected()

    def test_child_verified_without_proof_evidence(self):
        self.data["child_overrides"]["P-EQ-01"] = {"status": "verified", "evidence": []}
        self.rejected()

    def test_override_cannot_change_source_identity(self):
        self.data["child_overrides"]["P-EQ-01"] = {"source": "project"}
        self.rejected()

    def test_unknown_override(self):
        self.data["child_overrides"]["P-NONEXISTENT"] = {"status": "pending"}
        self.rejected()

    def test_unreviewed_different_arxiv_page(self):
        p = self.root / "docs/rebel/inventory/sources.json"
        d = json.loads(p.read_text())
        d["visual_review"]["arxiv_different_renderings_inspected"].pop()
        p.write_text(json.dumps(d))
        self.rejected()

    def test_parent_cycle(self):
        self.data["items"][0]["parent_id"] = self.data["items"][0]["id"]
        self.rejected()


if __name__ == "__main__":
    unittest.main()
