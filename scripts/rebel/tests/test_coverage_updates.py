"""Fail-closed coverage journal tests; no test result is Lean proof evidence."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/rebel"))
from coverage_updates import apply_updates, blob_hash, read_update


class CoverageUpdateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        folder = self.root / "docs/rebel/coverage-updates"
        folder.mkdir(parents=True)
        self.path = folder / "M05.json"
        self.base = self.root / "docs/rebel/coverage.json"
        self.base.write_text('{"frozen":true}\n', encoding="utf-8")
        self.source = self.root / "GameTheory/Example.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text('theorem example : True := True.intro\n', encoding="utf-8")
        self.ledger = {"items": [{"id": "VALUE", "milestone": "M05", "status": "pending",
                                  "obligation": "Original identity", "evidence": [{"old": True}]}]}
        proof = {"commit": "1" * 40, "module": "GameTheory/Example.lean",
                 "source_blob": blob_hash(self.source.read_bytes()), "declaration": "example",
                 "build_command": "fixture", "build_log": "fixture", "axioms_log": "fixture",
                 "semantic_review": "fixture", "assumptions": "fixture", "source_reading": "fixture"}
        self.data = {"schema_version": 1, "base_blob": blob_hash(self.base.read_bytes()),
                     "milestone": "M05", "updates": [{"id": "VALUE", "from_status": "pending",
                                                       "status": "verified", "evidence": [proof]}]}

    def tearDown(self):
        self.temp.cleanup()

    def run_update(self):
        self.path.write_text(json.dumps(self.data), encoding="utf-8")
        return apply_updates(self.ledger, self.root)

    def test_no_updates_preserves_frozen_ledger(self):
        self.assertEqual(apply_updates(self.ledger, self.root), self.ledger)

    def test_only_status_and_appended_evidence_change(self):
        old = copy.deepcopy(self.ledger)
        new = self.run_update()
        self.assertEqual(self.ledger, old)
        self.assertEqual(new["items"][0]["status"], "verified")
        self.assertEqual(new["items"][0]["obligation"], "Original identity")
        self.assertEqual(new["items"][0]["evidence"][0], {"old": True})
        self.assertEqual(len(new["items"][0]["evidence"]), 2)

    def test_stale_base_is_rejected(self):
        self.base.write_text("changed")
        with self.assertRaisesRegex(ValueError, "base blob"):
            self.run_update()

    def test_source_identity_edit_is_rejected(self):
        self.data["updates"][0]["obligation"] = "Weaker statement"
        with self.assertRaisesRegex(ValueError, "source identity"):
            self.run_update()

    def test_unknown_or_duplicate_target_is_rejected(self):
        self.data["updates"][0]["id"] = "MISSING"
        with self.assertRaisesRegex(ValueError, "identity"):
            self.run_update()
        self.data["updates"][0]["id"] = "VALUE"
        self.data["updates"].append(copy.deepcopy(self.data["updates"][0]))
        with self.assertRaisesRegex(ValueError, "identity"):
            self.run_update()

    def test_cross_milestone_and_stale_status_are_rejected(self):
        self.data["milestone"] = "M04"
        with self.assertRaisesRegex(ValueError, "milestone"):
            self.run_update()
        self.data["milestone"] = "M05"
        self.data["updates"][0]["from_status"] = "qualified"
        with self.assertRaisesRegex(ValueError, "stale"):
            self.run_update()

    def test_verified_evidence_cannot_be_downgraded(self):
        self.ledger["items"][0]["status"] = "verified"
        self.data["updates"][0].update(from_status="verified", status="qualified")
        with self.assertRaisesRegex(ValueError, "downgrade"):
            self.run_update()

    def test_missing_scope_or_changed_proof_source_is_rejected(self):
        self.data["updates"][0]["evidence"][0]["assumptions"] = ""
        with self.assertRaisesRegex(ValueError, "incomplete"):
            self.run_update()
        self.data["updates"][0]["evidence"][0]["assumptions"] = "fixture"
        self.source.write_text("changed")
        with self.assertRaisesRegex(ValueError, "source changed"):
            self.run_update()

    def test_duplicate_json_fields_are_rejected(self):
        self.path.write_text('{"schema_version":1,"schema_version":1}')
        with self.assertRaisesRegex(ValueError, "duplicate JSON"):
            read_update(self.path)

    def test_source_path_traversal_is_rejected(self):
        self.data["updates"][0]["evidence"][0]["module"] = "../Example.lean"
        with self.assertRaisesRegex(ValueError, "unsafe"):
            self.run_update()


if __name__ == "__main__":
    unittest.main()
