"""Check M05 evidence integrity and scope, not mathematical truth or CI authenticity."""
from collections import Counter
import copy
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/rebel"))
from coverage_inventory import expand
from coverage_updates import apply_updates, read_update
from check_coverage import validate
from check_inventory import check

PROOF_COMMIT = "b1b557b7e3c9471e5f774c7fc400c1665742a614"
REFUTED = {"P-FN-8", "P-EQ-03", "P-THM1-S", "P-F-CONCAVITY-STEP", "P-F-RADIAL-NORMAL"}
VERIFIED = {"PBS-EV", "P-PBS-EXPECTED", "P-PBS-EQUILIBRIUM", "P-TYPE-EQUILIBRIUM",
            "P-EQ-11", "P-L1-GLUING", "P-L2-MINIMAX", "P-L2-EQUILIBRIUM"}


class M05EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        folder = ROOT / "docs/rebel/coverage-updates"
        active, candidate = folder / "M05.json", folder / "M05.json.candidate"
        if active.exists() == candidate.exists():
            raise AssertionError("Exactly one active M05 journal or inactive candidate is required")
        cls.active = active.exists()
        cls.path = active if cls.active else candidate
        cls.update = read_update(cls.path)
        cls.raw = json.loads((ROOT / "docs/rebel/coverage.json").read_text(encoding="utf-8"))
        cls.baseline = expand(cls.raw, ROOT)

    def apply_in_isolation(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            dest = root / "docs/rebel/coverage-updates"
            dest.mkdir(parents=True)
            shutil.copyfile(self.path, dest / "M05.json")
            shutil.copyfile(ROOT / "docs/rebel/coverage.json", root / "docs/rebel/coverage.json")
            for entry in self.update["updates"]:
                for proof in entry["evidence"]:
                    target = root / proof["module"]
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / proof["module"], target)
            return apply_updates(self.baseline, root)

    def test_exact_m05_membership_and_dispositions(self):
        expected = {row["id"] for row in self.baseline["items"] if row["milestone"] == "M05"}
        entries = self.update["updates"]
        self.assertEqual(len(expected), 43)
        self.assertEqual(len(entries), len(expected))
        self.assertEqual({entry["id"] for entry in entries}, expected)
        for entry in entries:
            expected_status = ("refuted" if entry["id"] in REFUTED else
                               "verified" if entry["id"] in VERIFIED else "qualified")
            self.assertEqual(entry["status"], expected_status, entry["id"])
        self.assertEqual(Counter(entry["status"] for entry in entries),
                         {"verified": 8, "qualified": 30, "refuted": 5})

    def test_source_blobs_and_prior_evidence_are_preserved(self):
        before = copy.deepcopy(self.baseline)
        after = self.apply_in_isolation()
        self.assertEqual(self.baseline, before)
        old = {row["id"]: row for row in before["items"]}
        new = {row["id"]: row for row in after["items"]}
        self.assertEqual(set(old), set(new))
        for ident, previous in old.items():
            current = new[ident]
            if previous["milestone"] != "M05":
                self.assertEqual(current, previous, ident)
            else:
                self.assertEqual({k: v for k, v in current.items() if k not in {"status", "evidence"}},
                                 {k: v for k, v in previous.items() if k not in {"status", "evidence"}})
                self.assertEqual(current["evidence"][:len(previous["evidence"])],
                                 previous["evidence"])
        self.assertEqual(validate(after, ROOT), [])

    def test_proof_anchor_and_declaration_membership(self):
        for entry in self.update["updates"]:
            for proof in entry["evidence"]:
                with self.subTest(ident=entry["id"], declaration=proof["declaration"]):
                    self.assertEqual(proof["commit"], PROOF_COMMIT)
                    self.assertIn("35411381522", proof["build_log"])
                    self.assertIn("35411381563", proof["build_log"])
                    self.assertIn("docs/rebel/M05.md", proof["semantic_review"])
                    source = (ROOT / proof["module"]).read_text(encoding="utf-8")
                    short = proof["declaration"].rsplit(".", 1)[-1]
                    self.assertRegex(source, r"\b(?:theorem|lemma|def|abbrev)\s+" + re.escape(short) + r"\b")
                    self.assertTrue(proof["assumptions"].strip())
                    self.assertTrue(proof["source_reading"].strip())

    def test_candidate_is_not_silently_accepted_by_live_tools(self):
        live, _ = check(ROOT)
        rows = [row for row in live["items"] if row["milestone"] == "M05"]
        if self.active:
            self.assertEqual(Counter(row["status"] for row in rows),
                             {"verified": 8, "qualified": 30, "refuted": 5})
            report = (ROOT / "docs/rebel/M05-validation.md").read_text(encoding="utf-8")
            self.assertIn("PROOF_SOURCE_ACCEPTED=" + PROOF_COMMIT, report)
        else:
            self.assertTrue(all(row["status"] == "pending" for row in rows))
            self.assertNotIn("PROOF_SOURCE_ACCEPTED=" + PROOF_COMMIT,
                             (ROOT / "docs/rebel/M05-validation.md").read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
