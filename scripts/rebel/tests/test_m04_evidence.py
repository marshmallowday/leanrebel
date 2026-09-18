"""M04 evidence integrity regressions, not substitutes for Lean or source review."""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/rebel"))
from check_inventory import check
from coverage_inventory import expand
from audit_axioms import proof_modules

IMPLEMENTATION = "ee8fdf1d63af8c592d1d2ee4949df385a6341a4f"
BASELINE_BLOB = "8dbcba1f23a7eb8daf37ae57212d1a12df93d0a8"
REQUIRED = {
    "FOUND-NASH", "CFR-REACH", "CFR-REGRET", "CFR-MATCH", "CFR-SCHEDULE",
    "CFR-NASH", "POLICY-AVERAGE", "BR-ATTAINMENT", "P-BEST-RESPONSE", "P-NASH",
    "P-EQ-VALUE-UNIQUE", "P-OWN-REACH", "P-REACH-MIX", "P-REACH-ZERO",
    "P-DEP-61", "M04-RATIONAL-REFINEMENT",
}
FIELDS = {
    "commit", "module", "declaration", "source_blob", "build_command", "build_log",
    "axioms_log", "semantic_review", "assumptions", "source_reading",
}


def blob_hash(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def check_m04(rows: dict, root: Path) -> None:
    """Reject unreviewed status changes, stale evidence and forbidden trust claims."""
    if not REQUIRED <= rows.keys():
        raise ValueError("missing M04 obligation")
    log = (root / "docs/rebel/M04-compiler-log.txt").read_text(encoding="utf-8")
    if IMPLEMENTATION not in log:
        raise ValueError("wrong evidence source")
    if rows["P-DEP-28"]["status"] != "context_indexed":
        raise ValueError("unused solver alternative is not a proved dependency")
    if rows["M04-RUNTIME-CROSSCHECK"]["status"] != "empirical_documented":
        raise ValueError("runtime cross-check is not a kernel proof")
    for key in sorted(REQUIRED):
        row = rows[key]
        if row["milestone"] != "M04" or row["status"] != "verified":
            raise ValueError(f"{key}: unreviewed classification")
        if not row.get("evidence"):
            raise ValueError(f"{key}: absent evidence")
        proof = row["evidence"][0]
        if any(not isinstance(proof.get(k), str) or not proof[k].strip() for k in FIELDS):
            raise ValueError(f"{key}: incomplete proof or scope record")
        if proof["commit"] != IMPLEMENTATION:
            raise ValueError(f"{key}: stale/unreviewed implementation SHA")
        if any(run not in proof["build_log"] for run in ("35379068914", "35379068655")):
            raise ValueError(f"{key}: missing exact passing runs")
        path = (root / proof["module"]).resolve()
        if not path.is_relative_to(root.resolve()) or path.suffix != ".lean":
            raise ValueError(f"{key}: invalid source path")
        raw = path.read_bytes()
        if blob_hash(raw) != proof["source_blob"]:
            raise ValueError(f"{key}: source changed without renewed evidence")
        name = proof["declaration"]
        if not name.startswith("GameTheory.ReBeL."):
            raise ValueError(f"{key}: wrong namespace")
        short = re.escape(name.split(".")[-1])
        if not re.search(r"\b(?:theorem|def|structure|abbrev)\s+" + short + r"(?=\s|\(|\{|:)",
                         raw.decode()):
            raise ValueError(f"{key}: missing principal declaration")
        pattern = r"^REBEL_AXIOMS " + re.escape(name) + r": \[([^\]]*)\]$"
        match = re.search(pattern, log, re.M)
        if not match:
            raise ValueError(f"{key}: absent principal axiom evidence")
        axioms = {part.strip() for part in match[1].split(",") if part.strip()}
        if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError(f"{key}: forbidden axiom")


class M04EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ledger, _ = check(ROOT)
        cls.rows = {row["id"]: row for row in cls.ledger["items"]}

    def test_all_original_identities_and_previous_evidence_are_preserved(self):
        raw = (Path(__file__).with_name("fixtures") / "coverage_pre_m04.json").read_bytes()
        self.assertEqual(blob_hash(raw), BASELINE_BLOB)
        baseline = json.loads(raw)
        current = json.loads((ROOT / "docs/rebel/coverage.json").read_text(encoding="utf-8"))
        self.assertEqual(current["child_ledgers"], baseline["child_ledgers"])
        for old in expand(baseline, ROOT)["items"]:
            with self.subTest(obligation=old["id"]):
                new = self.rows[old["id"]]
                for field in ("id", "parent_id", "source", "locator", "obligation", "milestone"):
                    self.assertEqual(new.get(field), old.get(field), field)
                if old["evidence"]:
                    self.assertEqual(new["evidence"][:len(old["evidence"])], old["evidence"])
                if old["status"] in {"verified", "qualified"}:
                    self.assertEqual(new["status"], old["status"])
        # Later milestones can add real evidence, never erase original identities.

    def test_each_m04_proof_has_exact_source_and_scope(self):
        check_m04(self.rows, ROOT)

    def test_current_surface_includes_all_accepted_build_and_lint_modules(self):
        log = (ROOT / "docs/rebel/M04-compiler-log.txt").read_text(encoding="utf-8")
        built = set(re.findall(r"^REBEL_AUDIT_MODULE (\S+)$", log, re.M))
        linted = set(re.findall(r"^REBEL_LINT_PASS (\S+)$", log, re.M))
        count = re.search(r"^REBEL_VALIDATION_PASS modules=(\d+)$", log, re.M)
        self.assertIsNotNone(count)
        self.assertEqual(len(built), int(count[1]))
        self.assertGreater(len(built), 33)
        self.assertEqual(built, linted)
        self.assertTrue(built <= set(proof_modules()))
        self.assertIn("GameTheory.Analysis.ReBeL.Examples.EquilibriumValue", built)
        self.assertIn("GameTheory.Analysis.ReBeL.Examples.RationalAverage", built)
        self.assertRegex(log, r"REBEL_AXIOM_AUDIT_PASS declarations=[1-9][0-9]*")

    def test_failed_resume_sha_is_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows["CFR-NASH"]["evidence"][0]["commit"] = "04e956afd8c0805b687a1d9980b4dcd8c25ee2bf"
        with self.assertRaisesRegex(ValueError, "SHA"):
            check_m04(rows, ROOT)

    def test_forged_blob_is_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows["CFR-NASH"]["evidence"][0]["source_blob"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "source changed"):
            check_m04(rows, ROOT)

    def test_missing_assumptions_are_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows["CFR-NASH"]["evidence"][0]["assumptions"] = ""
        with self.assertRaisesRegex(ValueError, "scope"):
            check_m04(rows, ROOT)

    def test_unused_alternative_cannot_be_promoted(self):
        rows = copy.deepcopy(self.rows)
        rows["P-DEP-28"]["status"] = "verified"
        with self.assertRaisesRegex(ValueError, "unused solver"):
            check_m04(rows, ROOT)

    def test_runtime_evidence_cannot_be_called_a_kernel_proof(self):
        rows = copy.deepcopy(self.rows)
        rows["M04-RUNTIME-CROSSCHECK"]["status"] = "verified"
        with self.assertRaisesRegex(ValueError, "runtime cross-check"):
            check_m04(rows, ROOT)


if __name__ == "__main__":
    unittest.main()
