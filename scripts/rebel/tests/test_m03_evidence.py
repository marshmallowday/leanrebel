"""M03 acceptance bookkeeping regressions; these do not replace Lean or source review."""
from __future__ import annotations

from collections import Counter
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

IMPLEMENTATION = "703796b7a7a90b60851a0876ba99976b0be59341"
BASELINE_BLOB = "0e5648d3ab155fe4a0c998d2d3854c14d6593925"
REQUIRED = {
    "PBS-LAW", "PBS-ENCODING", "PBS-UPDATE", "PBS-EQUIVALENCE", "PBS-PERFECT",
    "PBS-SUBGAME", "PBS-POLICY-DOMAIN", "P-FIG1B", "P-PUBLIC-SUBGAME",
    "P-DEPTH-SUBGAME", "P-PBS-ROOT-SUBGAME", "P-PBS-JOINT", "P-PBS-REFEREE",
    "P-PBS-MARGINAL", "P-PBS-COMPACT", "P-PBS-LD-COMPACT", "P-BAYES-PBS",
    "P-BELIEF-EQUIVALENCE", "P-BELIEF-PERFECT", "P-FN-5", "P-FN-6", "P-FN-7",
    "P-DEP-45", "P-DEP-52",
}
QUALIFIED = {
    "PBS-EQUIVALENCE", "P-FIG1B", "P-PBS-REFEREE", "P-PBS-MARGINAL",
    "P-PBS-COMPACT", "P-PBS-LD-COMPACT", "P-BELIEF-EQUIVALENCE",
    "P-FN-5", "P-FN-6", "P-DEP-45", "P-DEP-52",
}
FIELDS = {
    "commit", "module", "declaration", "source_blob", "build_command",
    "build_log", "axioms_log", "semantic_review", "assumptions", "source_reading",
}


def blob_hash(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def check_m03(rows: dict, root: Path) -> None:
    """Reject stale evidence, lost qualifications, and source/decl drift."""
    if not REQUIRED <= rows.keys():
        raise ValueError("missing M03 obligation")
    log = (root / "docs/rebel/M03-compiler-log.txt").read_text(encoding="utf-8")
    if IMPLEMENTATION not in log:
        raise ValueError("wrong evidence source")
    for key in sorted(REQUIRED):
        row = rows[key]
        expected = "qualified" if key in QUALIFIED else "verified"
        if row["milestone"] != "M03" or row["status"] != expected:
            raise ValueError(f"{key}: unreviewed classification change")
        if not row.get("evidence"):
            raise ValueError(f"{key}: absent evidence")
        proof = row["evidence"][0]
        if any(not isinstance(proof.get(k), str) or not proof[k].strip() for k in FIELDS):
            raise ValueError(f"{key}: incomplete proof or scope record")
        if proof["commit"] != IMPLEMENTATION:
            raise ValueError(f"{key}: stale/unreviewed implementation SHA")
        if any(run not in proof["build_log"] for run in ("35276996529", "35276996593")):
            raise ValueError(f"{key}: missing actual passing build runs")
        if "declarations=1348" not in proof["axioms_log"] or "modules=33" not in proof["axioms_log"]:
            raise ValueError(f"{key}: wrong audit surface")
        if "M03.md" not in proof["semantic_review"]:
            raise ValueError(f"{key}: no semantic review")
        path = (root / proof["module"]).resolve()
        if not path.is_relative_to(root.resolve()) or path.suffix != ".lean":
            raise ValueError(f"{key}: invalid source path")
        raw = path.read_bytes()
        if blob_hash(raw) != proof["source_blob"]:
            raise ValueError(f"{key}: source changed without renewed evidence")
        name = proof["declaration"]
        if not name.startswith("GameTheory.ReBeL."):
            raise ValueError(f"{key}: wrong declaration namespace")
        short = re.escape(name.split(".")[-1])
        if not re.search(r"\b(?:theorem|def|structure|abbrev)\s+" + short + r"(?=\s|\(|\{|:)", raw.decode()):
            raise ValueError(f"{key}: declaration missing from its source")
        pattern = r"^REBEL_AXIOMS " + re.escape(name) + r": \[([^\]]*)\]$"
        match = re.search(pattern, log, re.M)
        if not match:
            raise ValueError(f"{key}: no retained principal-declaration axiom line")
        axioms = {part.strip() for part in match[1].split(",") if part.strip()}
        if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError(f"{key}: forbidden axiom in evidence")


class M03EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ledger, _ = check(ROOT)
        cls.rows = {row["id"]: row for row in cls.ledger["items"]}

    def test_original_obligations_and_accepted_evidence_are_preserved(self):
        raw = (Path(__file__).with_name("fixtures") / "coverage_pre_m03.json").read_bytes()
        self.assertEqual(blob_hash(raw), BASELINE_BLOB)
        baseline = json.loads(raw)
        current = json.loads((ROOT / "docs/rebel/coverage.json").read_text(encoding="utf-8"))
        self.assertEqual(current["child_ledgers"], baseline["child_ledgers"])
        for old in expand(baseline, ROOT)["items"]:
            with self.subTest(obligation=old["id"]):
                self.assertIn(old["id"], self.rows)
                new = self.rows[old["id"]]
                for field in ("id", "parent_id", "source", "locator", "obligation", "milestone"):
                    self.assertEqual(new.get(field), old.get(field), field)
                if old["evidence"]:
                    self.assertEqual(new["evidence"][:len(old["evidence"])], old["evidence"])
                if old["status"] == "verified":
                    self.assertEqual(new["status"], "verified")
        # Later milestones may add evidence, but cannot erase these identities or proofs.

    def test_every_m03_obligation_has_pinned_and_qualified_evidence(self):
        check_m03(self.rows, ROOT)
        self.assertEqual(Counter(self.rows[k]["status"] for k in REQUIRED),
                         Counter({"verified": 13, "qualified": 11}))

    def test_explicit_build_and_lint_surface_is_retained(self):
        log = (ROOT / "docs/rebel/M03-compiler-log.txt").read_text(encoding="utf-8")
        built = set(re.findall(r"^REBEL_AUDIT_MODULE (\S+)$", log, re.M))
        linted = set(re.findall(r"^REBEL_LINT_PASS (\S+)$", log, re.M))
        self.assertEqual(len(built), 33)
        self.assertEqual(built, linted)
        self.assertTrue({"GameTheory.Protocol.BehavioralReach",
                         "GameTheory.Analysis.Protocol.CounterfactualReach"} <= built)
        umbrella = (ROOT / "GameTheory/ReBeL.lean").read_text(encoding="utf-8")
        for path in (ROOT / "GameTheory/ReBeL").rglob("*.lean"):
            module = path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
            self.assertIn("import " + module, umbrella)
            self.assertIn(module, built)

    def test_failed_old_sha_is_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows["PBS-LAW"]["evidence"][0]["commit"] = "5576151cfc97945a9a958c8a5eee54d4d5599343"
        with self.assertRaisesRegex(ValueError, "SHA"):
            check_m03(rows, ROOT)

    def test_forged_source_blob_is_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows["PBS-LAW"]["evidence"][0]["source_blob"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "source changed"):
            check_m03(rows, ROOT)

    def test_qualified_claim_cannot_be_silently_promoted(self):
        rows = copy.deepcopy(self.rows)
        rows["PBS-EQUIVALENCE"]["status"] = "verified"
        with self.assertRaisesRegex(ValueError, "classification"):
            check_m03(rows, ROOT)

    def test_missing_assumptions_are_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows["PBS-EQUIVALENCE"]["evidence"][0]["assumptions"] = ""
        with self.assertRaisesRegex(ValueError, "scope"):
            check_m03(rows, ROOT)


if __name__ == "__main__":
    unittest.main()
