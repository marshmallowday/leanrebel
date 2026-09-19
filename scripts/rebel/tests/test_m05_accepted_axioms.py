"""Check retained compiler-excerpt integrity, not proof truth or CI authenticity."""
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[3]
SOURCE = "b1b557b7e3c9471e5f774c7fc400c1665742a614"
LOG_SHA256 = "39a814432300e9b86ae589329d23ca1c6dfe7662eac03c76115e6a8d79c533f8"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def validate_excerpt(text, anchors):
    """Require complete, unique axiom records for exactly the selected anchors."""
    lines = text.splitlines()
    if lines.count("# Source: " + SOURCE) != 1:
        raise ValueError("wrong or missing proof source")
    if lines.count("# Full log SHA-256: " + LOG_SHA256) != 1:
        raise ValueError("wrong or missing full-log identity")
    for marker in ("REBEL_AXIOM_AUDIT_PASS declarations=2543",
                   "REBEL_VALIDATION_PASS modules=105"):
        if lines.count(marker) != 1:
            raise ValueError("missing or duplicate whole-run pass marker")
    records = {}
    for line in lines:
        if not line.startswith("REBEL_AXIOMS "):
            continue
        match = re.fullmatch(r"REBEL_AXIOMS ([^:\s]+): \[([^\]]*)\]", line)
        if match is None:
            raise ValueError("incomplete axiom record")
        name, raw = match.groups()
        if name in records:
            raise ValueError("duplicate axiom record")
        axioms = [part.strip() for part in raw.split(",") if part.strip()]
        if not set(axioms) <= ALLOWED:
            raise ValueError("forbidden axiom")
        records[name] = axioms
    if set(records) != anchors:
        raise ValueError("selected records do not match the journal anchors")
    return records


class M05AcceptedAxiomTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        folder = ROOT / "docs/rebel"
        cls.text = (folder / "M05-accepted-axioms.txt").read_text(encoding="utf-8")
        journal = json.loads((folder / "coverage-updates/M05.json").read_text(encoding="utf-8"))
        cls.anchors = {proof["declaration"] for row in journal["updates"]
                       for proof in row["evidence"]}

    def test_all_journal_anchors_have_complete_compiler_records(self):
        self.assertEqual(len(self.anchors), 31)
        self.assertEqual(len(validate_excerpt(self.text, self.anchors)), 31)

    def test_missing_anchor_is_rejected(self):
        lines = self.text.splitlines()
        first = next(line for line in lines if line.startswith("REBEL_AXIOMS "))
        with self.assertRaisesRegex(ValueError, "journal anchors"):
            validate_excerpt(self.text.replace(first + "\n", "", 1), self.anchors)

    def test_forbidden_axiom_is_rejected(self):
        forged = self.text.replace("[propext, Classical.choice, Quot.sound]",
                                   "[propext, Classical.choice, Quot.sound, sorryAx]", 1)
        with self.assertRaisesRegex(ValueError, "forbidden axiom"):
            validate_excerpt(forged, self.anchors)

    def test_wrong_source_duplicate_and_missing_marker_are_rejected(self):
        record = next(line for line in self.text.splitlines() if line.startswith("REBEL_AXIOMS "))
        bad_cases = [self.text.replace(SOURCE, "0" * 40), self.text + record + "\n",
                     self.text.replace("REBEL_VALIDATION_PASS modules=105\n", "")]
        for bad in bad_cases:
            with self.subTest(case=bad[-100:]), self.assertRaises(ValueError):
                validate_excerpt(bad, self.anchors)


if __name__ == "__main__":
    unittest.main()
