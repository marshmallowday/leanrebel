"""M05 proof-surface regressions; actual Lean/lint/axiom gates remain mandatory."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/rebel"))
from audit_axioms import proof_modules

PREFIX = "GameTheory.Analysis.ReBeL."
REQUIRED = {
    "BeliefExistence", "PBSInfoValue", "PBSValue", "PBSOptimality", "PBSGeometry",
    "PBSFullAOH", "PBSTheorem1", "ValueDifferential", "Examples.ValuePBS",
    "Examples.ValueRadial", "Examples.ValueKink", "Examples.ValueGeometry",
}


class M05ProofSurfaceTests(unittest.TestCase):
    def test_canonical_pbs_and_adversarial_examples_reach_the_real_audit(self):
        modules = set(proof_modules())
        umbrella = (ROOT / "GameTheory/Analysis/ReBeL.lean").read_text(encoding="utf-8")
        for name in sorted(REQUIRED):
            module = PREFIX + name
            with self.subTest(module=module):
                self.assertIn(module, modules)
                self.assertIn("import " + module, umbrella)
                self.assertTrue((ROOT / (module.replace(".", "/") + ".lean")).is_file())

    def test_full_aoh_entry_point_and_actual_joint_game_are_present(self):
        base = ROOT / "GameTheory/Analysis/ReBeL"
        theorem = (base / "PBSTheorem1.lean").read_text(encoding="utf-8")
        example = (base / "Examples/ValuePBS.lean").read_text(encoding="utf-8")
        for name in ("theorem1_fullAOH", "fullAOHBeliefSlice", "IsNash", "ConcaveOn"):
            self.assertIn(name, theorem)
        for name in ("twoStage_joint_theorem1", "valueSlice_preserves_joint",
                     "valueSlice_correlation_control", "theorem1_fullAOH"):
            self.assertIn(name, example)

    def test_counterexamples_remain_distinct_from_corrected_extension(self):
        base = ROOT / "GameTheory/Analysis/ReBeL/Examples"
        radial = (base / "ValueRadial.lean").read_text(encoding="utf-8")
        for name in ("radialValue_hasFDerivAt", "radial_gradient_not_supporting",
                     "radialValue_not_concave", "zero_mass_type_control", "corrected_support",
                     "normal_shift_annihilates_tangent", "radialValue_changes_along_simplex_normal"):
            self.assertIn("theorem " + name, radial)
        kink = (base / "ValueKink.lean").read_text(encoding="utf-8")
        for name in ("value_not_differentiable", "both_equilibrium_opponents",
                     "distinct_centered_vectors", "arbitrary_linear_combination_not_supporting"):
            self.assertIn("theorem " + name, kink)
        coin = (base / "ValueGeometry.lean").read_text(encoding="utf-8")
        for name in ("coinSimplexValue_eq", "coinSimplexValue_not_differentiable",
                     "coin_nonunique_opponents", "coin_midpoint_support"):
            self.assertIn("theorem " + name, coin)

    def test_semantic_review_keeps_domain_and_quantifier_qualifications(self):
        review = (ROOT / "docs/rebel/M05.md").read_text(encoding="utf-8")
        for phrase in ("conditional-law slice", "not asserted to be uniquely determined",
                       "BASE", "No single universal extension", "fixed", "refuted"):
            self.assertIn(phrase, review)


if __name__ == "__main__":
    unittest.main()
