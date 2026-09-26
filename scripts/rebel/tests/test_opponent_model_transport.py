"""Exact finite-kernel controls; these tests do not replace Lean validation."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import unittest

ROOT = Path(__file__).resolve().parents[3]


def bind(law, kernel):
    return tuple(sum((law[x] * kernel[x][y] for x in range(len(law))), F(0))
                 for y in range(len(kernel[0])))


def variation(first, second):
    return sum((abs(x - y) for x, y in zip(first, second)), F(0))


def run(law, kernel, fuel):
    for _ in range(fuel):
        law = bind(law, kernel)
    return law


def charge(actual, first, second, fuel):
    result = F(0)
    for _ in range(fuel):
        result += sum((p * variation(first[x], second[x])
                       for x, p in enumerate(actual)), F(0))
        actual = bind(actual, first)
    return result


def support_loss(actual, model):
    """Actual probability of atoms absent from the model; not total variation."""
    return sum((p for p, q in zip(actual, model) if q == 0), F(0))


def support_charge(actual, first, second, fuel):
    result = F(0)
    for _ in range(fuel):
        result += sum((p * support_loss(first[x], second[x])
                       for x, p in enumerate(actual)), F(0))
        actual = bind(actual, first)
    return result


class OpponentModelTransportControls(unittest.TestCase):
    def test_kernel_transport_and_actual_prefix_hybrid_bound(self):
        laws = tuple((p, 1 - p) for p in (F(0), F(1, 4), F(1, 2), F(1)))
        kernels = tuple(product(laws, repeat=2))
        cases = 0
        for actual, model in product(laws, repeat=2):
            for first, second in product(kernels, repeat=2):
                for fuel in (0, 1, 2, 3):
                    error = variation(run(actual, first, fuel), run(model, second, fuel))
                    bound = variation(actual, model) + charge(actual, first, second, fuel)
                    self.assertLessEqual(error, bound)
                    cases += 1
        self.assertEqual(cases, 16384)

    def test_model_prefix_weight_is_unsound(self):
        actual, model = (F(1, 4), F(3, 4)), (F(0), F(1))
        retain, collapse = ((F(1), F(0)), (F(0), F(1))), ((F(0), F(1)),) * 2
        error = variation(bind(actual, retain), bind(actual, collapse))
        self.assertEqual(error, F(1, 2))
        self.assertEqual(charge(actual, retain, collapse, 1), error)
        self.assertEqual(charge(model, retain, collapse, 1), 0)
        self.assertGreater(error, charge(model, retain, collapse, 1))

    def test_zero_fuel_retains_initial_mismatch(self):
        actual, model = (F(1, 4), F(3, 4)), (F(0), F(1))
        retain = ((F(1), F(0)), (F(0), F(1)))
        self.assertEqual(charge(actual, retain, retain, 0), 0)
        self.assertEqual(variation(run(actual, retain, 0), run(model, retain, 0)), F(1, 2))

    def test_lost_support_is_not_a_zero_error_posterior(self):
        actual, model = (F(1, 4), F(3, 4)), (F(0), F(1))
        lost = sum((p for p, q in zip(actual, model) if q == 0), F(0))
        self.assertEqual(lost, F(1, 4))
        self.assertLessEqual(lost, variation(actual, model))
        self.assertEqual(model[0], 0)  # no model normalization at observation zero

    def test_matching_and_absorbed_models_have_zero_kernel_charge(self):
        first = ((F(1, 2), F(1, 2)), (F(0), F(1)))
        second = ((F(0), F(1)), (F(0), F(1)))
        law = (F(1, 4), F(3, 4))
        for fuel in (0, 1, 2, 8):
            self.assertEqual(charge(law, first, first, fuel), 0)
            self.assertEqual(charge((F(0), F(1)), first, second, fuel), 0)

    def test_support_rate_and_comparison_to_full_source_charge(self):
        laws = tuple((p, 1 - p) for p in (F(0), F(1, 4), F(1, 2), F(1)))
        kernels = tuple(product(laws, repeat=2))
        cases = 0
        for actual, model in product(laws, repeat=2):
            for first, second in product(kernels, repeat=2):
                for fuel in (0, 1, 2, 3):
                    lost = support_loss(run(actual, first, fuel), run(model, second, fuel))
                    allowance = support_loss(actual, model) + support_charge(
                        actual, first, second, fuel)
                    old_allowance = variation(actual, model) + charge(actual, first, second, fuel)
                    self.assertLessEqual(lost, allowance)
                    self.assertLessEqual(allowance, old_allowance)
                    cases += 1
        self.assertEqual(cases, 16384)

    def test_support_dominance_does_not_require_equal_laws_or_profiles(self):
        actual, model = (F(1, 4), F(3, 4)), (F(1, 2), F(1, 2))
        first = ((F(1), F(0)), (F(1, 4), F(3, 4)))
        second = ((F(1, 2), F(1, 2)),) * 2
        self.assertGreater(variation(actual, model), 0)
        self.assertNotEqual(first, second)
        for fuel in (0, 1, 2, 8):
            self.assertEqual(support_loss(actual, model), 0)
            self.assertEqual(support_charge(actual, first, second, fuel), 0)
            self.assertEqual(support_loss(run(actual, first, fuel), run(model, second, fuel)), 0)

    def test_support_rate_keeps_zero_fuel_incoming_defect(self):
        actual, model = (F(1, 4), F(3, 4)), (F(0), F(1))
        retain = ((F(1), F(0)), (F(0), F(1)))
        self.assertEqual(support_charge(actual, retain, retain, 0), 0)
        self.assertEqual(support_loss(run(actual, retain, 0), run(model, retain, 0)), F(1, 4))
        self.assertGreater(support_loss(actual, model), support_charge(actual, retain, retain, 0))

    def test_model_prefix_undercharges_support_leakage(self):
        actual, model = (F(1, 4), F(3, 4)), (F(0), F(1))
        retain, collapse = ((F(1), F(0)), (F(0), F(1))), ((F(0), F(1)),) * 2
        self.assertEqual(support_charge(actual, retain, collapse, 1), F(1, 4))
        self.assertEqual(support_charge(model, retain, collapse, 1), 0)
        self.assertGreater(support_loss(bind(actual, retain), bind(actual, collapse)),
                           support_charge(model, retain, collapse, 1))

    def test_support_rate_includes_rare_and_impossible_model_outcomes(self):
        retain, collapse = ((F(1), F(0)), (F(0), F(1))), ((F(0), F(1)),) * 2
        for rare in (F(0), F(1, 1000003), F(1, 8), F(1)):
            actual = (rare, 1 - rare)
            self.assertEqual(support_loss(bind(actual, retain), bind(actual, collapse)), rare)
            self.assertEqual(support_charge(actual, retain, collapse, 1), rare)
            self.assertEqual(charge(actual, retain, collapse, 1), 2 * rare)

    def test_new_modules_reach_existing_validation_consumers(self):
        names = ("GameTheory.Math.Probability.FinDistKernelVariation",
                 "GameTheory.Analysis.ReBeL.PBSOpponentModelTransport",
                 "GameTheory.Analysis.ReBeL.Examples.PBSOpponentModelTransport")
        umbrella = (ROOT / "GameTheory/Analysis/ReBeL.lean").read_text()
        targets = (ROOT / "scripts/rebel/m06-targets.txt").read_text().split()
        spec = importlib.util.spec_from_file_location(
            "opponent_model_auditor", ROOT / "scripts/rebel/audit_exact_leaf.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        for name in names:
            self.assertIn("import " + name, umbrella)
            self.assertIn(name, targets)
            self.assertIn(name, module.MODULES)
            self.assertTrue((ROOT / (name.replace(".", "/") + ".lean")).is_file())


if __name__ == "__main__":
    unittest.main()
