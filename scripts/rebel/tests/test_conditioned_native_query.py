"""Exact event-selection and audit-wiring controls; not kernel verification."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import unittest

ROOT = Path(__file__).resolve().parents[3]


def selected_tags(prior, kernel, event):
    """Retain tags through a stochastic kernel, then condition a possible event."""
    joint = {(a, b): p * q for a, p in prior.items() for b, q in kernel[a].items()}
    mass = sum((p for point, p in joint.items() if point in event), F(0))
    if mass == 0:
        raise ValueError("Impossible event has no conditional query")
    query = {a: sum((p for (tag, b), p in joint.items()
                     if tag == a and (tag, b) in event), F(0)) / mass for a in prior}
    return mass, query


class ConditionedNativeQueryControls(unittest.TestCase):
    def test_correlated_selection_is_sharp(self):
        prior = {pair: F(1, 4) for pair in product(range(2), repeat=2)}
        kernel = {pair: {pair[1]: F(1)} for pair in prior}
        event = {(pair, pair[1]) for pair in prior if pair[0] == pair[1]}
        mass, query = selected_tags(prior, kernel, event)
        loss = {pair: F(pair[0] == pair[1]) for pair in prior}
        before = sum((p * loss[pair] for pair, p in prior.items()), F(0))
        after = sum((p * loss[pair] for pair, p in query.items()), F(0))
        self.assertEqual((mass, before, after), (F(1, 2), F(1, 2), F(1)))
        self.assertEqual(after, before / mass)
        self.assertGreater(after, before)
        for axis in (0, 1):
            for value in (0, 1):
                self.assertEqual(sum(p for pair, p in query.items() if pair[axis] == value),
                                 F(1, 2))

    def test_kernel_events_support_density_and_nonnegative_error(self):
        atoms = (0, 1)
        outcomes = (0, 1)
        grid = (F(0), F(1, 4), F(1, 2), F(1))
        cases = 0
        for p, a, b in product(grid, repeat=3):
            prior = {0: p, 1: 1 - p}
            kernel = {0: {0: a, 1: 1 - a}, 1: {0: b, 1: 1 - b}}
            for flags in product((False, True), repeat=4):
                event = {point for point, take in zip(product(atoms, outcomes), flags) if take}
                try:
                    mass, query = selected_tags(prior, kernel, event)
                except ValueError:
                    continue
                self.assertEqual(sum(query.values()), 1)
                for tag in atoms:
                    if prior[tag] == 0:
                        self.assertEqual(query[tag], 0)
                    else:
                        self.assertLessEqual(query[tag] / prior[tag], 1 / mass)
                for x, y in product((F(0), F(1, 2), F(3)), repeat=2):
                    before = prior[0] * x + prior[1] * y
                    after = query[0] * x + query[1] * y
                    self.assertLessEqual(after, before / mass)
                    self.assertLessEqual(mass * after, before)
                cases += 1
        self.assertGreater(cases, 500)

    def test_impossible_events_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "Impossible"):
            selected_tags({0: F(1)}, {0: {0: F(1)}}, set())
        with self.assertRaisesRegex(ValueError, "Impossible"):
            selected_tags({0: F(1), 1: F(0)}, {0: {0: F(1)}, 1: {1: F(1)}}, {(1, 1)})

    def test_nonnegativity_cannot_be_dropped(self):
        prior = {0: F(1, 2), 1: F(1, 2)}
        mass, query = selected_tags(prior, {0: {0: F(1)}, 1: {1: F(1)}}, {(0, 0)})
        signed_before = prior[0] - prior[1]
        signed_after = query[0] - query[1]
        self.assertGreater(signed_after, signed_before / mass)

    def test_new_modules_reach_all_validation_consumers(self):
        names = ("GameTheory.Math.Probability.FinDistSelection",
                 "GameTheory.Analysis.ReBeL.PBSConditionedNativeGap",
                 "GameTheory.Analysis.ReBeL.Examples.PBSConditionedNativeGap")
        umbrella = (ROOT / "GameTheory/Analysis/ReBeL.lean").read_text()
        targets = (ROOT / "scripts/rebel/m06-targets.txt").read_text().split()
        spec = importlib.util.spec_from_file_location(
            "conditioned_query_auditor", ROOT / "scripts/rebel/audit_exact_leaf.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        for name in names:
            self.assertIn("import " + name, umbrella)
            self.assertIn(name, targets)
            self.assertIn(name, module.MODULES)
            self.assertTrue((ROOT / (name.replace(".", "/") + ".lean")).is_file())


if __name__ == "__main__":
    unittest.main()
