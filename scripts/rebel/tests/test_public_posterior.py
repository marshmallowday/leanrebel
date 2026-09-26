"""Exact finite-law public projection controls; not Lean compiler evidence."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import unittest

ROOT = Path(__file__).resolve().parents[3]


def pushforward(law, project):
    """Keep all projected atoms, including explicit zero masses."""
    result = {}
    for point, mass in law.items():
        image = project(point)
        result[image] = result.get(image, F(0)) + mass
    return result


def condition(law, event):
    mass = sum((p for point, p in law.items() if point in event), F(0))
    if mass == 0:
        raise ValueError("Impossible event")
    return mass, {point: p / mass if point in event else F(0)
                  for point, p in law.items()}


class PublicPosteriorControls(unittest.TestCase):
    def test_noninjective_projection_commutes_with_public_conditioning(self):
        cases = 0
        atoms = tuple(product(range(2), repeat=2))
        for weights in product((0, 1, 2), repeat=4):
            total = sum(weights)
            if not total:
                continue
            law = {point: F(weight, total) for point, weight in zip(atoms, weights)}
            image = pushforward(law, lambda point: point[1])
            for flags in product((False, True), repeat=2):
                event = {point for point, selected in enumerate(flags) if selected}
                preimage = {point for point in atoms if point[1] in event}
                if not sum(image[y] for y in event):
                    with self.assertRaisesRegex(ValueError, "Impossible"):
                        condition(law, preimage)
                    continue
                old_mass, selected = condition(law, preimage)
                new_mass, posterior = condition(image, event)
                self.assertEqual(old_mass, new_mass)
                self.assertEqual(pushforward(selected, lambda point: point[1]), posterior)
                cases += 1
        self.assertGreater(cases, 150)

    def test_nontrivial_public_output_mass_and_posterior(self):
        tags = tuple(product(range(2), repeat=2))
        execution = {(tag, tag[1]): F(1, 4) for tag in tags}
        mass, selected = condition(execution, {p for p in execution if p[1] == 0})
        self.assertEqual(mass, F(1, 2))
        self.assertEqual(pushforward(selected, lambda p: p[1]), {0: F(1), 1: F(0)})
        self.assertEqual(pushforward(execution, lambda p: p[1]), {0: F(1, 2), 1: F(1, 2)})

    def test_hidden_selection_is_not_a_public_update(self):
        law = {0: F(1, 2), 1: F(1, 2)}
        _, hidden = condition(law, {0})
        _, public = condition(law, set(law))  # the sole possible constant public event
        self.assertNotEqual(hidden, public)
        for event in (set(), {None}):
            self.assertNotEqual({0}, {x for x in law if None in event})

    def test_absent_visible_atom_is_not_a_posterior(self):
        law = {(0, 0): F(1), (1, 1): F(0)}
        with self.assertRaisesRegex(ValueError, "Impossible"):
            condition(law, {(1, 1)})
        with self.assertRaisesRegex(ValueError, "Impossible"):
            condition(pushforward(law, lambda p: p[1]), {1})

    def test_extended_modules_reach_unchanged_validation_gates(self):
        names = ("GameTheory.Math.Probability.FinDistSelection",
                 "GameTheory.Analysis.ReBeL.PBSConditionedNativeGap",
                 "GameTheory.Analysis.ReBeL.Examples.PBSConditionedNativeGap")
        umbrella = (ROOT / "GameTheory/Analysis/ReBeL.lean").read_text()
        targets = (ROOT / "scripts/rebel/m06-targets.txt").read_text().split()
        spec = importlib.util.spec_from_file_location(
            "public_posterior_auditor", ROOT / "scripts/rebel/audit_exact_leaf.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        for name in names:
            self.assertIn("import " + name, umbrella)
            self.assertIn(name, targets)
            self.assertIn(name, module.MODULES)
            self.assertTrue((ROOT / (name.replace(".", "/") + ".lean")).is_file())


if __name__ == "__main__":
    unittest.main()
