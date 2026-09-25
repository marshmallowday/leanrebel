"""Exact finite-law diagnostics, not Lean or actual CFR-iterate validation."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import unittest

ROOT = Path(__file__).resolve().parents[3]


def expectation(law, value):
    return sum((p * value[x] for x, p in law.items()), F(0))


def product_law(seed, own):
    return {(n, x): a * b for n, a in seed.items() for x, b in own.items()}


def tagged_law(seed, query):
    return {(n, x): a * b for n, a in seed.items() for x, b in query[n].items()}


def joint_density(reference, actual):
    """Reject unsupported mass, and give density zero on unused zero atoms."""
    result = {}
    for atom in reference.keys() | actual.keys():
        p, q = reference.get(atom, F(0)), actual.get(atom, F(0))
        if p == 0 and q != 0:
            raise ValueError("Actual law has mass outside reference support")
        result[atom] = q / p if p else F(0)
    return result


class JointNativeQueryControls(unittest.TestCase):
    def test_correlated_density_and_sharp_bound(self):
        seed = {0: F(1, 2), 1: F(1, 2)}
        reference = product_law(seed, seed)
        actual = tagged_law(seed, {n: {0: F(n == 0), 1: F(n == 1)} for n in seed})
        loss = {atom: F(atom[0] == atom[1]) for atom in reference}
        ratio = joint_density(reference, actual)
        self.assertEqual(max(ratio.values()), 2)
        self.assertEqual(expectation(reference, loss), F(1, 2))
        self.assertEqual(expectation(actual, loss), 1)
        self.assertGreater(expectation(actual, loss), expectation(reference, loss))
        for axis in (0, 1):
            marginal = {n: sum((p for atom, p in actual.items() if atom[axis] == n), F(0))
                        for n in seed}
            self.assertEqual(marginal, seed)

    def test_all_small_seed_dependent_kernels(self):
        seed = {0: F(1, 2), 1: F(1, 2)}
        grid = [F(0), F(1, 4), F(1, 2), F(3, 4), F(1)]
        losses = list(product([F(0), F(1, 2), F(1), F(3)], repeat=4))
        checked = 0
        for p in grid[1:-1]:
            own = {0: p, 1: 1 - p}
            reference = product_law(seed, own)
            atoms = list(reference)
            for a, b in product(grid, repeat=2):
                query = {0: {0: a, 1: 1 - a}, 1: {0: b, 1: 1 - b}}
                actual = tagged_law(seed, query)
                ratio = joint_density(reference, actual)
                factor = max(ratio.values())
                self.assertEqual(sum(actual.values()), 1)
                for values in losses:
                    loss = dict(zip(atoms, values))
                    weighted = {atom: ratio[atom] * loss[atom] for atom in atoms}
                    self.assertEqual(expectation(actual, loss), expectation(reference, weighted))
                    self.assertLessEqual(expectation(actual, loss),
                                         factor * expectation(reference, loss))
                    checked += 1
        self.assertEqual(checked, 19200)

    def test_absent_type_mass_is_rejected(self):
        seed = {0: F(1, 2), 1: F(1, 2)}
        reference = product_law(seed, {0: F(1), 1: F(0)})
        with self.assertRaises(ValueError):
            joint_density(reference, {(0, 1): F(1)})
        self.assertEqual(joint_density(reference, reference)[(0, 1)], 0)

    def test_all_new_modules_reach_both_auditors(self):
        names = ["GameTheory.Analysis.ReBeL." + suffix for suffix in (
            "PBSNativeConditionalGap", "Examples.PBSNativeConditionalGap",
            "PBSJointNativeGap", "Examples.PBSJointNativeGap")]
        umbrella = (ROOT / "GameTheory/Analysis/ReBeL.lean").read_text()
        targets = (ROOT / "scripts/rebel/m06-targets.txt").read_text().split()
        spec = importlib.util.spec_from_file_location(
            "joint_query_auditor", ROOT / "scripts/rebel/audit_exact_leaf.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        for name in names:
            self.assertIn("import " + name, umbrella)
            self.assertIn(name, targets)
            self.assertIn(name, module.MODULES)
            self.assertTrue((ROOT / (name.replace(".", "/") + ".lean")).is_file())


if __name__ == "__main__":
    unittest.main()
