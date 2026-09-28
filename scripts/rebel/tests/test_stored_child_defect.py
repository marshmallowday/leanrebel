"""Rational controls for public/live posterior loss.

These enumerate finite probability identities and counterexamples. They do not
execute Lean or pretend that changing a solver input preserves its policy.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def conditional(law, event):
    mass = sum((p for x, p in law.items() if event(x)), F(0))
    return None if mass == 0 else {x: p / mass for x, p in law.items() if event(x) and p}


def mean(law, value):
    return sum((p * value(x) for x, p in law.items()), F(0))


def bind(law, kernel):
    output = {}
    for x, p in law.items():
        for y, q in kernel(x).items():
            output[y] = output.get(y, F(0)) + p * q
    return output


class StoredChildDefectControls(unittest.TestCase):
    def test_nested_conditioning_bound_and_signed_identity(self):
        # 36 correlated/rare-query cases, without an atom-mass floor.
        for public, live, skew in product(
                (F(1), F(1, 101), F(1, 1000000)),
                (F(1), F(1, 2), F(1, 1000)),
                (F(1, 7), F(2, 7), F(4, 7), F(6, 7))):
            law = {("seen", True, 0): public * live * skew,
                   ("seen", True, 1): public * live * (1 - skew),
                   ("seen", False, 2): public * (1 - live),
                   ("other", False, 3): 1 - public}
            saved = conditional(law, lambda x: x[0] == "seen")
            child = conditional(law, lambda x: x[0] == "seen" and x[1])
            value = lambda x: {0: F(-2), 1: F(1, 3), 2: F(2), 3: F(-1)}[x[2]]
            center = mean(child, value)
            discarded = sum((p for x, p in saved.items() if not x[1]), F(0))
            self.assertEqual(discarded, 1 - live)
            residual = mean(saved, lambda x: F(0) if x[1] else value(x) - center)
            self.assertEqual(mean(saved, value) - center, residual)
            self.assertLessEqual(abs(residual), 4 * discarded)
            self.assertEqual(set(child), {x for x in saved if x[1]})

    def test_two_bound_constant_is_tight_and_unscaled_mass_is_wrong(self):
        for public, live in product((F(1), F(1, 1000000)),
                                    (F(1, 4), F(1, 1000), F(999, 1000))):
            law = {("seen", True): public * live,
                   ("seen", False): public * (1 - live),
                   ("other", False): 1 - public}
            saved = conditional(law, lambda x: x[0] == "seen")
            child = conditional(law, lambda x: x[0] == "seen" and x[1])
            value = lambda x: F(-2) if x[1] else F(2)
            error = abs(mean(saved, value) - mean(child, value))
            self.assertEqual(error, 4 * (1 - live))
            self.assertGreater(error, 2 * (1 - live))
            if public < 1:
                self.assertGreater(error, 4 * public * (1 - live))

    def test_same_draw_through_late_kernel_and_value_cancellation(self):
        law = {(True, 0): F(1, 8), (True, 1): F(1, 8), (False, 2): F(3, 4)}
        child = conditional(law, lambda x: x[0])
        for draw_weight, late in product((F(1, 5), F(1, 2), F(4, 5)), (1, 2, 7)):
            def kernel(x):
                # Retain a single chosen draw throughout stage + late.
                return {(x, 0, late): draw_weight, (x, 1, late): 1 - draw_weight}
            value = lambda out: F(2) if out[1] == (out[0][1] % 2) else F(-2)
            first, second = bind(law, kernel), bind(child, kernel)
            self.assertLessEqual(abs(mean(first, value) - mean(second, value)), F(3))
            self.assertEqual(mean(first, lambda _: F(7)), mean(second, lambda _: F(7)))
        # Independent resampling destroys the stage/late correlation.
        retained = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
        redrawn = {pair: F(1, 4) for pair in product((0, 1), repeat=2)}
        equality_payoff = lambda pair: F(pair[0] == pair[1])
        self.assertEqual(mean(retained, equality_payoff), 1)
        self.assertEqual(mean(redrawn, equality_payoff), F(1, 2))

    def test_visibility_empty_child_and_missing_public_are_distinct(self):
        law = {("live", True): F(1, 5), ("dead", False): F(4, 5)}
        self.assertEqual(conditional(law, lambda x: x[0] == "live"),
                         conditional(law, lambda x: x[0] == "live" and x[1]))
        self.assertIsNotNone(conditional(law, lambda x: x[0] == "dead"))
        self.assertIsNone(conditional(law, lambda x: x[0] == "dead" and x[1]))
        self.assertIsNone(conditional(law, lambda x: x[0] == "absent"))
        # Zero remaining fuel creates no live child, even at a supported query.
        self.assertIsNone(conditional(law, lambda _: False))

    def test_posterior_error_does_not_bound_a_changed_solver_kernel(self):
        saved = {True: F(999, 1000), False: F(1, 1000)}
        child = {True: F(1)}
        # Discontinuous policy selection on the PBS is deliberately different.
        saved_kernel = lambda _: {F(2): F(1)}
        child_kernel = lambda _: {F(-2): F(1)}
        discrepancy = abs(mean(bind(saved, saved_kernel), lambda x: x) -
                          mean(bind(child, child_kernel), lambda x: x))
        self.assertEqual(discrepancy, 4)
        self.assertGreater(discrepancy, 4 * F(1, 1000))


if __name__ == "__main__":
    unittest.main()
