"""Exact arithmetic controls for the depth-native gap proof's boundary.

These do not execute Lean or assert equivalence to the depth-CFR implementation.
The Lean examples instantiate the real noisy solver; these independently check
sign, allocation, finite-time and actual-event selection calculations.
"""
from fractions import Fraction as Q
from itertools import product
import unittest


def mean(law, values):
    """Expectation of a finite rational table under an explicit normalized law."""
    if sum(law.values(), Q(0)) != 1 or any(p < 0 for p in law.values()):
        raise ValueError("not a probability law")
    return sum((p * values[x] for x, p in law.items()), Q(0))


def selected(law, values, event):
    """Return actual event mass and its conditional expectation."""
    mass = sum((p for x, p in law.items() if event(x)), Q(0))
    if not mass:
        raise ValueError("zero-probability event")
    return mass, sum((p * values[x] for x, p in law.items() if event(x)), Q(0)) / mass


class DepthNativeGap(unittest.TestCase):
    def test_nonnegative_draw_gap_mean(self):
        law = {0: Q(1, 3), 1: Q(2, 3)}
        values = {0: Q(-1, 2), 1: Q(3, 4)}
        best_response = Q(1)
        gaps = {n: best_response - v for n, v in values.items()}
        self.assertTrue(all(g >= 0 for g in gaps.values()))
        self.assertEqual(mean(law, {n: abs(g) for n, g in gaps.items()}),
                         abs(best_response - mean(law, values)))

    def test_signed_cancellation_is_not_gap_identity(self):
        law = {0: Q(1, 2), 1: Q(1, 2)}
        signed = {0: Q(-1), 1: Q(1)}
        self.assertEqual(abs(mean(law, signed)), 0)
        self.assertEqual(mean(law, {n: abs(v) for n, v in signed.items()}), 1)

    def test_actual_selection_is_sharp_and_correlates_tags(self):
        law = {(seed, typ): Q(1, 4) for seed, typ in product(range(2), repeat=2)}
        gaps = {pair: Q(1) if pair == (1, 1) else Q(0) for pair in law}
        event = lambda pair: pair[0] == pair[1]
        mass, conditional = selected(law, gaps, event)
        self.assertEqual(mass, Q(1, 2))
        self.assertEqual(conditional, mean(law, gaps) / mass)
        self.assertGreater(conditional, mean(law, gaps))
        self.assertNotEqual(conditional, Q(1, 4))  # re-productized uniform marginals

    def test_impossible_event_has_no_conditional_query(self):
        with self.assertRaises(ValueError):
            selected({0: Q(1)}, {0: Q(0)}, lambda _: False)

    def test_allocation_retains_noise_and_child_loss(self):
        for coefficient in (Q(-100), Q(0), Q(1, 3), Q(7), Q(100)):
            for tolerance in (Q(1, 1000), Q(1, 4), Q(3)):
                error = tolerance / (4 * (abs(coefficient) + 1))
                child_loss = tolerance / 8
                self.assertGreater(error / 2, 0)  # genuinely noisy predictor fixture
                self.assertGreater(child_loss, 0)
                self.assertLess(coefficient * error + 2 * child_loss, tolerance)

    def test_parent_rounds_cannot_erase_fixed_error(self):
        coefficient, error, child_loss = Q(3), Q(1, 8), Q(1, 16)
        floor = coefficient * error + 2 * child_loss
        self.assertEqual(floor, Q(1, 2))
        for root_t in (1, 2, 10, 1000):
            self.assertGreater(floor + Q(1, root_t), Q(1, 4))

    def test_zero_noise_still_has_finite_parent_residual(self):
        for root_t in (1, 2, 4, 100):
            residual = Q(3, root_t)  # exact square-root time for T=root_t**2
            self.assertGreater(residual, 0)
        self.assertEqual(Q(3, 2), Q(3) / 2)


if __name__ == "__main__":
    unittest.main()
