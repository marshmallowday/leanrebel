"""Exact arithmetic controls for R5's conditional recurrence (not game proofs)."""
from fractions import Fraction as Q
import random
import unittest


class ErrorRecurrenceTests(unittest.TestCase):
    def test_nonnegative_composition(self):
        rng = random.Random(20260917)
        for _ in range(100):
            delta = Q(rng.randrange(6), 5)
            inv_sqrt_t = Q(1, rng.randrange(1, 20))
            a, b, e = Q(0), Q(rng.randrange(6)), Q(0)
            e = b * inv_sqrt_t
            for _ in range(10):
                x, y, z = (Q(rng.randrange(6), 3) for _ in range(3))
                e = x * delta + y * inv_sqrt_t + z * e
                a, b = x + z * a, y + z * b
                self.assertEqual(e, a * delta + b * inv_sqrt_t)
                self.assertGreaterEqual(a, 0)
                self.assertGreaterEqual(b, 0)

    def test_zero_oracle_error_does_not_erase_iteration_term(self):
        delta, a, b, inv_sqrt_t = Q(0), Q(3), Q(2), Q(1, 4)
        candidate = a * delta + b * inv_sqrt_t
        printed = a * delta + delta * b * inv_sqrt_t
        self.assertEqual(candidate, Q(1, 2))
        self.assertEqual(printed, 0)
        self.assertGreater(candidate, printed)
        # A witness for a scalar recurrence is NOT a game counterexample.

    def test_zero_depth_and_zero_coefficients(self):
        delta, a, b, inv_sqrt_t = Q(4), Q(0), Q(0), Q(1)
        self.assertEqual(a * delta + b * inv_sqrt_t, 0)


if __name__ == "__main__":
    unittest.main()
