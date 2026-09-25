"""Exact arithmetic checks for the scalar tail cutoff, not a Lean proof."""
from fractions import Fraction
from itertools import product
import unittest

F = Fraction


class ScalarTailControls(unittest.TestCase):
    def test_explicit_late_output_budget(self) -> None:
        checked = 0
        for coefficient, tolerance in product((F(0), F(1, 2), F(1), F(3)),
                                               (F(1, 8), F(1, 4), F(1))):
            half = tolerance / 2
            square = (abs(coefficient) / half) ** 2
            threshold = square.numerator // square.denominator + 1
            self.assertGreater(threshold, 0)
            for first, second in product((threshold, threshold + 1, threshold + 17), repeat=2):
                # Exact squared form of C/sqrt(t) <= tolerance/2 for positive t.
                self.assertLessEqual(coefficient ** 2, first * half ** 2)
                self.assertLessEqual(coefficient ** 2, second * half ** 2)
                checked += 1
        self.assertEqual(checked, 108)
        # An early iterate is not covered just because the chosen error is positive.
        self.assertGreater(F(3) ** 2, F(1) * (F(1, 8) / 2) ** 2)


if __name__ == '__main__':
    unittest.main()
