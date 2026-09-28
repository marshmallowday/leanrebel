"""Exact-rational controls for fixed-trace average convergence boundaries.

These are independent mathematical controls, not an execution of Lean CFR-D.
In particular the cycling profile sequence below is not claimed to be CFR.
"""
from fractions import Fraction as F
import unittest


def threshold(coefficient, epsilon):
    """The positive integer threshold, evaluated without floating-point roots."""
    ratio_squared = (abs(coefficient) / epsilon) ** 2
    return ratio_squared.numerator // ratio_squared.denominator + 1


def matching_pennies_gain(p, q):
    """Largest unilateral gain for independent mixed row/column strategies."""
    value = (2 * p - 1) * (2 * q - 1)
    return max(abs(2 * q - 1) - value, abs(2 * p - 1) + value)


class AverageLimitControls(unittest.TestCase):
    def test_all_later_counts_and_threshold_boundary(self):
        for coefficient in (F(0), F(1, 7), F(3, 2), F(-3, 2)):
            for epsilon in (F(1), F(1, 3), F(1, 101)):
                start = threshold(coefficient, epsilon)
                self.assertGreater(start, 0)
                for count in (start, start + 1, 2 * start, 100 * start):
                    self.assertLessEqual(coefficient ** 2, epsilon ** 2 * count)
        # A floor without the added positive step can miss the requested bound.
        self.assertGreater(F(3, 2) ** 2, F(1) ** 2 * 2)
        self.assertEqual(threshold(F(0), F(1, 101)), 1)

    def test_fixed_noise_and_child_loss_are_a_floor(self):
        numerical, child_loss, factor = F(1, 10), F(1, 20), F(3)
        floor = factor * numerical + 2 * child_loss
        self.assertEqual(floor, F(2, 5))
        for root_count in (1, 2, 10, 1000):
            # Square counts make the inverse-square-root term exact rational.
            finite_term = F(7, root_count)
            self.assertGreater(floor + finite_term, floor)
            self.assertGreater(floor + finite_term, F(1, 10))
        # Zero prediction error does not erase the independent finite-time term.
        self.assertGreater(F(0) + F(7, 1000), 0)
        self.assertGreater(2 * child_loss, numerical / 2)

    def test_average_not_final_iterate_or_monotone_gain(self):
        cycle = ((0, 0), (1, 1), (0, 1), (1, 0))
        row_total = col_total = 0
        gains = {}
        for count in range(1, 41):
            row, col = cycle[(count - 1) % len(cycle)]
            row_total += row
            col_total += col
            self.assertEqual(matching_pennies_gain(F(row), F(col)), 2)
            gain = matching_pennies_gain(F(row_total, count), F(col_total, count))
            self.assertLessEqual(gain, F(4, count))
            gains[count] = gain
            if count % 4 == 0:
                self.assertEqual(gain, 0)
        self.assertGreater(gains[5], gains[4])
        self.assertEqual(gains[40], 0)

    def test_fixed_trace_prefix_not_horizon_dependent_oracle(self):
        def train(rounds, oracle):
            state, trace = F(0), []
            for index in range(rounds):
                prediction = oracle(index, state)
                state = (state + prediction) / 2
                trace.append((prediction, state))
            return trace

        fixed_oracle = lambda index, state: F((-1) ** index, index + 1) + state / 3
        short = train(4, fixed_oracle)
        long = train(12, fixed_oracle)
        self.assertEqual(short, long[:4])
        self.assertNotEqual(
            train(4, lambda index, state: F(1, 4)),
            train(12, lambda index, state: F(1, 12))[:4],
        )

    def test_recursive_parent_keeps_tail_allocation(self):
        # Varying only the outer count must not silently tighten child solvers.
        coefficient, tolerance = F(5), F(1, 2)
        error = tolerance / (4 * (abs(coefficient) + 1))
        child = tolerance / 8
        floor = coefficient * error + 2 * child
        allocations = []
        counts = []
        for epsilon in (F(1, 2), F(1, 10), F(1, 100)):
            allocations.append((error, child))
            counts.append(threshold(F(9), epsilon))
            self.assertLessEqual(F(9) ** 2, epsilon ** 2 * counts[-1])
            self.assertGreater(floor + epsilon, floor)
        self.assertEqual(len(set(allocations)), 1)
        self.assertEqual(counts, sorted(counts))
        self.assertLess(floor, tolerance)
        self.assertGreater(floor, 0)
        retuned = F(1, 100) / 8
        self.assertNotEqual(child, retuned)


if __name__ == "__main__":
    unittest.main()
