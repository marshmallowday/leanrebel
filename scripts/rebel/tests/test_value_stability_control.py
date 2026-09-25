"""Exact rational controls, not Lean compilation or a proof of ReBeL safety."""
from __future__ import annotations

from fractions import Fraction
from itertools import product
import unittest

F = Fraction
Matrix = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]
Profile = tuple[Fraction, Fraction]


def payoff(matrix: Matrix, profile: Profile) -> Fraction:
    """Independent mixed row and column laws in a two-player zero-sum table."""
    row, column = profile
    return sum((r * c * matrix[i][j]
                for i, r in enumerate((row, 1 - row))
                for j, c in enumerate((column, 1 - column))), F(0))


def error(matrix: Matrix, profile: Profile) -> Fraction:
    """Smallest common unilateral-gain allowance, computed by pure responses."""
    row, column = profile
    current = payoff(matrix, profile)
    return max(F(0), *(payoff(matrix, (r, column)) - current for r in (F(0), F(1))),
               *(current - payoff(matrix, (row, c)) for c in (F(0), F(1))))


class ValueStabilityControls(unittest.TestCase):
    def test_all_small_zero_sum_tables(self) -> None:
        profiles = tuple(product((F(0), F(1, 2), F(1)), repeat=2))
        checked = 0
        for entries in product((F(-1), F(0), F(1)), repeat=4):
            matrix: Matrix = ((entries[0], entries[1]), (entries[2], entries[3]))
            for first, second in product(profiles, repeat=2):
                self.assertLessEqual(abs(payoff(matrix, first) - payoff(matrix, second)),
                                     error(matrix, first) + error(matrix, second))
                checked += 1
        self.assertEqual(checked, 6561)

    def test_mean_preserving_spread_cost(self) -> None:
        values = (F(0), F(-1), F(1))
        old = (F(1), F(0), F(0))
        fresh = (F(0), F(1, 2), F(1, 2))
        self.assertEqual(sum(p * v for p, v in zip(old, values)), F(0))
        self.assertEqual(sum(p * v for p, v in zip(fresh, values)), F(0))
        # Nonnegative rows with zero old mass must be zero: this is the ONLY
        # possible coupling with these marginals, not an arbitrary bad choice.
        joint = (fresh, (F(0), F(0), F(0)), (F(0), F(0), F(0)))
        self.assertEqual(tuple(sum(row) for row in joint), old)
        self.assertEqual(tuple(sum(joint[i][j] for i in range(3)) for j in range(3)), fresh)
        cost = sum(joint[i][j] * max(F(0), values[j] - values[i])
                   for i in range(3) for j in range(3))
        self.assertEqual(cost, F(1, 2))

    def test_spread_game_is_exact_zero_sum_nash(self) -> None:
        # Both row choices have expected payoff zero; the column is irrelevant.
        matrix: Matrix = ((F(0), F(0)), (F(0), F(0)))
        for profile in product((F(0), F(1, 2), F(1)), repeat=2):
            self.assertEqual(error(matrix, profile), F(0))

    def test_common_game_is_necessary(self) -> None:
        first: Matrix = ((F(0), F(0)), (F(0), F(0)))
        second: Matrix = ((F(1), F(1)), (F(1), F(1)))
        p = (F(1, 2), F(1, 2))
        self.assertEqual(error(first, p) + error(second, p), F(0))
        self.assertEqual(abs(payoff(first, p) - payoff(second, p)), F(1))

    def test_zero_sum_is_necessary(self) -> None:
        # Coordination, NOT zero sum: both players get the listed payoff.
        utility = ((F(1), F(0)), (F(0), F(2)))
        for action in (0, 1):
            incumbent = utility[action][action]
            self.assertTrue(all(utility[r][action] <= incumbent for r in (0, 1)))
            self.assertTrue(all(utility[action][c] <= incumbent for c in (0, 1)))
        self.assertNotEqual(utility[0][0], utility[1][1])

    def test_distinct_positive_budget_arithmetic(self) -> None:
        self.assertEqual(F(1, 4) + F(1, 8), F(3, 8))


if __name__ == '__main__':
    unittest.main()
