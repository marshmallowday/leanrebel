"""Independent finite controls for cross-query scalar value stability.

No function here runs CFR or the Lean solver. Policies are enumerated controls.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def mix(p):
    return (1 - p, p)


def mean(weights, values):
    return sum((w * v for w, v in zip(weights, values)), F(0))


def payoff(matrix, row, column):
    return sum((mix(row)[i] * mix(column)[j] * matrix[i][j]
                for i, j in product(range(2), repeat=2)), F(0))


def error(matrix, row, column):
    center = payoff(matrix, row, column)
    return max(F(0), *(payoff(matrix, r, column) - center for r in (0, 1)),
               *(center - payoff(matrix, row, c) for c in (0, 1)))


def average_game(matrices, roots):
    return tuple(tuple(mean(roots, [m[i][j] for m in matrices])
                       for j in range(2)) for i in range(2))


class RecursiveCrossQueryValueTests(unittest.TestCase):
    def test_independent_profiles_and_changed_roots(self):
        matrices = (((2, -1), (-2, 1)), ((-1, 2), (1, -2)))
        grid = (F(0), F(1, 2), F(1))
        roots = (F(1, 100), F(1, 2), F(99, 100))
        for a, b, r1, c1, r2, c2 in product(roots, roots, grid, grid, grid, grid):
            first = average_game(matrices, mix(a))
            second = average_game(matrices, mix(b))
            e1, e2 = error(first, r1, c1), error(second, r2, c2)
            v1, v2 = payoff(first, r1, c1), payoff(second, r2, c2)
            root_error = 2 * sum(abs(x - y) for x, y in zip(mix(a), mix(b)))
            for who in (0, 1):
                sign = 1 if who == 0 else -1
                self.assertLessEqual(abs(sign * (v1 - v2)), e1 + e2 + root_error)

    def test_public_live_recomputation_and_rare_denominator(self):
        matrices = (((2, -1), (-2, 1)), ((-1, 2), (1, -2)))
        for reach, live, r1, c1, r2, c2 in product(
                (F(1, 101), F(1, 3), F(1)), (F(1, 4), F(1, 2), F(1)),
                (F(0), F(1)), (F(1, 2),), (F(0), F(1)), (F(1, 2),)):
            public_game = average_game(matrices, (live, 1 - live))
            child_game = matrices[0]
            e1, e2 = error(public_game, r1, c1), error(child_game, r2, c2)
            stopped_mass = reach * (1 - live)
            gap = abs(payoff(public_game, r1, c1) - payoff(child_game, r2, c2))
            self.assertLessEqual(gap, e1 + e2 + 4 * stopped_mass / reach)
        # Constant-action exact equilibria attain the discarded-mass estimate.
        for reach, live in product((F(1, 101), F(1, 3)), (F(1, 4), F(3, 4))):
            public_value = live * (-2) + (1 - live) * 2
            child_value = F(-2)
            gap = abs(public_value - child_value)
            self.assertEqual(gap, 4 * (reach * (1 - live)) / reach)
            self.assertGreater(gap, 4 * reach * (1 - live))

    def test_scalar_agreement_is_not_policy_or_conditional_value_agreement(self):
        # Column is irrelevant; two row policies reverse the typewise payoff.
        matrices = (((1, 1), (-1, -1)), ((-1, -1), (1, 1)))
        game = average_game(matrices, (F(1, 2), F(1, 2)))
        self.assertEqual(error(game, 0, 0), 0)
        self.assertEqual(error(game, 1, 1), 0)
        self.assertEqual(payoff(game, 0, 0), payoff(game, 1, 1))
        self.assertEqual(abs(payoff(matrices[0], 0, 0) -
                             payoff(matrices[0], 1, 1)), 2)
        self.assertNotEqual(mix(F(0)), mix(F(1)))
        # A changed root makes an old equilibrium no longer an equilibrium.
        shifted = average_game(matrices, (F(3, 4), F(1, 4)))
        self.assertEqual(error(shifted, 1, 1), 1)
        self.assertEqual(error(shifted, 0, 0), 0)

    def test_private_security_keeps_both_solve_tolerances(self):
        matrices = (((2, -1), (0, 1)), ((-2, 1), (2, -1)))
        for a, b, r1, c1, r2, c2, opponent in product(
                (F(1, 10), F(9, 10)), (F(1, 3), F(2, 3)),
                (F(0), F(1)), (F(1, 2),), (F(1, 3), F(2, 3)),
                (F(1, 2),), (F(0), F(1))):
            first = average_game(matrices, mix(a))
            second = average_game(matrices, mix(b))
            v1 = payoff(first, r1, c1)
            e1, e2 = error(first, r1, c1), error(second, r2, c2)
            root_error = 2 * sum(abs(x - y) for x, y in zip(mix(a), mix(b)))
            private = mean(mix(r2), [payoff(second, pure, opponent) for pure in (0, 1)])
            self.assertEqual(private, payoff(second, r2, opponent))
            self.assertLessEqual(v1 - (e1 + 2 * e2 + root_error), private)
        matching = ((1, -1), (-1, 1))
        # An inaccurate new solve cannot inherit exact security with its error omitted.
        self.assertEqual(error(matching, F(1, 2), F(1, 2)), 0)
        self.assertLess(payoff(matching, 0, 1), 0)
        self.assertGreater(error(matching, 0, 0), 0)

    def test_horizon_and_joint_law_boundaries(self):
        # Action-independent terminal reward appears only after the late transition.
        before, after = F(0), F(2)
        self.assertGreater(abs(after - before), 0)
        # Both profiles are exact Nash on their own horizons; equal fuel is essential.
        for p in (F(1, 5), F(1, 2), F(4, 5)):
            same_draw_match = F(1)
            fresh_late_match = p * p + (1 - p) * (1 - p)
            self.assertGreater(same_draw_match, fresh_late_match)
        # Equal aggregate roots do not imply equality after conditioning on stored key.
        native = ((F(1, 2), 0, 0), (F(1, 2), 1, 1))
        joint_value = sum(w * (1 if key == h else -1) for w, key, h in native)
        erased_value = sum(F(1, 4) * (1 if key == h else -1)
                           for key, h in product(range(2), repeat=2))
        self.assertEqual(joint_value, 1)
        self.assertEqual(erased_value, 0)
        self.assertEqual(mean([F(1, 2), F(1, 2)], [F(0), F(1)]), F(1, 2))


if __name__ == "__main__":
    unittest.main()
