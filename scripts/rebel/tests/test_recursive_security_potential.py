"""Independent Fraction controls for opponent-uniform security potentials.

These finite games and native-memory analogues are not runs of Lean or CFR.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def mix(p):
    return (1 - p, p)


def expectation(weights, values):
    return sum((w * x for w, x in zip(weights, values)), F(0))


def value(matrix, row, column):
    return sum((mix(row)[i] * mix(column)[j] * matrix[i][j]
                for i, j in product(range(2), repeat=2)), F(0))


def nash_error(matrix, row, column):
    center = value(matrix, row, column)
    return max(F(0), *(value(matrix, r, column) - center for r in (0, 1)),
               *(center - value(matrix, row, c) for c in (0, 1)))


class RecursiveSecurityPotentialTests(unittest.TestCase):
    def test_both_players_secure_model_value_against_arbitrary_opponents(self):
        matrices = (((1, -1), (-1, 1)), ((2, -1), (0, 1)),
                    ((-2, 1), (2, -1)))
        grid = (F(0), F(1, 3), F(1))
        for matrix, row, column, unknown in product(matrices, grid, grid, grid):
            center = value(matrix, row, column)
            error = nash_error(matrix, row, column)
            cross0 = value(matrix, row, unknown)
            cross1 = -value(matrix, unknown, column)
            self.assertLessEqual(center - error, cross0)
            self.assertLessEqual(-center - error, cross1)
            # A private pure-policy draw has the same value against a fixed foe.
            self.assertEqual(cross0, expectation(mix(row),
                [value(matrix, r, unknown) for r in (0, 1)]))
            self.assertEqual(cross1, expectation(mix(column),
                [-value(matrix, unknown, c) for c in (0, 1)]))

    def test_one_root_charge_and_old_surplus_are_separate(self):
        roots = (F(1, 100), F(1, 2), F(99, 100))
        matrices = (((2, -1), (0, 1)), ((-2, 1), (2, -1)))
        for actual_p, model_p, row, column, old, unknown in product(
                roots, roots, (F(1, 3), F(2, 3)), (F(1, 2),),
                (F(0), F(1)), (F(0), F(1))):
            actual, model = mix(actual_p), mix(model_p)
            averaged = tuple(tuple(expectation(model, [m[i][j] for m in matrices])
                             for j in range(2)) for i in range(2))
            center = value(averaged, row, column)
            error = nash_error(averaged, row, column)
            old_value = expectation(actual, [value(m, old, unknown) for m in matrices])
            fresh_value = expectation(actual, [value(m, row, unknown) for m in matrices])
            root_charge = 2 * sum(abs(a - b) for a, b in zip(actual, model))
            self.assertLessEqual(center - error - root_charge, fresh_value)
            potential = old_value - center + root_charge
            self.assertLessEqual(old_value - fresh_value, error + potential)
        # Constant-in-actions state payoffs make the coefficient one sharp.
        model, actual = (F(1), F(0)), (F(0), F(1))
        bound = F(3)
        discrepancy = sum(abs(a - b) for a, b in zip(actual, model))
        self.assertEqual(expectation(model, [bound, -bound]) -
                         expectation(actual, [bound, -bound]), bound * discrepancy)
        self.assertGreater(expectation(model, [bound, -bound]),
                           expectation(actual, [bound, -bound]))

    def test_exact_nash_does_not_remove_signed_incumbent_surplus(self):
        matching = ((1, -1), (-1, 1))
        fresh, unknown = F(1, 2), F(0)
        center = value(matching, fresh, fresh)
        self.assertEqual(nash_error(matching, fresh, fresh), 0)
        self.assertEqual(value(matching, fresh, unknown), 0)
        for old, expected in ((F(0), F(1)), (F(1), F(-1))):
            surplus = value(matching, old, unknown) - center
            loss = value(matching, old, unknown) - value(matching, fresh, unknown)
            self.assertEqual(surplus, expected)
            self.assertEqual(loss, surplus)
        self.assertGreater(value(matching, 0, unknown) -
                           value(matching, fresh, unknown), 0)
        # Exact Nash can be far from the incumbent without unsafe new security.
        self.assertEqual(abs(F(0) - fresh), F(1, 2))

    def test_conditional_cells_keep_incumbent_and_model_correlations(self):
        for rare, within in product((F(1, 101), F(1, 3), F(3, 4)),
                                    (F(1, 5), F(1, 2), F(4, 5))):
            # key, hidden state, incumbent action; key fixes the whole incumbent.
            states = ((rare * within, 0, 0, 0),
                      (rare * (1 - within), 0, 1, 0),
                      ((1 - rare) * within, 1, 0, 1),
                      ((1 - rare) * (1 - within), 1, 1, 1))
            payoff = lambda h, old: F(1 if h == old else -1)
            direct = sum(w * payoff(h, old) for w, _, h, old in states)
            grouped = sum(weight * sum(w / weight * payoff(h, old)
                          for w, k, h, old in states if k == key)
                          for key, weight in ((0, rare), (1, 1 - rare)))
            self.assertEqual(direct, grouped)
            self.assertEqual(sum(w for w, _, _, _ in states), 1)
        # Hidden state and incumbent perfectly correlate; product marginals fail.
        joint = ((F(1, 2), 0, 0), (F(1, 2), 1, 1))
        self.assertEqual(sum(w * payoff(h, old) for w, h, old in joint), 1)
        erased = sum(F(1, 4) * payoff(h, old) for h, old in product(range(2), repeat=2))
        self.assertEqual(erased, 0)
        # Unsupported actual mass is not discarded by a model-root argument.
        for mass in (F(1, 100), F(1, 4), F(3, 4)):
            bound = F(2)
            self.assertEqual(mass * (bound - (-bound)), 2 * bound * mass)
        # An uncertified cell keeps its signed cost, even when negative.
        self.assertEqual(expectation([F(1, 4), F(3, 4)], [F(-2), F(1)]), F(1, 4))

    def test_native_forward_weights_late_draw_and_parent_terms(self):
        grid = (F(1, 5), F(1, 2), F(4, 5))
        for prior, first_rate, second_rate in product(grid, repeat=3):
            law = {(h, h): w for h, w in enumerate(mix(prior))}
            total = F(0)
            start = sum(w * (2 * h - draw) for (h, draw), w in law.items())
            for rate in (first_rate, second_rate):
                next_law = {}
                before = sum(w * (2 * h - draw) for (h, draw), w in law.items())
                for (h, draw), weight in law.items():
                    for new_draw, chance in enumerate(mix(rate)):
                        state = (h, new_draw)
                        next_law[state] = next_law.get(state, F(0)) + weight * chance
                after = sum(w * (2 * h - draw) for (h, draw), w in next_law.items())
                total += before - after
                law = next_law
            final = sum(w * (2 * h - draw) for (h, draw), w in law.items())
            self.assertEqual(start - final, total)
            self.assertEqual(sum(law.values()), 1)
        # One private draw controls both stage and late action.
        for p in grid:
            same_draw_equal = F(1)
            redraw_equal = p * p + (1 - p) * (1 - p)
            self.assertGreater(same_draw_equal, redraw_equal)
        for error, root_count, loss in product((F(0), F(1, 8)), (1, 2, 4),
                                                (F(0), F(1, 4))):
            # t=root_count^2; constants are fixed independently of error and t.
            allowance = 3 * error + F(2, root_count) + 2 * loss
            self.assertGreater(allowance, 0)
            if error == 0:
                self.assertEqual(allowance, F(2, root_count) + 2 * loss)
        self.assertEqual(sum([], F(0)), 0)


if __name__ == "__main__":
    unittest.main()
