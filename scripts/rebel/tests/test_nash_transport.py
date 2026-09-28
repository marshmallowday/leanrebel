"""Exact finite controls for Nash replacement transport and horizon alignment.

These games and kernels are independent rational controls, not an execution
of the Lean recursive CFR implementation or a learned oracle.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def mean(law, value):
    return sum((p * value(x) for x, p in law.items()), F(0))


def variation(first, second):
    return sum((abs(first.get(x, 0) - second.get(x, 0))
                for x in first.keys() | second.keys()), F(0))


def bit(p):
    return {0: 1 - p, 1: p}


def value(roots, own, opp, table):
    return mean(roots, lambda h: mean(bit(own), lambda a:
                mean(bit(opp), lambda b: table[h][a][b])))


class NashTransportControls(unittest.TestCase):
    def test_exhaustive_model_nash_actual_opponent_and_roots(self):
        table = {0: ((F(1), F(-1)), (F(-1), F(1))),
                 1: ((F(-1), F(1)), (F(1), F(-1)))}
        choices = (F(0), F(1, 2), F(1))
        exact = 0
        for mp, ap, own, modeled, old, unknown in product(choices, repeat=6):
            model, actual = bit(mp), bit(ap)
            baseline = value(model, own, modeled, table)
            # Both players' deviations, with player 1 receiving the negative payoff.
            epsilon = max(F(0),
                max(value(model, a, modeled, table) - baseline for a in (F(0), F(1))),
                max(baseline - value(model, own, b, table) for b in (F(0), F(1))))
            actual_gain = value(actual, old, unknown, table) - value(actual, own, unknown, table)
            # Outcomes retain both actions: changing the opposing Bernoulli law
            # has this exact L1 distance for either fixed own policy.
            left_charge = right_charge = 2 * abs(unknown - modeled)
            transport = 2 * variation(actual, model) + left_charge + right_charge
            self.assertLessEqual(actual_gain, epsilon + transport)
            if ap == mp and unknown == modeled:
                self.assertLessEqual(actual_gain, epsilon)
            exact += epsilon == 0
        self.assertGreater(exact, 0)

    def test_two_root_terms_are_necessary(self):
        model = bit(F(1, 2))
        old = {0: F(-1), 1: F(1)}
        fresh = {0: F(1), 1: F(-1)}
        # Equal model values: no model regret despite disjoint own choices.
        self.assertEqual(mean(model, old.get), mean(model, fresh.get))
        for delta in (F(1, 1000000), F(1, 7), F(1, 2)):
            actual = bit(F(1, 2) + delta)
            gain = mean(actual, old.get) - mean(actual, fresh.get)
            self.assertEqual(gain, 2 * variation(actual, model))
            self.assertGreater(gain, variation(actual, model))
        # Identical support does not remove root-distribution error.
        self.assertEqual(set(model), set(bit(F(3, 5))))

    def test_unknown_opponent_term_cannot_be_erased(self):
        # Matching pennies: the half/half profile is exact Nash.
        # An old pure row can exploit the actual pure opponent better.
        table = {0: ((F(1), F(-1)), (F(-1), F(1)))}
        roots = {0: F(1)}
        fresh = F(1, 2)
        self.assertEqual(value(roots, fresh, fresh, table), 0)
        gain = value(roots, F(0), F(0), table) - value(roots, fresh, F(0), table)
        self.assertEqual(gain, 1)
        self.assertEqual(variation(roots, roots), 0)
        self.assertGreater(gain, 0)  # Nash error + root error would both be zero.
        # Transport vanishes with the modeled opponent, even for the old pure row.
        self.assertEqual(value(roots, F(0), fresh, table) -
                         value(roots, fresh, fresh, table), 0)

    def test_late_horizon_and_native_forward_weights(self):
        # Both choices have zero current payoff. A shorter-horizon exact
        # equilibrium does not control their different delayed outcomes.
        current = {"old": F(0), "fresh": F(0)}
        late = {"old": F(1), "fresh": F(-1)}
        self.assertEqual(current["old"] - current["fresh"], 0)
        self.assertEqual(late["old"] - late["fresh"], 2)
        def aligned(final, configs):
            remaining = final
            result = True
            for cuts, fuel in reversed(configs):
                result &= sum(cuts) == fuel + remaining
                remaining += fuel
            return result
        self.assertTrue(aligned(1, [([1, 1, 1], 1), ([1, 1], 1)]))
        self.assertFalse(aligned(1, [([1, 1, 1], 1), ([1], 1)]))
        self.assertTrue(aligned(2, [([0, 1, 1], 0)]))
        for p, q in product((F(1, 7), F(1, 2), F(6, 7)), repeat=2):
            # Native state includes the private tag and its correlated model.
            actual = {(0, 0): p, (1, 1): 1 - p}
            local = lambda state: F(1, 8) + state[0] * F(1, 3)
            next_native = {(0, 0): q, (1, 1): 1 - q}
            second = lambda state: F(1, 9) + state[1] * F(1, 2)
            cost = mean(actual, local) + mean(next_native, second)
            explicit = F(1, 8) + (1 - p) / 3 + F(1, 9) + (1 - q) / 2
            self.assertEqual(cost, explicit)
            if p != q:
                self.assertNotEqual(cost, mean(actual, local) + mean(actual, second))

    def test_support_charge_separate_from_model_nash(self):
        for outside in (F(0), F(1, 11), F(1)):
            actual = {"supported": 1 - outside, "outside": outside}
            # On support sampled value equals the average. Outside, the gap
            # between two bounded values can attain exactly 2*bound.
            sampled = {"supported": F(1, 3), "outside": F(-2)}
            average = {"supported": F(1, 3), "outside": F(2)}
            penalty = mean(actual, lambda h: average[h] - sampled[h])
            self.assertEqual(penalty, 4 * outside)
            if outside:
                self.assertGreater(penalty, 0)
        # A pointwise root-law bound may be much looser than averaging first.
        prior = bit(F(1, 2))
        expected_distance = mean(prior, lambda h: variation({h: F(1)}, prior))
        self.assertEqual(expected_distance, 1)
        self.assertEqual(variation(prior, prior), 0)


if __name__ == "__main__":
    unittest.main()
