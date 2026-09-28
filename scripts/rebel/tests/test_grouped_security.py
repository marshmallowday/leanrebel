"""Independent exact-rational controls for conditional native grouping.

These finite controls are not executions of the Lean CFR implementation.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import unittest


def expect(law, value):
    return sum((mass * value(state) for state, mass in law.items()), F(0))


def marginal(law, tag):
    result = defaultdict(F)
    for state, mass in law.items():
        result[tag(state)] += mass
    return dict(result)


def conditional(law, tag, label):
    mass = sum((p for state, p in law.items() if tag(state) == label), F(0))
    if not mass:
        return dict(law)  # Total fallback, unused in disintegration.
    return {state: p / mass for state, p in law.items() if tag(state) == label}


def variation(first, second):
    return sum((abs(first.get(x, 0) - second.get(x, 0))
                for x in first.keys() | second.keys()), F(0))


def grouped(law, tag, value):
    labels = marginal(law, tag)
    return expect(labels, lambda label: expect(conditional(law, tag, label), value))


def forward(law, kernel):
    result = defaultdict(F)
    for state, mass in law.items():
        for after, chance in kernel(state).items():
            result[after] += mass * chance
    return dict(result)


class GroupedSecurityTests(unittest.TestCase):
    def test_calibrated_groups_remove_singleton_root_overcharge(self):
        for weight, first, second in product((F(1, 17), F(1, 3), F(4, 5)),
                                              (F(1, 7), F(2, 3), F(4, 5)),
                                              (F(1, 4), F(3, 5), F(9, 10))):
            law = {(0, 0): weight * first, (0, 1): weight * (1 - first),
                   (1, 0): (1 - weight) * second,
                   (1, 1): (1 - weight) * (1 - second)}
            models = {0: {0: first, 1: 1 - first},
                      1: {0: second, 1: 1 - second}}
            labels = marginal(law, lambda state: state[0])
            grouped_charge = expect(labels, lambda label: variation(
                marginal(conditional(law, lambda state: state[0], label),
                         lambda state: state[1]), models[label]))
            singleton_charge = expect(law, lambda state:
                                      variation({state[1]: F(1)}, models[state[0]]))
            self.assertEqual(grouped_charge, 0)
            self.assertGreater(singleton_charge, 0)
            value = lambda state: F(3 * state[0] - 2 * state[1], 7)
            self.assertEqual(grouped(law, lambda state: state[0], value),
                             expect(law, value))
        self.assertEqual(conditional(law, lambda state: state[0], 99), law)

    def test_private_incumbent_and_saved_posterior_cannot_be_erased(self):
        # Own action equals the retained seed, perfectly correlated with history.
        law = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
        payoff = lambda action, history: F(1 if action == history else -1)
        old_value = expect(law, lambda state: payoff(state[0], state[1]))
        fresh_value = expect(law, lambda state:
                             (payoff(0, state[1]) + payoff(1, state[1])) / 2)
        self.assertEqual(old_value - fresh_value, 1)
        # Destroying the incumbent/history correlation would falsely give zero.
        product_law = {(seed, history): F(1, 4) for seed, history in product(range(2), repeat=2)}
        self.assertEqual(expect(product_law, lambda state: payoff(*state)), 0)
        for seed in (0, 1):
            actual = marginal(conditional(law, lambda state: state[0], seed),
                              lambda state: state[1])
            self.assertEqual(actual, {seed: F(1)})
            self.assertEqual(variation(actual, {0: F(1, 2), 1: F(1, 2)}), 1)
        # Selected MODEL is itself correlated with the seed; averaging then
        # independently redrawing it changes the native joint distribution.
        saved = {(seed, seed, history): mass for (seed, history), mass in law.items()}
        self.assertEqual(expect(saved, lambda state: F(state[1] == state[2])), 1)
        self.assertEqual(expect(product_law, lambda state: F(state[0] == state[1])), F(1, 2))

    def test_actual_label_weights_and_uncertified_cost_are_retained(self):
        law = {("live", 0): F(1, 10), ("live", 1): F(1, 10),
               ("missing", 0): F(7, 10), ("stopped", 1): F(1, 10)}
        values = {"live": F(-1, 2), "missing": F(3, 4), "stopped": F(0)}
        exact = expect(law, lambda state: values[state[0]])
        self.assertEqual(grouped(law, lambda state: state[0],
                                 lambda state: values[state[0]]), exact)
        self.assertEqual(exact, F(17, 40))
        self.assertNotEqual(exact, sum(values.values()) / 3)
        self.assertNotEqual(exact, F(-1, 10))  # Missing is not a zero-cost cell.
        # A maximal two-sided deviation on actual unsupported mass is tight.
        unsupported = F(7, 10)
        self.assertEqual(unsupported * (F(2) - F(-2)), 2 * 2 * unsupported)

    def test_nash_root_and_opponent_terms_remain_after_grouping(self):
        # Two root states with sign-reversed matching-pennies payoffs.
        # Uniform fresh policies are exact Nash for every model root law.
        for actual0, model0, old0, opponent0 in product(
                (F(1, 7), F(1, 2), F(6, 7)),
                (F(1, 4), F(1, 2), F(3, 4)),
                (F(0), F(1, 2), F(1)),
                (F(0), F(1, 3), F(1))):
            signed_change = (2 * actual0 - 1) * (2 * old0 - 1) * (2 * opponent0 - 1)
            root = 2 * abs(actual0 - model0)
            opponent_charge = 2 * abs(opponent0 - F(1, 2))
            bound = 2 * root + opponent_charge + opponent_charge
            self.assertLessEqual(signed_change, bound)
        self.assertEqual((2 * F(1) - 1) * (2 * F(1) - 1) * (2 * F(1) - 1), 1)
        # Exact Nash and a calibrated root do not remove an unknown opponent.

    def test_native_joint_forward_and_retained_late_draw(self):
        for prior, chance in product((F(1, 9), F(1, 2), F(8, 9)),
                                     (F(1, 5), F(1, 2), F(4, 5))):
            law = {(0, 0, False): prior, (1, 1, False): 1 - prior}
            def step(state):
                seed, model, stopped = state
                if stopped:
                    return {state: F(1)}
                return {(seed, model, True): chance,
                        (seed, model, False): 1 - chance}
            after = forward(law, step)
            after_two = forward(after, step)
            value = lambda state: F(1 if state[0] == state[1] else -1)
            for states in (law, after, after_two):
                self.assertEqual(grouped(states, lambda state: (state[0], state[1]),
                                         value), expect(states, value))
                self.assertEqual(expect(states, value), 1)
            # Independent late resampling loses the private-draw/MODEL correlation.
            redrawn = forward(after, lambda state:
                              {(0, state[1], state[2]): F(1, 2),
                               (1, state[1], state[2]): F(1, 2)})
            self.assertEqual(expect(redrawn, value), 0)
            # Empty and zero-fuel execution are identities, not discarded tails.
            self.assertEqual(forward(law, lambda state: {state: F(1)}), law)
            self.assertEqual(sum(after_two.values()), 1)


if __name__ == "__main__":
    unittest.main()
