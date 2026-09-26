"""Exact event-tail controls; diagnostic losses are not CFR-generated gaps.

These rational calculations distinguish a selected conditional probability from
its unconditional joint-event probability. Lean compilation and axiom checks
remain separate acceptance requirements.
"""
from fractions import Fraction as F
from itertools import product
import unittest

from test_public_posterior import condition, pushforward


def expectation(law, observable):
    return sum((mass * observable(point) for point, mass in law.items()), F(0))


def event_mass(law, event):
    return sum((mass for point, mass in law.items() if point in event), F(0))


class PublicNativeTailControls(unittest.TestCase):
    def test_exact_joint_and_conditional_rates(self):
        cases = 0
        losses = ((0, 0, 0, 0), (0, 1, 1, 0), (0, 1, 2, 3), (3, 0, 0, 0))
        for weights in product((0, 1, 2), repeat=4):
            total = sum(weights)
            if total == 0:
                continue
            law = {point: F(weight, total) for point, weight in enumerate(weights)}
            for flags in product((False, True), repeat=4):
                event = {point for point, included in enumerate(flags) if included}
                mass = event_mass(law, event)
                for values in losses:
                    mean = expectation(law, lambda point: values[point])
                    for threshold in (F(1, 4), F(1), F(2)):
                        bad = {point for point in law if threshold <= values[point]}
                        joint = event_mass(law, event & bad)
                        self.assertLessEqual(joint, mean / threshold)
                        if mass:
                            _, selected = condition(law, event)
                            tail = event_mass(selected, bad)
                            self.assertEqual(mass * tail, joint)
                            self.assertLessEqual(tail, mean / (mass * threshold))
                        else:
                            self.assertEqual(joint, 0)
                        cases += 1
        self.assertEqual(cases, 15360)

    def test_real_tagged_kernel_without_resampling(self):
        tags = tuple(product(range(2), repeat=2))
        prior = {tag: F(1, 4) for tag in tags}
        execution = {}
        for tag, mass in prior.items():
            probability = F(sum(tag), 2)
            execution[(tag, 0)] = mass * (1 - probability)
            execution[(tag, 1)] = mass * probability
        self.assertEqual(pushforward(execution, lambda point: point[0]), prior)
        event = {point for point in execution if point[1] == 1}
        mass, selected = condition(execution, event)
        query = pushforward(selected, lambda point: point[0])
        seed = pushforward(query, lambda tag: tag[0])
        own_type = pushforward(query, lambda tag: tag[1])
        self.assertNotEqual(query, {tag: seed[tag[0]] * own_type[tag[1]] for tag in tags})
        loss = lambda tag: F(tag == (1, 1))
        mean = expectation(prior, loss)
        tail = event_mass(query, {tag for tag in tags if loss(tag) >= 1})
        self.assertEqual((mass, mean, tail), (F(1, 2), F(1, 4), F(1, 2)))
        self.assertEqual(mass * tail, mean)
        self.assertGreater(tail, mean)

    def test_rare_public_observation_has_no_uniform_conditional_rate(self):
        for denominator in (2, 3, 7, 1000003):
            rare = F(1, denominator)
            # The output discloses the type, not the private iteration.
            execution = {((seed, own_type), own_type): F(1, 2) *
                         (rare if own_type else 1 - rare)
                         for seed, own_type in product(range(2), repeat=2)}
            event = {point for point in execution if point[1] == 1}
            mass, selected = condition(execution, event)
            bad = {point for point in execution if point[0][1] == 1}
            mean = expectation(execution, lambda point: F(point[0][1] == 1))
            tail = event_mass(selected, bad)
            self.assertEqual(mass, rare)
            self.assertEqual((tail, event_mass(execution, event & bad)), (F(1), rare))
            self.assertEqual(tail, mean / mass)
            self.assertGreater(tail, mean)

    def test_impossible_public_event_has_joint_rate_but_no_posterior(self):
        execution = {((0, 0), 0): F(1, 2), ((1, 0), 0): F(1, 2),
                     ((0, 1), 1): F(0), ((1, 1), 1): F(0)}
        for event in (set(), {point for point in execution if point[1] == 1}):
            self.assertEqual(event_mass(execution, event), 0)
            self.assertEqual(event_mass(execution, event & set(execution)), 0)
            with self.assertRaisesRegex(ValueError, "Impossible"):
                condition(execution, event)


if __name__ == "__main__":
    unittest.main()
