"""Exact finite-law controls for native randomized resolver support transport.

These arithmetic fixtures are not Lean proofs or a complete CFR implementation.
They independently detect pooling selected models, wrong-prefix weighting,
and the stopped/missing-belief boundary of the new support predicate.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product
import unittest

Law = tuple[F, F]
Kernel = tuple[Law, Law]
GRID = (F(0), F(1, 2), F(1))


def bernoulli(zero_mass: F) -> Law:
    """A normalized two-point law; zero weights are not in its support."""
    if not F(0) <= zero_mass <= F(1):
        raise ValueError("probability outside the unit interval")
    return zero_mass, 1 - zero_mass


def bind(law: Law, kernel: Kernel) -> Law:
    return tuple(sum((law[x] * kernel[x][y] for x in range(2)), F(0))
                 for y in range(2))


def unsupported(actual: Law, model: Law) -> F:
    return sum((actual[x] for x in range(2) if model[x] == 0), F(0))


def leakage(actual: Law, first: Kernel, second: Kernel) -> F:
    return sum((actual[x] * unsupported(first[x], second[x])
                for x in range(2)), F(0))


def weighted(weights: Law, values: tuple[F, F]) -> F:
    return sum((weights[i] * values[i] for i in range(2)), F(0))


class ResolverSupportTests(unittest.TestCase):
    def test_native_profile_model_pairing_cannot_be_pooled(self) -> None:
        weights = bernoulli(F(1, 4))
        actual = (bernoulli(F(0)), bernoulli(F(0)))
        models = (bernoulli(F(1)), bernoulli(F(0)))
        paired = weighted(weights, tuple(unsupported(actual[i], models[i])
                                         for i in range(2)))
        pooled_actual = bind(weights, actual)
        pooled_model = bind(weights, models)
        self.assertEqual(paired, F(1, 4))
        self.assertEqual(unsupported(pooled_actual, pooled_model), 0)
        self.assertGreater(paired, unsupported(pooled_actual, pooled_model))

    def test_retained_memory_preserves_pair_specific_event(self) -> None:
        weights = bernoulli(F(1, 4))
        models = (bernoulli(F(1)), bernoulli(F(0)))
        # Every actual outcome is history 1, but its private selected model differs.
        next_states = [(('old', (chosen,)), 1, models[chosen], weights[chosen])
                       for chosen in range(2)]
        failed = sum((mass for _, history, model, mass in next_states
                      if model[history] == 0), F(0))
        self.assertEqual(failed, F(1, 4))
        self.assertEqual(len({memory for memory, _, _, _ in next_states}), 2)

    def test_stopped_state_does_not_query_or_erase_incoming_failure(self) -> None:
        calls = []

        def transition(live, history, model, query):
            # Finite control of the explicit no-query stopping convention.
            if live:
                return query()
            return history, model

        def forbidden_query() -> None:
            calls.append('query')
            raise AssertionError('stopped stage must not invoke a resolver')

        for history, model, expected in ((0, None, True),
                                         (0, bernoulli(F(1)), False),
                                         (1, bernoulli(F(1)), True)):
            kept_history, kept_model = transition(False, history, model, forbidden_query)
            failed = kept_model is None or kept_model[kept_history] == 0
            self.assertEqual(failed, expected)
        self.assertEqual(calls, [])

    def test_missing_live_belief_has_unit_failure_not_a_fake_posterior(self) -> None:
        weights = bernoulli(F(1, 4))
        outcomes = (bernoulli(F(1)), bernoulli(F(0)))
        # Every selected profile leaves a missing carried belief missing.
        failure = sum((weights[i] * sum(outcomes[i]) for i in range(2)), F(0))
        self.assertEqual(failure, 1)
        self.assertNotEqual(failure, 0)

    def test_reweighting_positive_model_support_has_no_incoming_cost(self) -> None:
        actual, model = bernoulli(F(1, 4)), bernoulli(F(1, 2))
        identity = (bernoulli(F(1)), bernoulli(F(0)))
        self.assertEqual(unsupported(actual, model), 0)
        self.assertEqual(leakage(actual, identity, identity), 0)
        self.assertEqual(unsupported(bind(actual, identity), bind(model, identity)), 0)
        self.assertEqual(sum(abs(a - b) for a, b in zip(actual, model)), F(1, 2))

    def test_zero_weight_profiles_are_not_required_to_dominate(self) -> None:
        weights = bernoulli(F(1))
        costs = (F(0), F(1))
        self.assertEqual(weighted(weights, costs), 0)
        self.assertGreater(costs[1], 0)

    def test_wrong_prefix_weights_undercharge_support_leakage(self) -> None:
        actual, model = bernoulli(F(1, 4)), bernoulli(F(0))
        first = (bernoulli(F(1)), bernoulli(F(0)))
        second = (bernoulli(F(0)), bernoulli(F(0)))
        self.assertEqual(leakage(actual, first, second), F(1, 4))
        self.assertEqual(leakage(model, first, second), 0)

    def test_exhaustive_one_step_bound_then_native_mixture(self) -> None:
        weights = bernoulli(F(1, 4))
        for prior_mass, root in product(GRID, range(2)):
            actual = bernoulli(F(1 - root))
            prior = bernoulli(prior_mass)
            for entries in product(GRID, repeat=6):
                first = (bernoulli(entries[0]), bernoulli(entries[1]))
                models = ((bernoulli(entries[2]), bernoulli(entries[3])),
                          (bernoulli(entries[4]), bernoulli(entries[5])))
                actual_next = bind(actual, first)
                failures = tuple(unsupported(actual_next, bind(prior, model))
                                 for model in models)
                charges = tuple(unsupported(actual, prior) + leakage(actual, first, model)
                                for model in models)
                for failure, charge in zip(failures, charges):
                    self.assertLessEqual(failure, charge)
                self.assertLessEqual(weighted(weights, failures), weighted(weights, charges))


if __name__ == '__main__':
    unittest.main()
