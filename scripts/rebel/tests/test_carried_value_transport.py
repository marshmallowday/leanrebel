"""Exact arithmetic controls for carried execution and late value transport.

These finite models exercise the intended semantics independently of the Lean
proofs. They do not replace Lean compilation, transitive axiom audits, or review.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def expect(law, value):
    return sum((mass * value(state) for state, mass in law.items()), F(0))


def bind(law, kernel):
    result = {}
    for state, mass in law.items():
        for target, weight in kernel(state).items():
            result[target] = result.get(target, F(0)) + mass * weight
    return {state: mass for state, mass in result.items() if mass}


def run(law, kernel, fuel):
    for _ in range(fuel):
        law = bind(law, kernel)
    return law


def variation(first, second):
    return sum((abs(first.get(state, F(0)) - second.get(state, F(0)))
                for state in first.keys() | second.keys()), F(0))


def execution_charge(law, first, second, fuel):
    """Accumulate L1 row differences under FIRST-policy prefix laws."""
    total = F(0)
    for _ in range(fuel):
        total += expect(law, lambda history:
                        variation(first(history), second(history)))
        law = bind(law, first)
    return total


def fixed_policy(bit):
    return lambda history: {history + (bit,): F(1)}


def bernoulli(probability_one):
    return {0: 1 - probability_one, 1: probability_one}


def resolve_step(state, fuel, draw):
    """A full state retains history and the privately selected policy."""
    if fuel == 0:
        return {state: F(1)}
    history, _ = state
    return bind(
        draw(state),
        lambda bit: {
            (target, bit): mass
            for target, mass in run(
                {history: F(1)}, fixed_policy(bit), fuel).items()
        },
    )


def selected_value(state, remaining, payoff):
    history, selected = state
    return expect(run({history: F(1)}, fixed_policy(selected), remaining),
                  payoff)


def replacement_charge(state, fuel, remaining, draw):
    # A stopped stage neither asks the resolver nor replaces its policy.
    if fuel == 0:
        return F(0)
    history, selected = state
    return expect(
        draw(state),
        lambda bit: execution_charge(
            {history: F(1)}, fixed_policy(selected), fixed_policy(bit),
            fuel + remaining),
    )


def posterior(prior, likelihood):
    mass = expect(prior, likelihood.__getitem__)
    if mass == 0:
        return None
    return {state: weight * likelihood[state] / mass
            for state, weight in prior.items()}


class CarriedValueTransportTests(unittest.TestCase):
    def test_late_tail_charge_cannot_be_replaced_by_stage_charge(self):
        cases = 0
        for stage_fuel, remaining in product((1, 2, 3), repeat=2):
            first = fixed_policy(0)

            def second(history):
                bit = int(len(history) >= stage_fuel)
                return {history + (bit,): F(1)}

            root = {(): F(1)}
            self.assertEqual(run(root, first, stage_fuel),
                             run(root, second, stage_fuel))
            self.assertEqual(
                execution_charge(root, first, second, stage_fuel), 0)
            payoff = lambda history: F(1 - history[-1])
            horizon = stage_fuel + remaining
            loss = (expect(run(root, first, horizon), payoff) -
                    expect(run(root, second, horizon), payoff))
            full_charge = execution_charge(root, first, second, horizon)
            self.assertEqual(loss, 1)
            self.assertEqual(full_charge, 2 * remaining)
            self.assertLessEqual(abs(loss), full_charge)
            cases += 1
        self.assertEqual(cases, 9)

    def test_private_draw_is_retained_into_the_late_tail(self):
        cases = 0
        for probability in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
            draw = lambda state: bernoulli(probability)
            states = resolve_step(((), 0), 1, draw)
            retained = bind(
                states,
                lambda state: run(
                    {state[0]: F(1)}, fixed_policy(state[1]), 1),
            )
            resampled = bind(
                states,
                lambda state: bind(
                    bernoulli(probability),
                    lambda bit: fixed_policy(bit)(state[0])),
            )
            payoff = lambda history: F(history[0] == history[1])
            self.assertEqual(expect(retained, payoff), 1)
            self.assertEqual(expect(resampled, payoff),
                             probability ** 2 + (1 - probability) ** 2)
            if 0 < probability < 1:
                self.assertLess(expect(resampled, payoff),
                                expect(retained, payoff))
            cases += 1
        self.assertEqual(cases, 5)

    def test_signed_losses_telescope_under_forward_full_state_laws(self):
        cases = 0
        for first_probability, after_zero, after_one in product(
                (F(0), F(1, 2), F(1)), repeat=3):
            states = {((), 0): F(1, 3), ((), 1): F(2, 3)}
            payoff = lambda history: F(
                sum(1 - 2 * bit for bit in history), 3)
            initial_value = expect(
                states, lambda state: selected_value(state, 3, payoff))

            def first_draw(state):
                return bernoulli(first_probability)

            def second_draw(state):
                probability = after_zero if state[0][-1] == 0 else after_one
                return bernoulli(probability)

            signed_total = F(0)
            charge_total = F(0)
            for remaining, draw in ((2, first_draw), (1, second_draw)):
                def loss(state):
                    before = selected_value(state, 1 + remaining, payoff)
                    after = expect(
                        resolve_step(state, 1, draw),
                        lambda target: selected_value(
                            target, remaining, payoff))
                    return before - after

                signed_stage = expect(states, loss)
                stage_charge = expect(
                    states,
                    lambda state: replacement_charge(
                        state, 1, remaining, draw))
                self.assertLessEqual(signed_stage, stage_charge)
                signed_total += signed_stage
                charge_total += stage_charge
                states = bind(
                    states, lambda state: resolve_step(state, 1, draw))
                self.assertEqual(sum(states.values(), F(0)), 1)

            final_histories = bind(
                states,
                lambda state: run(
                    {state[0]: F(1)}, fixed_policy(state[1]), 1),
            )
            actual_loss = initial_value - expect(final_histories, payoff)
            self.assertEqual(actual_loss, signed_total)
            self.assertLessEqual(actual_loss, charge_total)
            cases += 1
        self.assertEqual(cases, 27)

    def test_rare_history_charge_uses_actual_not_model_weights(self):
        actual = {(0,): F(9, 10), (1,): F(1, 10)}
        model = {(0,): F(99, 100), (1,): F(1, 100)}
        first = fixed_policy(0)

        def second(history):
            return {history + (history[0],): F(1)}

        payoff = lambda history: F(1 - 2 * history[-1])
        loss = (expect(run(actual, first, 1), payoff) -
                expect(run(actual, second, 1), payoff))
        actual_charge = execution_charge(actual, first, second, 1)
        model_charge = execution_charge(model, first, second, 1)
        self.assertEqual(loss, F(1, 5))
        self.assertEqual(actual_charge, loss)
        self.assertEqual(model_charge, F(1, 50))
        self.assertGreater(loss, model_charge)
        self.assertEqual(actual.keys(), model.keys())

    def test_zero_fuel_does_not_query_or_replace_even_with_positive_tail(self):
        state = ((1,), 0)
        calls = []

        def forbidden_draw(current):
            calls.append(current)
            raise AssertionError("A stopped stage queried its resolver")

        self.assertEqual(resolve_step(state, 0, forbidden_draw),
                         {state: F(1)})
        self.assertEqual(replacement_charge(state, 0, 3, forbidden_draw), 0)
        self.assertEqual(calls, [])
        payoff = lambda history: F(history[-1])
        self.assertEqual(selected_value(state, 3, payoff), 0)
        self.assertEqual(selected_value((state[0], 1), 3, payoff), 1)
        self.assertGreater(execution_charge(
            {state[0]: F(1)}, fixed_policy(0), fixed_policy(1), 3), 0)

    def test_negative_signed_replacement_gain_is_preserved(self):
        payoff = lambda history: F(history[-1])
        initial = ((), 0)
        first_states = resolve_step(initial, 1, lambda state: {1: F(1)})
        first_loss = (
            selected_value(initial, 3, payoff) -
            expect(first_states, lambda state: selected_value(state, 2, payoff)))
        second_states = bind(
            first_states,
            lambda state: resolve_step(state, 1, lambda current: {0: F(1)}),
        )
        second_loss = (
            expect(first_states, lambda state: selected_value(state, 2, payoff)) -
            expect(second_states, lambda state: selected_value(state, 1, payoff)))
        actual_loss = (
            selected_value(initial, 3, payoff) -
            expect(second_states, lambda state: selected_value(state, 1, payoff)))
        self.assertEqual(first_loss, -1)
        self.assertEqual(second_loss, 1)
        self.assertEqual(actual_loss, first_loss + second_loss)
        self.assertEqual(actual_loss, 0)
        self.assertNotEqual(max(first_loss, 0) + max(second_loss, 0),
                            actual_loss)

    def test_posterior_uses_stored_prior_and_selected_future_policy(self):
        initial = {0: F(1, 2), 1: F(1, 2)}
        previous_likelihood = {0: F(3, 4), 1: F(1, 4)}
        selected_likelihood = {0: F(1, 3), 1: F(1)}
        stored = posterior(initial, previous_likelihood)
        self.assertEqual(stored, {0: F(3, 4), 1: F(1, 4)})
        correct = posterior(stored, selected_likelihood)
        reset = posterior(initial, selected_likelihood)
        pooled_likelihood = {
            state: (previous_likelihood[state] + selected_likelihood[state]) / 2
            for state in initial
        }
        pooled = posterior(stored, pooled_likelihood)
        self.assertEqual(correct, {0: F(1, 2), 1: F(1, 2)})
        self.assertEqual(reset, {0: F(1, 4), 1: F(3, 4)})
        self.assertEqual(pooled, {0: F(13, 18), 1: F(5, 18)})
        self.assertNotEqual(correct, reset)
        self.assertNotEqual(correct, pooled)


if __name__ == '__main__':
    unittest.main()
