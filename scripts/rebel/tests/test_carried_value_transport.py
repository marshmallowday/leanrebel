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


    def test_public_then_type_kernel_preserves_joint_correlation(self):
        # Three own types; type 2 is unreachable and has explicit completions.
        prior = {(0, 0): F(2, 5), (0, 1): F(1, 10),
                 (1, 0): F(1, 10), (1, 1): F(2, 5)}
        cases = 0
        for low, high in product((F(1, 4), F(1, 2), F(3, 4)), repeat=2):
            likelihood = {h: high if h[1] else low for h in prior}
            public = posterior(prior, likelihood)
            masses = {t: sum((m for h, m in public.items() if h[0] == t), F(0))
                      for t in (0, 1)}
            kernels = {
                t: {h: m / masses[t] for h, m in public.items() if h[0] == t}
                for t in masses
            }
            self.assertEqual(bind(masses, kernels.__getitem__), public)
            for t in masses:
                weights = {h: prior[h] * likelihood[h]
                           for h in prior if h[0] == t}
                total = sum(weights.values(), F(0))
                self.assertEqual(kernels[t], {h: m / total for h, m in weights.items()})
                self.assertEqual(sum(kernels[t].values(), F(0)), 1)
            self.assertEqual(masses.get(2, 0), 0)
            for completion in ({(2, 0): F(1)}, {(2, 1): F(1)}):
                completed = {**kernels, 2: completion}
                self.assertEqual(bind(masses, completed.__getitem__), public)
            # Independent marginals destroy the conditional opposing bit.
            opponent = sum((m for h, m in public.items() if h[1] == 1), F(0))
            self.assertNotEqual(kernels[0].get((0, 1), F(0)), opponent)
            cases += 1
        self.assertEqual(cases, 9)

    def test_value_coupling_ignores_payoff_preserving_label_change(self):
        # Disjoint histories, nonconstant payoff on the physical carrier.
        old = {("old",): F(1)}
        fresh = {("fresh",): F(1)}
        values = {("old",): F(1), ("fresh",): F(1), ("bad",): F(-1)}
        joint = {(("fresh",), ("old",)): F(1)}
        cost = expect(joint, lambda pair:
                      max(F(0), values[pair[1]] - values[pair[0]]))
        signed = expect(old, values.__getitem__) - expect(fresh, values.__getitem__)
        self.assertEqual(variation(old, fresh), 2)
        self.assertEqual(cost, 0)
        self.assertEqual(signed, 0)
        self.assertLess(cost, variation(old, fresh))
        self.assertEqual(bind(joint, lambda pair: {pair[0]: F(1)}), fresh)
        self.assertEqual(bind(joint, lambda pair: {pair[1]: F(1)}), old)

    def test_coupling_marginals_and_orientation_are_essential(self):
        for fresh_value, old_value in product((F(-1), F(0), F(1)), repeat=2):
            joint = {(fresh_value, old_value): F(1)}
            cost = expect(joint, lambda pair: max(F(0), pair[1] - pair[0]))
            signed = old_value - fresh_value
            self.assertLessEqual(signed, cost)
            self.assertLessEqual(signed, min(cost, F(2)))
        # Reversing the directed cost is invalid for a payoff-losing replacement.
        self.assertGreater(F(1) - F(-1), max(F(0), F(-1) - F(1)))
        law = {-1: F(1, 2), 1: F(1, 2)}
        diagonal = {(-1, -1): F(1, 2), (1, 1): F(1, 2)}
        independent = {(a, b): p * q for a, p in law.items() for b, q in law.items()}
        cost = lambda joint: expect(joint, lambda pair: max(F(0), pair[1] - pair[0]))
        self.assertEqual(cost(diagonal), 0)
        self.assertEqual(cost(independent), F(1, 2))
        for joint in (diagonal, independent):
            for index in (0, 1):
                self.assertEqual(bind(joint, lambda pair: {pair[index]: F(1)}), law)

    def test_value_cost_composes_under_native_forward_weights(self):
        states = {((), 0): F(1, 3), ((), 1): F(2, 3)}
        payoff = lambda history: F(history[-1])
        before = expect(states, lambda state: selected_value(state, 3, payoff))
        total_signed, total_cost, total_kernel = F(0), F(0), F(0)
        for remaining, bit in ((2, 1), (1, 0)):
            draw = lambda state: {bit: F(1)}
            def quantities(state):
                old = run({state[0]: F(1)}, fixed_policy(state[1]), 1 + remaining)
                next_states = resolve_step(state, 1, draw)
                fresh = bind(next_states, lambda nxt:
                             run({nxt[0]: F(1)}, fixed_policy(nxt[1]), remaining))
                joint = {(new, oldh): p * q
                         for new, p in fresh.items() for oldh, q in old.items()}
                signed = expect(old, payoff) - expect(fresh, payoff)
                cost = expect(joint, lambda pair:
                              max(F(0), payoff(pair[1]) - payoff(pair[0])))
                kernel = replacement_charge(state, 1, remaining, draw)
                self.assertLessEqual(signed, min(cost, kernel))
                return signed, cost, kernel
            total_signed += expect(states, lambda state: quantities(state)[0])
            total_cost += expect(states, lambda state: quantities(state)[1])
            total_kernel += expect(states, lambda state: quantities(state)[2])
            states = bind(states, lambda state: resolve_step(state, 1, draw))
        after = expect(states, lambda state: selected_value(state, 1, payoff))
        self.assertEqual(before - after, total_signed)
        self.assertEqual(total_signed, F(2, 3))
        self.assertEqual(total_cost, F(1))
        self.assertLess(total_cost, total_kernel)


if __name__ == '__main__':
    unittest.main()
