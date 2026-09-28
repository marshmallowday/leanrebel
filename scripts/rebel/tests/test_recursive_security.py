"""Independent exact-rational controls for finite-parent/native-chain accounting.

These finite kernels exercise the combined allowance and retained-memory
telescope. They are not a Python execution of the Lean CFR implementation.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def mean(law, value):
    return sum((mass * value(state) for state, mass in law.items()), F(0))


def bind(law, kernel):
    result = {}
    for state, mass in law.items():
        for nxt, weight in kernel(state).items():
            result[nxt] = result.get(nxt, F(0)) + mass * weight
    return result


def advance(state, fuel):
    """Retain both the chosen draw and its stored model through late fuel."""
    hidden, draw, model, stopped = state
    if stopped or fuel == 0:
        return state
    return (hidden ^ (draw if fuel % 2 else 0), draw, model, stopped)


def payoff(state):
    return F(1 if state[0] == state[2] else -1)


def fresh(state, probability, fuel):
    if state[3] or fuel == 0:
        return {state: F(1)}
    hidden, _, model, stopped = state
    # New model memory and private draw stay correlated in the full state.
    return {advance((hidden, draw, model ^ draw, stopped), fuel): weight
            for draw, weight in ((0, 1 - probability), (1, probability))}


def chain(law, configs, late):
    current = law
    signed = F(0)
    remaining = late + sum(fuel for _, fuel in configs)
    costs = []
    for probability, fuel in configs:
        after = bind(current, lambda s: fresh(s, probability, fuel))
        before_value = mean(current, lambda s: payoff(advance(s, remaining)))
        after_value = mean(after, lambda s: payoff(advance(s, remaining - fuel)))
        cost = before_value - after_value
        costs.append(cost)
        signed += cost
        current = after
        remaining -= fuel
    return mean(current, lambda s: payoff(advance(s, late))), signed, costs


def allowance(delta, sqrt_t, child_loss, error_factor=F(3), finite_factor=F(2)):
    return error_factor * delta + finite_factor / sqrt_t + 2 * child_loss


class RecursiveSecurityControls(unittest.TestCase):
    def test_independent_prediction_iteration_and_child_terms(self):
        for delta, root_t, loss in product((F(0), F(1, 100), F(1, 3)),
                                         (F(1), F(3), F(10)), (F(0), F(1, 8))):
            total = allowance(delta, root_t, loss)
            self.assertEqual(total - allowance(F(0), root_t, loss), 3 * delta)
            self.assertEqual(total - allowance(delta, root_t, F(0)), 2 * loss)
            self.assertEqual(total - allowance(delta, 2 * root_t, loss), 1 / root_t)
        self.assertEqual(allowance(F(0), F(4), F(1, 8)), F(3, 4))
        # An allowance comparison, NOT a counterexample proving positive CFR error.
        printed = F(0) * 3 + F(0) * 2 / 4
        self.assertEqual(printed, 0)
        self.assertGreater(allowance(F(0), F(4), F(0)), printed)

    def test_depth_recurrence_keeps_constants_independent(self):
        # Independent numerical, finite and child terms under a structural recurrence.
        for delta, root_t, child in product((F(0), F(1, 7)),
                                           (F(1), F(5)), (F(0), F(1, 11))):
            coefficients = (F(0), F(1), F(0))
            direct = 1 / root_t
            for depth in range(1, 6):
                multiplier = F(depth + 1, depth)
                direct = multiplier * direct + 2 * delta + 3 / root_t + 2 * child
                a, b, c = coefficients
                coefficients = (multiplier * a + 2, multiplier * b + 3,
                                multiplier * c + 2)
                a, b, c = coefficients
                self.assertEqual(direct, a * delta + b / root_t + c * child)
                self.assertGreater(b, 0)

    def test_actual_full_state_telescope_and_parent_inheritance(self):
        saw_negative = False
        for p, q, r in product((F(1, 7), F(1, 2), F(6, 7)), repeat=3):
            initial = {(0, 0, 0, False): p, (1, 1, 1, False): 1 - p}
            configs = [(q, 1), (r, 1)]
            before = mean(initial, lambda s: payoff(advance(s, 3)))
            final, signed, costs = chain(initial, configs, 1)
            self.assertEqual(before - final, signed)
            saw_negative |= any(cost < 0 for cost in costs)
            # An explicit independent initial security certificate plus its slack.
            initial_error = abs(before)
            reference = before + initial_error
            parent = initial_error + allowance(F(1, 10), F(5), F(1, 20))
            self.assertLessEqual(reference - parent, before)
            self.assertLessEqual(reference - (parent + signed), final)
            self.assertEqual((reference - final) - (reference - before), signed)
        self.assertTrue(saw_negative)

    def test_support_penalty_and_signed_cost_do_not_cancel_by_assumption(self):
        for mass, delta, root_t in product((F(0), F(1, 13), F(1)),
                                          (F(0), F(1, 7)), (F(1), F(4))):
            law = {"inside": 1 - mass, "outside": mass}
            average = {"inside": F(1, 2), "outside": F(1)}
            sampled = {"inside": F(1, 2), "outside": F(-1)}
            actual_penalty = mean(law, lambda s: average[s] - sampled[s])
            self.assertEqual(actual_penalty, 2 * mass)
            parent = allowance(delta, root_t, F(1, 9))
            computed_loss = F(-1, 5)
            complete = parent + computed_loss + actual_penalty
            self.assertEqual(complete - parent - computed_loss, 2 * mass)
            if mass:
                self.assertGreater(complete, parent + computed_loss)
        # Even zero prediction error leaves all three independent contributions.
        self.assertEqual(allowance(F(0), F(4), F(1, 8)) + F(1, 3), F(13, 12))

    def test_empty_zero_fuel_stopping_and_same_draw_late(self):
        law = {(0, 0, 0, False): F(1, 3), (1, 1, 1, True): F(2, 3)}
        expected = mean(law, lambda s: payoff(advance(s, 2)))
        self.assertEqual(chain(law, [], 2), (expected, F(0), []))
        final, signed, costs = chain(law, [(F(3, 4), 0)], 2)
        self.assertEqual((final, signed, costs), (expected, F(0), [F(0)]))
        stopped = {(1, 1, 0, True): F(1)}
        self.assertEqual(chain(stopped, [(F(1, 4), 1), (F(3, 4), 2)], 4),
                         (F(-1), F(0), [F(0), F(0)]))
        # A draw held through stage AND late cancels two bit flips. Re-drawing
        # in the late step changes the payoff while leaving the stage marginal.
        after = {(0, 0, 0, False): F(1, 4), (1, 1, 0, False): F(3, 4)}
        native = mean(after, lambda s: payoff(advance(s, 1)))
        redrawn = bind(after, lambda s: {
            advance((s[0], d, s[2], False), 1): w
            for d, w in ((0, F(1, 4)), (1, F(3, 4)))})
        self.assertNotEqual(native, mean(redrawn, payoff))


if __name__ == "__main__":
    unittest.main()
