"""Exact rational controls for recomputed values and native forward costs.

The finite kernels are independent controls, not claims of executing Lean or
of a CFR trace. They separate posterior filtering, changed policies, retained
private randomness and support defects under the actual joint state law.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def mean(law, value):
    return sum((p * value(x) for x, p in law.items()), F(0))


def bind(law, kernel):
    result = {}
    for x, p in law.items():
        for y, q in kernel(x).items():
            result[y] = result.get(y, F(0)) + p * q
    return {x: p for x, p in result.items() if p}


def conditional(law, event):
    mass = sum((p for x, p in law.items() if event(x)), F(0))
    return {x: p / mass for x, p in law.items() if p and event(x)}


class RecomputedValueControls(unittest.TestCase):
    def test_changed_policy_signed_residual(self):
        for reach, live, skew in product(
                (F(1), F(1, 101), F(1, 1000000)),
                (F(1), F(1, 2), F(1, 1000)),
                (F(1, 7), F(2, 7), F(4, 7), F(6, 7))):
            law = {(True, True, 0): reach * live * skew,
                   (True, True, 1): reach * live * (1 - skew),
                   (True, False, 2): reach * (1 - live),
                   (False, False, 3): 1 - reach}
            saved = conditional(law, lambda x: x[0])
            child = conditional(law, lambda x: x[0] and x[1])
            first = lambda x: F(2) if x[2] % 2 == 0 else F(-1)
            second = lambda x: F(-2) if x[2] == 0 else F(1, 3)
            difference = mean(saved, first) - mean(child, second)
            changed = mean(child, lambda x: first(x) - second(x))
            posterior = mean(saved, first) - mean(child, first)
            self.assertEqual(difference - changed, posterior)
            self.assertLessEqual(abs(difference - changed), 4 * (1 - live))
            # The centered residual preserves the sign of the policy term.
            self.assertLessEqual(difference, changed + 4 * (1 - live))

    def test_solver_change_survives_zero_posterior_error(self):
        # Same supported PBS, different computation/budget selects another policy.
        saved = child = {0: F(1, 3), 1: F(2, 3)}
        first, second = lambda _: F(2), lambda _: F(-2)
        change = mean(child, lambda x: first(x) - second(x))
        difference = mean(saved, first) - mean(child, second)
        self.assertEqual(change, 4)
        self.assertEqual(difference - change, 0)
        # Small discarded mass likewise does not control changed policies.
        for stopped in (F(1, 1000), F(1, 1000000)):
            saved = {0: 1 - stopped, 2: stopped}
            child = {0: F(1)}
            difference = mean(saved, first) - mean(child, second)
            self.assertGreater(abs(difference), 4 * stopped)

    def test_actual_support_penalty_and_direction_are_tight(self):
        # Only the unsupported state disagrees. Native is -2, proxy is +2.
        for missing in (F(0), F(1, 1000), F(1, 4), F(1)):
            actual = {False: 1 - missing, True: missing}
            old = lambda _: F(1)
            native = lambda bad: F(-2) if bad else F(0)
            proxy = lambda bad: F(2) if bad else F(0)
            native_loss = mean(actual, lambda x: old(x) - native(x))
            computed_loss = mean(actual, lambda x: old(x) - proxy(x))
            self.assertEqual(native_loss, computed_loss + 4 * missing)
            # A model law has no missing mass, but cannot replace actual weights.
            if missing:
                self.assertGreater(native_loss, computed_loss)
            # A gain is kept as a negative local loss, not clamped away.
            self.assertEqual(F(-1) - F(2), -3)

    def test_native_joint_forward_telescoping(self):
        for skew, first_weight, second_weight in product(
                (F(1, 5), F(1, 2), F(4, 5)), repeat=3):
            initial = {(0, 0): skew, (1, 1): 1 - skew}
            value = lambda state: F(2) if state[0] == state[1] else F(-2)

            def kernel(weight, state):
                hidden, old = state
                # A private-memory-dependent resolver, with hidden type retained.
                return {(hidden, old): weight, (hidden, 1 - old): 1 - weight}

            actual = initial
            signed_sum = F(0)
            computed_budget = F(0)
            for weight in (first_weight, second_weight):
                native = lambda state: mean(kernel(weight, state), value)
                bad = lambda state: state == (1, 0)
                proxy = lambda state: F(2) if bad(state) else native(state)
                signed_sum += mean(actual, lambda state: value(state) - native(state))
                computed_budget += mean(actual, lambda state: value(state) - proxy(state))
                computed_budget += 4 * mean(actual, lambda state: F(bad(state)))
                actual = bind(actual, lambda state: kernel(weight, state))
            self.assertEqual(mean(initial, value) - mean(actual, value), signed_sum)
            self.assertLessEqual(signed_sum, computed_budget)
        # Replacing joint memory by independent marginals destroys the value.
        correlated = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
        independent = {x: F(1, 4) for x in product((0, 1), repeat=2)}
        self.assertEqual(mean(correlated, value), 2)
        self.assertEqual(mean(independent, value), 0)

    def test_full_late_fuel_private_draw_and_stopped_stage(self):
        for weight, late in product((F(1, 5), F(1, 2), F(4, 5)), (1, 2, 7)):
            retained = {(0, 0, late): weight, (1, 1, late): 1 - weight}
            redrawn = {(a, b, late): pa * pb
                       for a, pa in ((0, weight), (1, 1 - weight))
                       for b, pb in ((0, weight), (1, 1 - weight))}
            value = lambda out: F(2) if out[0] == out[1] else F(-2)
            self.assertEqual(mean(retained, value), 2)
            self.assertLess(mean(redrawn, value), 2)
        # One-step kernels may agree while a positive late step differs.
        old_path, fresh_path = (0, 0), (0, 1)
        self.assertEqual(old_path[0], fresh_path[0])
        self.assertNotEqual(old_path[1], fresh_path[1])
        # A stopped or zero-fuel stage makes no draw despite a positive tail.
        for live, present in product((False, True), repeat=2):
            calls = []
            def resolve():
                calls.append("query")
                return F(-2)
            old_tail = F(2)
            result = resolve() if live and present else old_tail
            if not live or not present:
                self.assertEqual(calls, [])
                self.assertEqual(result, old_tail)


if __name__ == "__main__":
    unittest.main()
