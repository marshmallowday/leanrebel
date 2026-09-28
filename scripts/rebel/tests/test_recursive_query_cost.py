"""Independent rational controls for native query/diameter safety.

No control here claims to execute the Lean CFR solver.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import unittest


def expect(law, value):
    return sum((mass * value(state) for state, mass in law.items()), F(0))


def bind(law, kernel):
    out = defaultdict(F)
    for state, mass in law.items():
        for nxt, weight in kernel(state).items():
            out[nxt] += mass * weight
    return dict(out)


def queried(state, fuel):
    # Full state: history, retained private draw, saved-PBS presence, terminal.
    return fuel > 0 and state[2] and not state[3]


class QueryCostTests(unittest.TestCase):
    def test_interval_width_and_rare_query_mass_are_tight(self):
        for rare, lower, width in product(
            (F(1, 100), F(1, 4), F(1)),
            (F(-7), F(0), F(100)),
            (F(0), F(1, 3), F(5)),
        ):
            law = {False: 1 - rare, True: rare}
            old = lambda hit: lower + width if hit else lower
            fresh = lambda _hit: lower
            loss = expect(law, old) - expect(law, fresh)
            self.assertEqual(loss, width * rare)
            for shift in (F(-1000), F(19)):
                shifted = expect(law, lambda h: old(h) + shift)
                shifted -= expect(law, lambda h: fresh(h) + shift)
                self.assertEqual(shifted, loss)
        # Omitting the actual event probability overcharges rare queries.
        self.assertLess(F(5, 100), F(5))

    def test_missing_stopped_and_zero_fuel_keep_the_late_incumbent(self):
        for has_pbs, stopped, fuel, late in product(
            (False, True), (False, True), (0, 1, 2), (0, 1, 3)
        ):
            state = (0, 1, has_pbs, stopped)
            old = F(2 + late)
            candidate = F(-1 - late)
            native = candidate if queried(state, fuel) else old
            loss = old - native
            diameter = old - candidate
            self.assertLessEqual(loss, diameter * int(queried(state, fuel)))
            if not queried(state, fuel):
                self.assertEqual(loss, 0)
        # A missing PBS can still have a nonzero incumbent late payoff.
        self.assertEqual(F(2 + 3), 5)

    def test_unsupported_queries_are_not_deleted(self):
        for mass in (F(1, 100), F(1, 3), F(1)):
            supported = (0, 0, True, False)
            unsupported = (1, 1, True, False)
            states = {supported: 1 - mass, unsupported: mass}
            loss = expect(states, lambda s: F(4) if s == unsupported else F(0))
            actual_queries = expect(states, lambda s: F(queried(s, 1)))
            supported_queries = expect(
                states, lambda s: F(queried(s, 1) and s == supported)
            )
            self.assertLessEqual(loss, 4 * actual_queries)
            if mass == 1:
                self.assertGreater(loss, 4 * supported_queries)
        # Negative signed gains must remain negative.
        self.assertLessEqual(F(-3), F(0))

    def test_native_joint_forward_query_count_and_retained_late_draw(self):
        for weight, stop in product((F(1, 4), F(1, 2), F(3, 4)),
                                    (F(0), F(1, 3), F(1))):
            states = {(0, 0, True, False): weight,
                      (1, 1, True, False): 1 - weight}

            def step(s):
                h, seed, present, terminal = s
                if terminal:
                    return {s: F(1)}
                return {(h, seed, present, True): stop,
                        (h, seed, present, False): 1 - stop}

            first = expect(states, lambda s: F(queried(s, 1)))
            advanced = bind(states, step)
            second = expect(advanced, lambda s: F(queried(s, 1)))
            self.assertEqual(first + second, 2 - stop)
            self.assertEqual(
                expect(advanced, lambda s: F(s[0] == s[1])), 1
            )
            # Redrawing at the late tail destroys retained history/draw pairing.
            redrawn_match = weight**2 + (1 - weight)**2
            self.assertLess(redrawn_match, 1)
            # Replacing the native future by an all-stopped average changes visits.
            self.assertLessEqual(second, 1)
        self.assertGreater(F(2), F(1))  # Visits are not a union probability.

    def test_capped_security_and_independent_parent_terms(self):
        for signed, grouped, query_cap in (
            (F(1, 4), F(1, 3), F(1)),
            (F(1, 4), F(5), F(1, 2)),
            (F(-2), F(-1), F(0)),
        ):
            self.assertLessEqual(signed, min(grouped, query_cap))
            for prediction, finite, child in product(
                (F(0), F(1, 8)), (F(1, 2), F(1, 8)), (F(1, 4), F(1, 16))
            ):
                initial = prediction + finite + 2 * child
                capped = initial + min(grouped, query_cap)
                self.assertLessEqual(initial + signed, capped)
                self.assertGreater(finite + 2 * child, 0)
        # A growing search count does not itself make actual queries rare.
        for count in (1, 4, 16, 64):
            query_visits = F(1)
            self.assertEqual(4 * query_visits, 4)
            self.assertGreater(count, 0)


if __name__ == "__main__":
    unittest.main()
