"""Independent rational controls for saved rooted public-to-original queries.

These kernels and finite matrix comparisons do not execute CFR or Lean.
"""
from fractions import Fraction as F
from itertools import product
import unittest

from test_rooted_child_decode import utility, nash_error, push


def condition(law, event):
    reach = sum((w for h, w in law.items() if event(h)), F(0))
    if not reach:
        return None
    return {h: w / reach for h, w in law.items() if event(h)}


def mean(law, value):
    return sum((w * value(h) for h, w in law.items()), F(0))


def blend(live, stopped, live_mass):
    return tuple(tuple(live_mass * live[r][c] + (1 - live_mass) * stopped[r][c]
                       for c in (0, 1)) for r in (0, 1))


class RootedStoredQueryTests(unittest.TestCase):
    def test_actual_saved_public_joint_decode_and_missing(self):
        # Rooted histories retain a private seed and a correlated original state.
        prior = {(0, (0, 0), True, "seen"): F(1, 20),
                 (1, (1, 1), True, "seen"): F(3, 20),
                 (1, (1, 0), False, "seen"): F(6, 20),
                 (0, (0, 1), True, "other"): F(1, 2)}
        public = condition(prior, lambda h: h[3] == "seen")
        live = condition(prior, lambda h: h[3] == "seen" and h[2])
        read = lambda h: (h[1], h[2])
        saved = push(public, read)
        self.assertEqual(saved, {((0, 0), True): F(1, 10),
                                 ((1, 1), True): F(3, 10),
                                 ((1, 0), False): F(3, 5)})
        self.assertNotEqual(saved, push(live, read))
        self.assertNotEqual(saved, push(prior, read))
        self.assertIsNone(condition(prior, lambda h: h[3] == "absent"))
        self.assertEqual(mean(public, lambda h: h[0] * h[1][0]), F(9, 10))
        self.assertNotEqual(mean(public, lambda h: h[0] * h[1][0]),
                            mean(public, lambda h: h[0]) *
                            mean(public, lambda h: h[1][0]))

    def test_stopped_fraction_needs_public_denominator_and_common_kernel(self):
        cases = 0
        for reach, live_share, shift in product(
                (F(1, 1000), F(1, 7), F(1)),
                (F(1, 8), F(1, 2), F(7, 8)), (F(-3), F(0), F(5))):
            law = {"live": reach * live_share, "stop": reach * (1 - live_share),
                   "else": 1 - reach}
            public = condition(law, lambda h: h != "else")
            live = condition(law, lambda h: h == "live")
            value = lambda h: shift + (1 if h == "live" else -1)
            gap = abs(mean(public, value) - mean(live, value))
            self.assertEqual(gap, 2 * (1 - live_share))
            if reach < 1:
                self.assertGreater(gap, 2 * law["stop"])
            cases += 1
        self.assertEqual(cases, 27)

    def test_independent_public_and_live_nash_and_private_security(self):
        live = ((F(1), F(-1)), (F(-1), F(1)))
        stopped = ((F(-1), F(-1)), (F(-1), F(-1)))
        grid = (F(0), F(1, 2), F(1))
        cases = 0
        for share in (F(1, 10), F(1, 2), F(9, 10)):
            public = blend(live, stopped, share)
            root_error = 2 * (1 - share)
            for ri, ci, rf, cf in product(grid, repeat=4):
                internal_error = nash_error(live, ri, ci)
                fresh_error = nash_error(public, rf, cf)
                internal_value = utility(live, ri, ci)
                fresh_value = utility(public, rf, cf)
                self.assertLessEqual(abs(internal_value - fresh_value),
                                     internal_error + fresh_error + root_error)
                for unknown in grid:
                    private = ((1 - rf) * utility(public, 0, unknown) +
                               rf * utility(public, 1, unknown))
                    self.assertEqual(private, utility(public, rf, unknown))
                    self.assertGreaterEqual(
                        private, internal_value - internal_error - 2 * fresh_error - root_error)
                cases += 1
        self.assertEqual(cases, 243)

    def test_stopped_mass_and_fresh_security_terms_cannot_be_discarded(self):
        # Exact self-play values differ even with two exact solvers.
        live = ((F(1), F(1)), (F(1), F(1)))
        stopped = ((F(-1), F(-1)), (F(-1), F(-1)))
        public = blend(live, stopped, F(1, 4))
        self.assertEqual(nash_error(live, 0, 0), 0)
        self.assertEqual(nash_error(public, 1, 1), 0)
        self.assertEqual(abs(utility(live, 0, 0) - utility(public, 1, 1)), F(3, 2))
        # Scalar self-play proximity alone gives no opponent-uniform security.
        matrix = ((F(1), F(-1)), (F(-1), F(1)))
        reference = utility(matrix, F(1, 2), F(1, 2))
        fresh_selfplay = utility(matrix, 0, F(1, 2))
        self.assertEqual(reference, fresh_selfplay)
        self.assertLess(utility(matrix, 0, 1), fresh_selfplay)
        self.assertGreater(nash_error(matrix, 0, F(1, 2)), 0)

    def test_native_correlation_horizon_and_retained_private_draw(self):
        for p in (F(1, 10), F(1, 2), F(9, 10)):
            native = {(0, 0): 1 - p, (1, 1): p}
            redrawn = {(a, b): pa * pb for a, pa in enumerate((1 - p, p))
                       for b, pb in enumerate((1 - p, p))}
            self.assertEqual(mean(native, lambda h: int(h[0] == h[1])), 1)
            self.assertLess(mean(redrawn, lambda h: int(h[0] == h[1])), 1)
            # An observer of the seed can choose the losing response each time.
            matching = ((F(1), F(-1)), (F(-1), F(1)))
            self.assertEqual(mean(native, lambda h: utility(matching, h[0], 1 - h[0])), -1)
        # A late, action-independent reward changes the scalar under a new clock.
        values_by_fuel = {0: F(0), 1: F(0), 2: F(1)}
        self.assertNotEqual(values_by_fuel[1], values_by_fuel[2])
        # Neither prediction error nor child loss replaces the finite term.
        for delta, finite, child in product((F(0), F(1, 8)), (F(1, 4), F(1, 9)),
                                             (F(0), F(1, 5))):
            parent = 3 * delta + finite + 2 * child
            self.assertGreaterEqual(parent, finite)


if __name__ == "__main__":
    unittest.main()
