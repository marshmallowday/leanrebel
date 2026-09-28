"""Independent rational controls for recursive-child replay.

These finite history kernels check the semantic boundaries of the Lean
integration; they neither execute CFR nor claim solver convergence.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def bind(law, kernel):
    result = {}
    for first, mass in law.items():
        for last, conditional in kernel(first).items():
            result[last] = result.get(last, F(0)) + mass * conditional
    return {h: p for h, p in result.items() if p}


def push(law, fn):
    return bind(law, lambda h: {fn(h): F(1)})


def expectation(law, fn):
    return sum((p * fn(h) for h, p in law.items()), F(0))


def conditioned(law, read, label):
    selected = {h: p for h, p in law.items() if read(h) == label}
    mass = sum(selected.values(), F(0))
    return {h: p / mass for h, p in selected.items()} if mass else dict(law)


def child_draw(history, weight, opponent):
    # A single private iterate controls BOTH own actions. The intervening
    # opponent decision is unknown to the child model, and may depend on root.
    if history[-1] == "stop":
        return {history: F(1)}
    return {(history, a, b, a): pa * pb
            for a, pa in ((0, weight), (1, 1 - weight))
            for b, pb in ((0, opponent), (1, 1 - opponent)) if pa * pb}


def own_reach_average(history, weight, opponent):
    if history[-1] == "stop":
        return {history: F(1)}
    prefix = {(history, a, b): pa * pb
              for a, pa in ((0, weight), (1, 1 - weight))
              for b, pb in ((0, opponent), (1, 1 - opponent)) if pa * pb}
    # Perfect recall reveals own first action. Its own-reach weighted
    # continuation fixes the same action, rather than resampling a policy.
    return bind(prefix, lambda h: {h + (h[1],): F(1)})


class RecursiveReplayControls(unittest.TestCase):
    def test_supported_roots_arbitrary_unknown_reweighting_and_late_fuel(self):
        for rare, actual_first, opponent in product(
                (F(1, 2), F(1, 101), F(1, 1000000)),
                (F(0), F(1, 4), F(1)), (F(0), F(2, 3), F(1))):
            roots = ((0, "live"), (1, "live"))
            model = {roots[0]: rare, roots[1]: 1 - rare}
            actual = {roots[0]: actual_first, roots[1]: 1 - actual_first}
            drawn = lambda h: child_draw(h, F(1, 3), opponent)
            averaged = lambda h: own_reach_average(h, F(1, 3), opponent)
            self.assertEqual(bind(model, drawn), bind(model, averaged))
            for root in roots:
                self.assertEqual(drawn(root), averaged(root))
            self.assertEqual(bind(actual, drawn), bind(actual, averaged))
            self.assertEqual(expectation(bind(actual, drawn),
                                         lambda h: F(h[1] != h[3])), 0)
        stopped = (2, "stop")
        self.assertEqual(child_draw(stopped, F(1, 3), F(2, 3)), {stopped: 1})

    def test_redrawing_at_late_continuation_breaks_replay(self):
        root, weight = (0, "live"), F(1, 3)
        retained = child_draw(root, weight, F(1, 2))
        redrawn = {(root, a, b, late): pa * F(1, 2) * pl
                   for a, pa in ((0, weight), (1, 1 - weight))
                   for b in (0, 1)
                   for late, pl in ((0, weight), (1, 1 - weight))}
        # Stage history alone cannot distinguish the incorrect independent
        # late draw, while the complete history/payoff does distinguish it.
        self.assertEqual(push(retained, lambda h: h[:3]),
                         push(redrawn, lambda h: h[:3]))
        self.assertEqual(expectation(retained, lambda h: F(h[1] != h[3])), 0)
        self.assertEqual(expectation(redrawn, lambda h: F(h[1] != h[3])), F(4, 9))

    def test_parent_factual_mass_scaled_budget_is_computational_data(self):
        # This control is a budget-dependent finite solver, not a Nash proof.
        def solve(tolerance):
            rounds = (F(1) / tolerance).__ceil__()
            return F(rounds - 1, rounds)
        for mass in (F(1, 2), F(1, 7), F(1, 101)):
            factual = {"hidden-a": mass, "hidden-b": 1 - mass}
            target = min(factual.values()) * F(1, 3)
            parent_child = solve(target)
            fresh_same = solve(target)
            fresh_wrong = solve(F(1, 3))
            self.assertEqual(parent_child, fresh_same)
            self.assertNotEqual(parent_child, fresh_wrong)
        # Public conditioning with a terminal atom differs from live-public
        # conditioning: a later stored PBS cannot simply be substituted.
        public = {("a", True): F(1, 4), ("b", True): F(1, 4),
                  ("c", False): F(1, 2)}
        live = conditioned(public, lambda h: h[1], True)
        self.assertNotEqual(public, live)
        self.assertEqual(live, {("a", True): F(1, 2), ("b", True): F(1, 2)})

    def test_unsupported_actual_roots_need_explicit_probability_charge(self):
        for unsupported in (F(0), F(1, 10), F(1, 2), F(1)):
            actual = {"supported": 1 - unsupported, "absent": unsupported}
            first = bind(actual, lambda h: {-1: F(1)} if h == "absent" else {0: F(1)})
            second = bind(actual, lambda h: {1: F(1)} if h == "absent" else {0: F(1)})
            error = abs(expectation(first, F) - expectation(second, F))
            self.assertEqual(error, 2 * unsupported)
            if unsupported:
                self.assertNotEqual(first, second)

    def test_history_first_preserves_native_draw_posterior_correlation(self):
        # State = (history, private draw, its modeled posterior). Same history
        # may arise from multiple draws; future re-solving can read the pair.
        native = {("h0", 0, F(1, 4)): F(1, 6),
                  ("h0", 1, F(3, 4)): F(1, 3),
                  ("h1", 0, F(1, 4)): F(1, 2)}
        histories = push(native, lambda s: s[0])
        rebuilt = bind(histories, lambda h: conditioned(native, lambda s: s[0], h))
        self.assertEqual(native, rebuilt)
        future = lambda s: F(s[1] == 1 and s[2] == F(3, 4))
        self.assertEqual(expectation(native, future), expectation(rebuilt, future))
        draws = push(native, lambda s: s[1])
        beliefs = push(native, lambda s: s[2])
        independent = {(h, d, b): ph * pd * pb for h, ph in histories.items()
                       for d, pd in draws.items() for b, pb in beliefs.items()}
        self.assertEqual(expectation(native, future), F(1, 3))
        self.assertEqual(expectation(independent, future), F(1, 9))
        self.assertNotEqual(native, independent)


if __name__ == "__main__":
    unittest.main()
