"""Independent exact-rational controls for backed-up root training vectors.

These finite games test information-fiber cancellation, terminal handling and
iteration correlation. They neither execute Lean nor certify convergence.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def mean(law, value):
    return sum((mass * value(leaf) for leaf, mass in law.items()), F(0))


def conditioned(law, tag, selected):
    mass = sum((p for h, p in law.items() if tag(h) == selected), F(0))
    if not mass:
        return dict(law)  # explicit FinDist total convention, not a posterior
    return {h: p / mass for h, p in law.items() if tag(h) == selected}


def supported(law, tag):
    return {tag(h) for h, p in law.items() if p}


def backup(law, info, root, live, actual, predicted, selected):
    root_law = conditioned(law, lambda h: root(info(h)), selected)
    return mean(root_law, lambda h: predicted[info(h)] if live(h) else actual(h))


def vector_average(vectors):
    return {key: sum((v[key] for v in vectors), F(0)) / len(vectors)
            for key in vectors[0]}


class ValueTargetControls(unittest.TestCase):
    def test_root_fiber_cancellation_without_hidden_pointwise_accuracy(self):
        # The residuals +9 and -9 cancel inside each live information fiber.
        # Conditioning on a remembered root type must preserve that cancellation.
        for rare, bias in product((F(1, 2), F(1, 101), F(1, 1000000)),
                                  (F(-1, 8), F(0), F(1, 8))):
            law = {(r, hidden): (rare if r == 0 else 1 - rare) / 2
                   for r, hidden in product(range(2), repeat=2)}
            value = lambda h: F(2 * h[0]) + (9 if h[1] else -9)
            predicted = {0: bias, 1: F(2) + bias}
            for r in range(2):
                target = backup(law, lambda h: h[0], lambda i: i, lambda h: True,
                                value, predicted, r)
                exact = mean(conditioned(law, lambda h: h[0], r), value)
                self.assertEqual(target - exact, bias)
                self.assertGreater(abs(predicted[r] - value((r, 0))), F(1, 8))

    def test_terminal_and_exhausted_leaves_do_not_query_predictions(self):
        law = {("terminal", 0): F(1, 4), ("exhausted", 0): F(1, 4),
               ("live", 0): F(1, 2)}
        values = {"terminal": F(7), "exhausted": F(-3), "live": F(2)}
        # No terminal/exhausted dictionary entries: a query there raises KeyError.
        target = backup(law, lambda h: h[0], lambda i: 0,
                        lambda h: h[0] == "live", lambda h: values[h[0]],
                        {"live": F(17, 8)}, 0)
        self.assertEqual(target, F(33, 16))
        self.assertEqual(target - mean(law, lambda h: values[h[0]]), F(1, 16))

    def test_absent_root_label_is_separately_marked(self):
        law = {("a", 0): F(1, 3), ("a", 1): F(2, 3)}
        tags = supported(law, lambda h: h[0])
        self.assertNotIn("b", tags)
        self.assertEqual(conditioned(law, lambda h: h[0], "b"), law)
        # A total vector entry exists, but no training sample for b was observed.
        self.assertEqual(mean(conditioned(law, lambda h: h[0], "b"),
                              lambda h: F(h[1])), F(2, 3))

    def test_online_uniform_vector_mean_and_error(self):
        vectors = [{0: F(2 * n - 1), 1: F(4 * n + 2)} for n in range(7)]
        errors = [F((-1) ** n, 8) for n in range(7)]
        noisy = [{key: value + errors[n] for key, value in v.items()}
                 for n, v in enumerate(vectors)]
        online = dict(noisy[0])
        for n in range(1, len(noisy)):
            online = {key: F(n, n + 1) * online[key] + noisy[n][key] / (n + 1)
                      for key in online}
            self.assertEqual(online, vector_average(noisy[:n + 1]))
        exact = vector_average(vectors)
        for key in exact:
            self.assertLessEqual(abs(online[key] - exact[key]), F(1, 8))
        self.assertNotEqual(exact, vectors[-1])
        self.assertNotEqual(exact[0], exact[1])

    def test_both_player_average_payoff_is_not_average_target(self):
        # Both players use 0 in round 0 and 1 in round 1.
        # Equality payoff is always 1 per round. Independently mixing their
        # policies creates unequal actions, so evaluating that profile gives 1/2.
        targets = [F(int(a == b)) for a, b in ((0, 0), (1, 1))]
        independently_mixed = sum((F(int(a == b), 4)
                                   for a, b in product(range(2), repeat=2)), F(0))
        self.assertEqual(sum(targets) / 2, 1)
        self.assertEqual(independently_mixed, F(1, 2))
        self.assertNotEqual(sum(targets) / 2, independently_mixed)

    def test_root_readout_keeps_first_private_snapshot(self):
        # Administrative root observation contains own type. Later observations
        # may differ but cannot alter the root coordinate or reveal other types.
        def root_readout(local):
            return local[1][1]
        for own, other, later in product(range(2), repeat=3):
            local = ((None, None), (None, own), ("move", later))
            self.assertEqual(root_readout(local), own)
            changed_world = ((None, None), (None, own), ("move", other))
            self.assertEqual(root_readout(local), root_readout(changed_world))

    def test_prediction_change_uses_changed_learner_trace(self):
        # A simple positive-regret update changes the NEXT policy when biased.
        # This is an independent recurrence control, not a Lean CFR proof.
        def next_policy(scores):
            regrets = [score - sum(scores) / 2 for score in scores]
            positive = [max(F(0), r) for r in regrets]
            return [r / sum(positive) for r in positive]
        old = next_policy([F(0), F(1, 16)])
        new = next_policy([F(1, 8), F(1, 16)])
        self.assertNotEqual(old, new)
        continuation = [F(-2), F(3)]
        old_value = sum(p * v for p, v in zip(old, continuation))
        new_value = sum(p * v for p, v in zip(new, continuation))
        predicted = new_value + F(1, 8)
        self.assertEqual(abs(predicted - new_value), F(1, 8))
        self.assertGreater(abs(predicted - old_value), F(1, 8))

    def test_remembered_label_kernel_commutes_with_conditioning(self):
        # Correlated root types, rare labels and zero-probability coordinates.
        for rare, move in product((F(1, 2), F(1, 101), F(1, 1000000)),
                                  (F(0), F(1, 3), F(1))):
            roots = {(0, 0): rare / 4, (0, 1): 3 * rare / 4,
                     (1, 0): (1 - rare) * F(2, 3), (1, 1): (1 - rare) / 3}

            def kernel(root):
                return {(*root, 0): 1 - move, (*root, 1): move}

            end = {leaf: mass * p for root, mass in roots.items()
                   for leaf, p in kernel(root).items()}
            value = lambda h: F(5 * h[1] - 3 * h[2] + h[0])
            for label in (0, 1, 2):
                early = mean(conditioned(roots, lambda h: h[0], label),
                             lambda h: mean(kernel(h), value))
                late = mean(conditioned(end, lambda h: h[0], label), value)
                self.assertEqual(early, late)
            for label in (0, 1):
                root_mass = sum(p for h, p in roots.items() if h[0] == label)
                end_mass = sum(p for h, p in end.items() if h[0] == label)
                self.assertEqual(root_mass, end_mass)

    def test_cut_tower_includes_early_terminal_roots(self):
        # terminal branches do not acquire fictitious observations or actions.
        roots = {(0, "terminal"): F(1, 5), (0, "live"): F(2, 5),
                 (1, "live"): F(2, 5)}

        def continuation(h):
            if h[1] == "terminal":
                return {(h[0], "terminal", 7): F(1)}
            return {(h[0], "done", -2): F(1, 4),
                    (h[0], "done", 6): F(3, 4)}

        full = {leaf: mass * p for h, mass in roots.items()
                for leaf, p in continuation(h).items()}
        # Contributions from different roots that reach the same leaf add.
        self.assertEqual(sum(full.values()), 1)
        for label in (0, 1, 2):
            cut_value = mean(conditioned(roots, lambda h: h[0], label),
                             lambda h: mean(continuation(h), lambda x: F(x[2])))
            full_value = mean(conditioned(full, lambda h: h[0], label),
                              lambda x: F(x[2]))
            self.assertEqual(cut_value, full_value)
        self.assertEqual(mean(conditioned(full, lambda h: h[0], 0),
                              lambda h: F(h[2])), F(5))

    def test_latest_observation_is_not_a_retained_root_label(self):
        roots = {0: F(1, 4), 1: F(3, 4)}
        # Later private observations swap, so reading the latest snapshot
        # reverses which original information state the payoff belongs to.
        full = {(r, 1 - r): p for r, p in roots.items()}
        value = lambda h: F(10 * h[0])
        self.assertEqual(mean(conditioned(full, lambda h: h[0], 0), value), 0)
        self.assertEqual(mean(conditioned(full, lambda h: h[1], 0), value), 10)
        self.assertNotEqual(sum(p for h, p in full.items() if h[1] == 0), roots[0])

    def test_conditioning_preserves_hidden_correlation(self):
        roots = {(0, 0): F(1, 10), (0, 1): F(4, 10),
                 (1, 0): F(3, 10), (1, 1): F(2, 10)}
        true_value = mean(conditioned(roots, lambda h: h[0], 0), lambda h: F(h[1]))
        hidden_marginal = mean(roots, lambda h: F(h[1]))
        self.assertEqual(true_value, F(4, 5))
        self.assertEqual(hidden_marginal, F(3, 5))
        self.assertNotEqual(true_value, hidden_marginal)

    def test_original_continuation_mean_uses_each_noisy_round(self):
        roots = {(0, 0): F(1, 8), (0, 1): F(3, 8),
                 (1, 0): F(3, 8), (1, 1): F(1, 8)}
        exact, target = [], []
        for n in range(5):
            chance = F(n, 4)
            vector = {}
            for label in (0, 1):
                vector[label] = mean(
                    conditioned(roots, lambda h: h[0], label),
                    lambda h: (1 - chance) * (2 * h[1] - 1) + chance * (3 - h[1]))
            exact.append(vector)
            target.append({label: v + F((-1) ** n, 8) for label, v in vector.items()})
        for label, val in vector_average(exact).items():
            self.assertLessEqual(abs(vector_average(target)[label] - val), F(1, 8))
            self.assertNotEqual(val, exact[-1][label])


if __name__ == "__main__":
    unittest.main()
