"""Exact-rational integration controls for recursive root training output.

The finite kernels vary with the node and parent round. These tests detect
cross-round/level averaging and horizon mistakes; they do not run Lean or
assert equilibrium convergence.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def mean(law, value):
    return sum((p * value(h) for h, p in law.items()), F(0))


def conditional(law, label):
    selected = {h: p for h, p in law.items() if h[0] == label}
    mass = sum(selected.values(), F(0))
    return {h: p / mass for h, p in selected.items()} if mass else dict(law)


def advance(law, fuel, round_index, level):
    result = dict(law)
    for step in range(fuel):
        next_law = {}
        for history, mass in result.items():
            # A terminal private branch absorbs. Later steps cannot restart it.
            if history[-1] == "stop":
                next_law[history] = next_law.get(history, F(0)) + mass
                continue
            p = F(1 + (round_index + level + step + history[1]) % 3, 4)
            for action, weight in ((0, 1 - p), (1, p)):
                end = history + (action,)
                next_law[end] = next_law.get(end, F(0)) + mass * weight
        result = next_law
    return result


def payoff(history):
    return F(3 * history[1] - history[0] +
             sum((2 * j - 1) * a for j, a in enumerate(history[2:], 1)
                 if a != "stop"))


def continuation(history, cuts, round_index, level=0):
    if not cuts:
        return payoff(history)
    law = advance({history: F(1)}, cuts[0], round_index, level)
    return mean(law, lambda h: continuation(h, cuts[1:], round_index, level + 1))


class RecursiveTargetControls(unittest.TestCase):
    def test_every_node_keeps_joint_root_and_full_tail(self):
        for rare, schedule in product((F(1, 2), F(1, 101), F(1, 1000000)),
                                      ((1, 1, 1), (0, 1, 2), (2, 0, 1))):
            roots = {(0, 0): rare / 4, (0, 1): 3 * rare / 4,
                     (1, 0): (1 - rare) * F(2, 3), (1, 1): (1 - rare) / 3}
            for level in range(len(schedule)):
                tail = schedule[level:]
                values, backups = [], []
                for n in range(3):
                    # Re-root at a genuinely reached joint PBS, with the
                    # current round's prefix, then keep that round in the tail.
                    incoming = dict(roots)
                    for k in range(level):
                        incoming = advance(incoming, schedule[k], n, k)
                    cut_law = advance(incoming, tail[0], n, level)
                    epsilon = F(1, 8 * (level + 1))
                    exact, backed = {}, {}
                    for label in (0, 1, 2):  # absent-label total convention
                        exact[label] = mean(conditional(incoming, label),
                                            lambda h: continuation(h, tail, n, level))
                        backed[label] = mean(conditional(cut_law, label),
                                             lambda h: continuation(h, tail[1:], n,
                                                                    level + 1) + epsilon)
                        self.assertEqual(backed[label] - exact[label], epsilon)
                    values.append(exact)
                    backups.append(backed)
                for label in (0, 1, 2):
                    error = sum(v[label] for v in backups) / 3
                    error -= sum(v[label] for v in values) / 3
                    self.assertEqual(error, epsilon)
                self.assertEqual(sum(incoming.values()), 1)

    def test_cross_round_child_or_missing_tail_changes_target(self):
        roots = {(0, 0): F(1, 8), (0, 1): F(3, 8),
                 (1, 0): F(3, 8), (1, 1): F(1, 8)}
        same, wrong, truncated = [], [], []
        for n in range(3):
            cut_law = advance(roots, 1, n, 0)
            law = conditional(cut_law, 0)
            same.append(mean(law, lambda h: continuation(h, (1, 1), n, 1)))
            wrong.append(mean(law, lambda h: continuation(h, (1, 1), 2, 1)))
            truncated.append(mean(law, payoff))
        self.assertNotEqual(sum(same) / 3, sum(wrong) / 3)
        self.assertNotEqual(sum(same) / 3, sum(truncated) / 3)
        self.assertNotEqual(sum(same) / 3, same[-1])

    def test_parent_mean_does_not_flatten_child_iterations(self):
        # One value per parent round. Child solvers have different finite
        # budgets; flattening their samples changes the parent training target.
        child_values = [[F(-2), F(2)], [F(3), F(3), F(3)], [F(-1)]]
        parent = [sum(v) / len(v) for v in child_values]
        uniform = sum(parent) / len(parent)
        flattened = sum(sum(v) for v in child_values) / sum(map(len, child_values))
        self.assertEqual(uniform, F(2, 3))
        self.assertEqual(flattened, F(4, 3))
        self.assertNotEqual(uniform, flattened)

    def test_empty_schedule_and_early_stop_bypass_queries(self):
        roots = {(0, 0, "stop"): F(1, 3), (1, 1, "stop"): F(2, 3)}
        for label in (0, 1, 2):
            law = conditional(roots, label)
            for cuts in ((), (0,), (1, 2), (0, 1, 0, 2)):
                self.assertEqual(mean(law, lambda h: continuation(h, cuts, 7)),
                                 mean(law, payoff))
            self.assertEqual(advance(law, 3, 5, 1), law)


if __name__ == "__main__":
    unittest.main()
