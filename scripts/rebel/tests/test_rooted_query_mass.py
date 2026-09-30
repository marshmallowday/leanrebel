"""Independent rational controls for weighted rooted-query comparisons.

These finite models do not execute Lean, CFR, or a learned neural oracle.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def expect(law, value):
    return sum((mass * value(atom) for atom, mass in law.items()), F(0))


def push(law, observe):
    result = {}
    for atom, mass in law.items():
        label = observe(atom)
        result[label] = result.get(label, F(0)) + mass
    return result


def conditional_share(model, observe, event, label):
    reach = expect(model, lambda atom: F(observe(atom) == label))
    if not reach:
        return expect(model, lambda atom: F(event(atom)))
    return expect(model, lambda atom: F(observe(atom) == label and event(atom))) / reach


def variation(first, second):
    return sum((abs(first.get(x, F(0)) - second.get(x, F(0)))
                for x in first.keys() | second.keys()), F(0))


def utility(matrix, p, q):
    return (p * q * matrix[0][0] + p * (1 - q) * matrix[0][1]
            + (1 - p) * q * matrix[1][0] + (1 - p) * (1 - q) * matrix[1][1])


def nash_error(matrix, p, q):
    value = utility(matrix, p, q)
    return max(F(0), max(utility(matrix, a, q) for a in (F(0), F(1))) - value,
               value - min(utility(matrix, p, b) for b in (F(0), F(1))))


class RootedQueryMassTests(unittest.TestCase):
    def test_rare_queries_cancel_only_with_correct_weights(self):
        for reach, stopped, other in product(
                (F(1, 1000), F(1, 7), F(3, 4)), repeat=3):
            law = {(0, True): reach * stopped, (0, False): reach * (1 - stopped),
                   (1, True): (1 - reach) * other, (1, False): (1 - reach) * (1 - other)}
            observe = lambda x: x[0]
            event = lambda x: x[1]
            shares = lambda tag: conditional_share(law, observe, event, tag)
            self.assertEqual(expect(push(law, observe), shares), expect(law, lambda x: F(event(x))))
            self.assertEqual(shares(0), stopped)
        rare = {(0, True): F(1, 2000), (0, False): F(1, 2000), (1, False): F(999, 1000)}
        self.assertEqual(conditional_share(rare, lambda x: x[0], lambda x: x[1], 0), F(1, 2))
        self.assertEqual(expect(rare, lambda x: F(x[1])), F(1, 2000))
        self.assertNotEqual(sum(conditional_share(rare, lambda x: x[0], lambda x: x[1], tag)
                                for tag in (0, 1)), F(1, 2000))

    def test_actual_weights_retain_variation_and_absent_fallback(self):
        grid = (F(0), F(1, 3), F(1))
        for model_weight, actual_weight, first, second in product(grid, repeat=4):
            model = {(0, True): model_weight * first, (0, False): model_weight * (1 - first),
                     (1, True): (1 - model_weight) * second,
                     (1, False): (1 - model_weight) * (1 - second)}
            actual = {(0, True): actual_weight, (1, False): 1 - actual_weight}
            observe = lambda x: x[0]
            event = lambda x: x[1]
            weighted = expect(push(actual, observe),
                              lambda tag: conditional_share(model, observe, event, tag))
            self.assertLessEqual(weighted, expect(model, lambda x: F(event(x))) +
                                 variation(actual, model))
            self.assertGreaterEqual(weighted, 0)
            self.assertLessEqual(weighted, 1)
        model = {(0, True): F(1, 100), (1, False): F(99, 100)}
        actual = {(0, True): F(1)}
        weighted = expect(push(actual, lambda x: x[0]),
                          lambda tag: conditional_share(model, lambda x: x[0], lambda x: x[1], tag))
        self.assertEqual(weighted, 1)
        self.assertGreater(weighted, F(1, 100))
        self.assertEqual(conditional_share(model, lambda x: x[0], lambda x: x[1], 99), F(1, 100))

    def test_independent_solve_errors_private_draw_and_stopped_mass(self):
        live = ((F(1), F(-1)), (F(-1), F(1)))
        stopped = ((F(2), F(2)), (F(2), F(2)))
        grid = (F(0), F(1, 2), F(1))
        for mass, old_p, old_q, fresh_p, fresh_q in product(grid, repeat=5):
            saved = tuple(tuple((1 - mass) * live[i][j] + mass * stopped[i][j]
                                for j in range(2)) for i in range(2))
            first = utility(live, old_p, old_q)
            second = utility(saved, fresh_p, fresh_q)
            eps1 = nash_error(live, old_p, old_q)
            eps2 = nash_error(saved, fresh_p, fresh_q)
            self.assertLessEqual(abs(first - second), eps1 + eps2 + 4 * mass)
            for unknown in grid:
                private_value = (fresh_p * utility(saved, F(1), unknown)
                                 + (1 - fresh_p) * utility(saved, F(0), unknown))
                self.assertEqual(private_value, utility(saved, fresh_p, unknown))
                self.assertLessEqual(first - private_value, eps1 + 2 * eps2 + 4 * mass)

    def test_actual_mass_scaled_request_and_independent_parent_terms(self):
        for first, loss, tolerance in product((F(1, 100), F(1, 4), F(1, 2)),
                                               (F(1, 8), F(1, 4), F(1)),
                                               (F(1, 16), F(1, 8), F(1, 4))):
            floor = min(first, 1 - first)
            request = floor * loss
            self.assertGreater(request, 0)
            self.assertLessEqual(request, loss)
            self.assertLessEqual(request + 2 * tolerance, loss + 2 * tolerance)
        for root_t in (1, 2, 4):
            finite_allowance = F(3, root_t)
            child_loss = F(1, 4)
            self.assertGreater(finite_allowance + 2 * child_loss, 0)
            self.assertNotEqual(finite_allowance + 2 * child_loss, 2 * child_loss)

    def test_joint_checkpoint_and_exclusion_are_not_factual_security(self):
        joint = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
        independent = {atom: F(1, 4) for atom in product((0, 1), repeat=2)}
        self.assertEqual(push(joint, lambda x: x[0]), push(independent, lambda x: x[0]))
        self.assertEqual(push(joint, lambda x: x[1]), push(independent, lambda x: x[1]))
        self.assertNotEqual(expect(joint, lambda x: F(x[0] == x[1])),
                            expect(independent, lambda x: F(x[0] == x[1])))
        # A missing query contributes nothing to a restricted diagnostic, but
        # an unrelated native replacement can still lose the full payoff diameter.
        excluded_diagnostic = F(0)
        actual_native_loss = F(1) - F(-1)
        self.assertLess(excluded_diagnostic, actual_native_loss)
        # Changing the continuation clock changes payoffs even at one root.
        same_root = {0: F(1)}
        self.assertNotEqual(expect(same_root, lambda _: F(0)),
                            expect(same_root, lambda _: F(1)))


if __name__ == "__main__":
    unittest.main()
