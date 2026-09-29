"""Independent exact controls for decoding an already sampled rooted child.

These finite kernels and matrix profiles do not execute CFR or the Lean solver.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def add(law, key, mass):
    law[key] = law.get(key, F(0)) + mass


def bind(law, kernel):
    result = {}
    for state, mass in law.items():
        for target, chance in kernel(state).items():
            add(result, target, mass * chance)
    return result


def push(law, read):
    return bind(law, lambda state: {read(state): F(1)})


def original_step(state, policies):
    hidden, actions = state
    if len(actions) == 2:
        return {state: F(1)}
    who = len(actions)
    p = policies[who][hidden[who]]
    return {(hidden, actions + (0,)): 1 - p, (hidden, actions + (1,)): p}


def run(law, kernel, fuel):
    for _ in range(fuel):
        law = bind(law, kernel)
    return law


def root_step(state, policies):
    # The wrapper keeps the outer cut and full history; no root is redrawn.
    cut, original, trace = state
    if len(original[1]) == 2:
        return {state: F(1)}
    return push(original_step(original, policies),
                lambda target: (cut, target, trace + (target[1][-1],)))


def utility(matrix, row, column):
    return sum((pr * pc * matrix[r][c]
                for r, pr in enumerate((1 - row, row))
                for c, pc in enumerate((1 - column, column))), F(0))


def nash_error(matrix, row, column):
    value = utility(matrix, row, column)
    return max(F(0), *(utility(matrix, r, column) - value for r in (0, 1)),
               *(value - utility(matrix, row, c) for c in (0, 1)))


class RootedChildDecodeTests(unittest.TestCase):
    def test_child_joint_posterior_is_not_outer_reset_or_product(self):
        outer = {(bits, ()): F(1, 4) for bits in product((0, 1), repeat=2)}
        child = {((0, 0), ()): F(3, 4), ((1, 1), ()): F(1, 4)}
        rooted = {(7, state, ()): mass for state, mass in child.items()}
        decoded = push(rooted, lambda state: state[1])
        self.assertEqual(decoded, child)
        self.assertNotEqual(decoded, outer)
        joint_match = sum(mass for (bits, _), mass in decoded.items() if bits[0] == bits[1])
        independent_match = F(3, 4) ** 2 + F(1, 4) ** 2
        self.assertEqual(joint_match, 1)
        self.assertLess(independent_match, joint_match)

    def test_all_local_profiles_and_deviations_preserve_full_law(self):
        child = {((0, 0), ()): F(1, 10), ((0, 1), ()): F(2, 10),
                 ((1, 0), ()): F(3, 10), ((1, 1), ()): F(4, 10)}
        rooted = {(4, state, ()): mass for state, mass in child.items()}
        grid = (F(0), F(1, 3), F(1))
        cases = 0
        for values in product(grid, repeat=4):
            policies = (values[:2], values[2:])
            for fuel in (0, 1, 2):
                native = run(rooted, lambda state: root_step(state, policies), fuel)
                original = run(child, lambda state: original_step(state, policies), fuel)
                self.assertEqual(push(native, lambda state: state[1]), original)
                # Both players' full local replacement grids occur in the enumeration.
                self.assertEqual(sum(native.values()), 1)
                cases += 1
        self.assertEqual(cases, 243)

    def test_clock_zero_and_terminal_do_not_repeat_administrative_draw(self):
        child = {((1, 0), ()): F(1)}
        policies = ((F(1), F(1)), (F(0), F(0)))
        self.assertEqual(run(child, lambda h: original_step(h, policies), 0), child)
        once = run(child, lambda h: original_step(h, policies), 1)
        twice = run(child, lambda h: original_step(h, policies), 2)
        self.assertNotEqual(once, twice)
        self.assertEqual(run(twice, lambda h: original_step(h, policies), 5), twice)
        # A spurious administrative unit would either skip an original action or
        # redraw a prior; both disagree with the already sampled child semantics.
        self.assertNotEqual(once, child)
        outer = {((0, 0), ()): F(1)}
        self.assertNotEqual(run(outer, lambda h: original_step(h, policies), 1), once)

    def test_independent_nash_computations_compare_scalars_not_policies(self):
        matrix = ((F(2), F(-1)), (F(-2), F(1)))
        grid = (F(0), F(1, 2), F(1))
        for r1, c1, r2, c2 in product(grid, repeat=4):
            e1, e2 = nash_error(matrix, r1, c1), nash_error(matrix, r2, c2)
            self.assertLessEqual(abs(utility(matrix, r1, c1) - utility(matrix, r2, c2)),
                                 e1 + e2)
        # Two protocol-dependent routines can choose different exact equilibria.
        flat = ((F(0), F(0)), (F(0), F(0)))
        self.assertEqual(nash_error(flat, 0, 0), 0)
        self.assertEqual(nash_error(flat, 1, 1), 0)
        self.assertEqual(utility(flat, 0, 0), utility(flat, 1, 1))
        self.assertNotEqual((0, 0), (1, 1))
        # An action-independent late reward also requires a common horizon.
        self.assertNotEqual(F(0), F(2))

    def test_private_draw_retention_security_and_seed_blindness(self):
        matching = ((F(1), F(-1)), (F(-1), F(1)))
        for opponent in (F(0), F(1, 7), F(1, 2), F(1)):
            retained_mean = sum(F(1, 2) * utility(matching, pure, opponent)
                                for pure in (0, 1))
            self.assertEqual(retained_mean, utility(matching, F(1, 2), opponent))
            self.assertEqual(retained_mean, 0)
        seed_aware = sum(F(1, 2) * utility(matching, seed, 1 - seed) for seed in (0, 1))
        self.assertEqual(seed_aware, -1)
        for p in (F(1, 5), F(1, 2), F(4, 5)):
            same_draw = {(0, 0): 1 - p, (1, 1): p}
            redrawn = {(a, b): pa * pb
                       for a, pa in enumerate((1 - p, p))
                       for b, pb in enumerate((1 - p, p))}
            self.assertNotEqual(same_draw, redrawn)
            self.assertEqual(sum(w for (a, b), w in same_draw.items() if a == b), 1)
            self.assertLess(sum(w for (a, b), w in redrawn.items() if a == b), 1)


if __name__ == "__main__":
    unittest.main()
