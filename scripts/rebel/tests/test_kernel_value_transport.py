"""Exact arithmetic controls; these do not replace Lean compilation or semantics."""
from fractions import Fraction as F
from itertools import product
import unittest


def expect(law, value):
    return sum((p * x for p, x in zip(law, value)), F(0))


def variation(old, fresh):
    return sum((abs(p - q) for p, q in zip(old, fresh)), F(0))


def gap(law, payoffs, chosen):
    values = [expect(law, action) for action in payoffs]
    return max(values) - values[chosen]


class KernelValueTransportTests(unittest.TestCase):
    def test_exhaustive_two_history_kernels(self):
        weights = [F(i, 4) for i in range(5)]
        cases = 0
        for p, q in product(weights, repeat=2):
            old, fresh = (p, 1 - p), (q, 1 - q)
            cost = variation(old, fresh)
            for entries in product((F(-1), F(0), F(1)), repeat=4):
                payoffs = (entries[:2], entries[2:])
                old_values = [expect(old, a) for a in payoffs]
                fresh_values = [expect(fresh, a) for a in payoffs]
                self.assertLessEqual(abs(max(old_values) - max(fresh_values)), cost)
                for chosen in range(2):
                    self.assertLessEqual(abs(gap(fresh, payoffs, chosen) -
                                             gap(old, payoffs, chosen)), 2 * cost)
                    cases += 1
        self.assertEqual(cases, 4050)

    def test_gap_factor_two_is_sharp(self):
        old, fresh = (F(1, 2), F(1, 2)), (F(3, 4), F(1, 4))
        payoffs = ((F(-1), F(1)), (F(1), F(-1)))
        self.assertEqual(gap(old, payoffs, 0), 0)
        self.assertEqual(gap(fresh, payoffs, 0), 2 * variation(old, fresh))
        self.assertGreater(gap(fresh, payoffs, 0), variation(old, fresh))

    def test_new_only_atom_is_not_dropped(self):
        old, fresh = (F(1), F(0)), (F(0), F(1))
        self.assertEqual(variation(old, fresh), 2)
        old_support_only = sum(abs(p - q) for p, q in zip(old, fresh) if p)
        self.assertEqual(old_support_only, 1)
        self.assertGreater(abs(expect(old, (-1, 1)) - expect(fresh, (-1, 1))),
                           old_support_only)

    def test_joint_query_cannot_be_reproductized(self):
        joint = (F(1, 2), F(0), F(0), F(1, 2))
        independent = (F(1, 4),) * 4
        paired_cost = (F(2), F(0), F(0), F(2))
        self.assertEqual(expect(joint, paired_cost), 2)
        self.assertEqual(expect(independent, paired_cost), 1)

    def test_selected_kernel_cost_is_already_conditional(self):
        event_mass, native_budget, bound = F(1, 4), F(1, 16), F(2)
        selected_variation = F(1, 8)
        allowance = native_budget / event_mass + 2 * bound * selected_variation
        self.assertEqual(allowance, F(3, 4))
        self.assertNotEqual(allowance,
                            (native_budget + 2 * bound * selected_variation) / event_mass)

    def test_zero_variation_recovers_native_budget(self):
        law = (F(2, 3), F(1, 3))
        self.assertEqual(variation(law, law), 0)
        self.assertEqual(F(1, 8) / F(1, 2) + 4 * variation(law, law), F(1, 4))

    def test_same_kernel_does_not_allow_changed_opponent(self):
        law = (F(1, 2), F(1, 2))
        first_values, second_values = ((F(0), F(0)),), ((F(1), F(1)),)
        self.assertEqual(variation(law, law), 0)
        self.assertEqual(max(expect(law, a) for a in second_values) -
                         max(expect(law, a) for a in first_values), 1)

    def test_type_readout_affects_the_actual_pairing(self):
        kernels = ((F(1), F(0)), (F(0), F(1)))
        self.assertEqual(sum(variation(kernels[i], kernels[i]) for i in range(2)), 0)
        self.assertEqual(sum(variation(kernels[i], kernels[1-i]) for i in range(2)), 4)


if __name__ == '__main__':
    unittest.main()
