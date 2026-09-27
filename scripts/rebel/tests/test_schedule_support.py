"""Exact finite-schedule controls; arithmetic fixtures, not Lean verification.

The forward recurrence and independent path enumeration both observe inputs to
scheduled stages. Full state indices can encode private memory/model pairing.
No model posterior is substituted for the actual prefix law.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product
import unittest

Law = tuple[F, ...]
Kernel = tuple[Law, ...]


def validate_law(law: Law) -> None:
    if not law or any(weight < 0 for weight in law) or sum(law) != 1:
        raise ValueError("expected a nonnegative normalized finite law")


def advance(law: Law, kernel: Kernel) -> Law:
    validate_law(law)
    if len(kernel) != len(law):
        raise ValueError("kernel domain mismatch")
    for row in kernel:
        validate_law(row)
        if len(row) != len(law):
            raise ValueError("kernel codomain mismatch")
    return tuple(sum((law[x] * kernel[x][y] for x in range(len(law))), F(0))
                 for y in range(len(law)))


def enumerate_inputs(law: Law, kernels: tuple[Kernel, ...],
                     events: tuple[frozenset[int], ...]) -> tuple[F, F]:
    """Enumerate entire trajectories independently of the forward recursion."""
    if len(kernels) != len(events):
        raise ValueError("one event per stage is required")
    paths = [((state,), mass) for state, mass in enumerate(law)]
    for kernel in kernels:
        paths = [(path + (nxt,), mass * row_mass)
                 for path, mass in paths
                 for nxt, row_mass in enumerate(kernel[path[-1]]) if row_mass]
    hit, visits = F(0), F(0)
    for path, mass in paths:
        count = sum(path[index] in event for index, event in enumerate(events))
        hit += mass * bool(count)
        visits += mass * count
    return hit, visits


def forward_charges(law: Law, kernels: tuple[Kernel, ...],
                    events: tuple[frozenset[int], ...],
                    unsupported: frozenset[int]) -> tuple[F, F]:
    """Use exact one-step output defects as conservative charge witnesses.

    This tests the composition algebra, not the ReBeL primitive-charge theorem.
    The latter is separately implemented and audited in Lean.
    """
    if len(kernels) != len(events) or any(not e <= unsupported for e in events):
        raise ValueError("events must be contained in unsupported states")
    bound = sum((law[x] for x in unsupported), F(0))
    visits = F(0)
    for kernel, event in zip(kernels, events):
        visits += sum((law[x] for x in event), F(0))
        charge = tuple(sum((row[y] for y in unsupported), F(0)) for row in kernel)
        bound += sum((law[x] * charge[x] for x in range(len(law))), F(0))
        law = advance(law, kernel)
    return bound, visits


BAD = frozenset({0})
GOOD_ROOT = (F(0), F(1))
QUARTER: Kernel = ((F(1, 4), F(3, 4)),) * 2
IDENTITY: Kernel = ((F(1), F(0)), (F(0), F(1)))


class ScheduleSupportTests(unittest.TestCase):
    def test_empty_schedule_has_no_hit_even_with_bad_initial_state(self) -> None:
        bad_root = (F(1), F(0))
        self.assertEqual(enumerate_inputs(bad_root, (), ()), (0, 0))
        self.assertEqual(forward_charges(bad_root, (), (), BAD), (1, 0))

    def test_final_output_is_not_an_extra_scheduled_input(self) -> None:
        self.assertEqual(enumerate_inputs(GOOD_ROOT, (QUARTER,), (BAD,)), (0, 0))
        self.assertEqual(advance(GOOD_ROOT, QUARTER)[0], F(1, 4))
        self.assertEqual(enumerate_inputs(GOOD_ROOT, (QUARTER,) * 2, (BAD,) * 2),
                         (F(1, 4), F(1, 4)))

    def test_first_hit_is_not_visit_mass_or_reused_single_seed(self) -> None:
        hit, visits = enumerate_inputs(GOOD_ROOT, (QUARTER,) * 3, (BAD,) * 3)
        self.assertEqual((hit, visits), (F(7, 16), F(1, 2)))
        self.assertNotEqual(hit, visits)
        self.assertNotEqual(hit, F(1, 4))  # Reusing one draw across both inputs.
        bound, forward_visits = forward_charges(GOOD_ROOT, (QUARTER,) * 3,
                                                (BAD,) * 3, BAD)
        self.assertEqual((bound, forward_visits), (F(3, 4), visits))
        self.assertLessEqual(hit, min(1, bound))

    def test_repeated_bad_visits_need_the_probability_cap(self) -> None:
        root = (F(1), F(0))
        hit, visits = enumerate_inputs(root, (IDENTITY,) * 3, (BAD,) * 3)
        bound, _ = forward_charges(root, (IDENTITY,) * 3, (BAD,) * 3, BAD)
        self.assertEqual((hit, visits, bound), (1, 3, 4))
        self.assertEqual(min(1, bound), hit)

    def test_strict_event_subset_retains_missing_and_stopped_boundary(self) -> None:
        # Index 0: unsupported but stopped; 1: missing; 2: live supported.
        root = (F(1, 4), F(1, 2), F(1, 4))
        kernel = tuple(tuple(F(x == y) for y in range(3)) for x in range(3))
        events = (frozenset(),) * 2
        self.assertEqual(enumerate_inputs(root, (kernel,) * 2, events), (0, 0))
        self.assertEqual(forward_charges(root, (kernel,) * 2, events,
                                         frozenset({0, 1})), (F(9, 4), 0))
        with self.assertRaises(ValueError):
            forward_charges(root, (kernel,), (frozenset({2}),), frozenset({0, 1}))

    def test_model_prefix_cannot_replace_actual_private_pairing(self) -> None:
        # Indices 1 and 2 have the same visible history but different stored models.
        root = (F(1), F(0), F(0))
        first = ((F(0), F(1, 4), F(3, 4)),) * 3
        second = ((F(0), F(0), F(1)), (F(1), F(0), F(0)), (F(0), F(0), F(1)))
        third = tuple(tuple(F(x == y) for y in range(3)) for x in range(3))
        events = (frozenset(), frozenset(), BAD)
        hit, visits = enumerate_inputs(root, (first, second, third), events)
        self.assertEqual((hit, visits), (F(1, 4), F(1, 4)))
        actual_prefix = advance(root, first)
        pooled_model_prefix = (F(0), F(0), F(1))
        self.assertEqual(advance(actual_prefix, second)[0], F(1, 4))
        self.assertEqual(advance(pooled_model_prefix, second)[0], 0)

    def test_exhaustive_inhomogeneous_three_stage_composition(self) -> None:
        grid = (F(0), F(1, 2), F(1))
        kernels = tuple(((a, 1 - a), (b, 1 - b)) for a, b in product(grid, repeat=2))
        for mass, k1, k2, k3 in product(grid, kernels, kernels, kernels):
            law, schedule = (mass, 1 - mass), (k1, k2, k3)
            events = (BAD,) * 3
            hit, visits = enumerate_inputs(law, schedule, events)
            bound, forward_visits = forward_charges(law, schedule, events, BAD)
            self.assertEqual(visits, forward_visits)
            self.assertLessEqual(hit, visits)
            self.assertLessEqual(visits, bound)
            self.assertLessEqual(hit, min(1, bound))


if __name__ == '__main__':
    unittest.main()
