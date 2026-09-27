"""Primitive good-state rate controls; independent arithmetic, not Lean evidence."""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product
import unittest

from test_schedule_support import (
    BAD, GOOD_ROOT, IDENTITY, Kernel, Law, advance, enumerate_inputs,
)


def rate_bound(law: Law, kernels: tuple[Kernel, ...],
               events: tuple[frozenset[int], ...], bad: frozenset[int],
               rates: tuple[F, ...]) -> F:
    """Check the premises and charge only transitions before the last input."""
    if len(kernels) != len(events) or len(kernels) != len(rates):
        raise ValueError("one event and rate per stage required")
    if any(not event <= bad for event in events) or any(rate < 0 for rate in rates):
        raise ValueError("event containment and nonnegative rates required")
    for kernel, rate in zip(kernels, rates):
        advance(law, kernel)  # Validate every finite kernel without changing the input.
        for state, row in enumerate(kernel):
            if state not in bad and sum((row[y] for y in bad), F(0)) > rate:
                raise ValueError("good-state leakage exceeds supplied rate")
    return min(F(1), sum((law[x] for x in bad), F(0)) + sum(rates[:-1], F(0)))


STICKY: Kernel = ((F(1), F(0)), (F(1, 4), F(3, 4)))


class PrimitiveSupportTests(unittest.TestCase):
    def test_absorbing_failure_needs_no_rate_bound_at_bad_states(self) -> None:
        hit, visits = enumerate_inputs(GOOD_ROOT, (STICKY,) * 3, (BAD,) * 3)
        bound = rate_bound(GOOD_ROOT, (STICKY,) * 3, (BAD,) * 3, BAD, (F(1, 4),) * 3)
        self.assertEqual((hit, visits, bound), (F(7, 16), F(11, 16), F(1, 2)))
        self.assertGreater(STICKY[0][0], F(1, 4))
        self.assertLessEqual(hit, bound)
        self.assertGreater(visits, bound)  # This theorem is NOT a visit-count bound.

    def test_final_transition_is_not_observed(self) -> None:
        everything_bad: Kernel = ((F(1), F(0)),) * 2
        schedule = (IDENTITY, everything_bad)
        self.assertEqual(enumerate_inputs(GOOD_ROOT, schedule, (BAD,) * 2)[0], 0)
        self.assertEqual(rate_bound(GOOD_ROOT, schedule, (BAD,) * 2, BAD, (F(0), F(1))), 0)
        self.assertEqual(advance(GOOD_ROOT, everything_bad)[0], 1)

    def test_empty_and_singleton_boundaries_retain_initial_defect(self) -> None:
        bad_root = (F(1), F(0))
        self.assertEqual(enumerate_inputs(bad_root, (), ())[0], 0)
        self.assertEqual(rate_bound(bad_root, (), (), BAD, ()), 1)
        self.assertEqual(rate_bound(GOOD_ROOT, (STICKY,), (BAD,), BAD, (F(1, 4),)), 0)
        self.assertEqual(enumerate_inputs(bad_root, (STICKY,), (BAD,))[0], 1)

    def test_narrow_events_and_recovery_after_bad_states(self) -> None:
        root = (F(1, 3), F(2, 3))
        recovery: Kernel = ((F(0), F(1)), (F(0), F(1)))
        events = (frozenset(), BAD, BAD)
        schedule = (recovery, STICKY, STICKY)
        hit = enumerate_inputs(root, schedule, events)[0]
        bound = rate_bound(root, schedule, events, BAD, (F(0), F(1, 4), F(1, 4)))
        self.assertEqual(hit, F(1, 4))
        self.assertLessEqual(hit, bound)

    def test_private_model_pairing_is_not_a_visible_history_quotient(self) -> None:
        # 1 and 2 may share a visible history, but only model-memory state 2 leaks.
        law = (F(0), F(3, 4), F(1, 4))
        kernel = ((F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(1), F(0), F(0)))
        self.assertEqual(advance(law, kernel)[0], F(1, 4))
        with self.assertRaises(ValueError):
            rate_bound(law, (kernel,) * 2, (BAD,) * 2, BAD, (F(0), F(0)))

    def test_false_rate_and_event_premises_are_rejected(self) -> None:
        with self.assertRaises(ValueError):
            rate_bound(GOOD_ROOT, (STICKY,), (BAD,), BAD, (F(0),))
        with self.assertRaises(ValueError):
            rate_bound(GOOD_ROOT, (IDENTITY,), (frozenset({1}),), BAD, (F(0),))
        with self.assertRaises(ValueError):
            rate_bound(GOOD_ROOT, (IDENTITY,), (BAD,), BAD, (F(-1),))

    def test_exhaustive_inhomogeneous_good_state_rates(self) -> None:
        grid = (F(0), F(1, 2), F(1))
        kernels = tuple(((a, 1 - a), (b, 1 - b)) for a, b in product(grid, repeat=2))
        for mass, k1, k2, k3 in product(grid, kernels, kernels, kernels):
            law, schedule = (mass, 1 - mass), (k1, k2, k3)
            events = (BAD,) * 3
            hit = enumerate_inputs(law, schedule, events)[0]
            rates = tuple(kernel[1][0] for kernel in schedule)
            bound = rate_bound(law, schedule, events, BAD, rates)
            self.assertLessEqual(hit, bound)


if __name__ == '__main__':
    unittest.main()
