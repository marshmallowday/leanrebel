"""Independent rational controls for model-stored versus factual live PBSs.

These controls test conditioning and recurrence identity, not Lean compilation
or a claim that Nash accuracy forces posterior equality.
"""
from fractions import Fraction as F
from itertools import product
import unittest


def condition(law, predicate):
    mass = sum((p for h, p in law.items() if predicate(h)), F(0))
    if not mass:
        return None
    return {h: p / mass for h, p in law.items() if predicate(h) and p}


def bind(law, kernel):
    result = {}
    for root, mass in law.items():
        for h, p in kernel(root).items():
            result[h] = result.get(h, F(0)) + mass * p
    return {h: p for h, p in result.items() if p}


class StoredChildControls(unittest.TestCase):
    def test_public_phase_live_posterior_matches_every_parent_round(self):
        for rare, noise in product((F(1, 2), F(1, 101), F(1, 1000000)),
                                   (F(0), F(1, 8), F(-1, 8))):
            prior = {(0, 0): rare / 4, (0, 1): 3 * rare / 4,
                     (1, 0): (1 - rare) * F(2, 3), (1, 1): (1 - rare) / 3}
            for n in range(4):
                def step(root):
                    live = F(n + 1, 6) + noise
                    return {(root, "live", True): live,
                            (root, "terminal", False): 1 - live}
                parent_prefix = bind(prior, step)
                # The selected complete round preserves its actual trunk.
                model_prefix = bind(prior, step)
                for phase in ("live", "terminal", "absent"):
                    saved = condition(model_prefix, lambda h: h[1] == phase)
                    factual = condition(parent_prefix, lambda h: h[1] == phase and h[2])
                    if phase == "live":
                        self.assertEqual(saved, factual)
                        # Hidden correlation survives: do not replace by
                        # an independent product of private marginals.
                        self.assertEqual(saved[((0, 1), "live", True)], 3 * rare / 4)
                    else:
                        self.assertIsNone(factual)
                    if phase == "absent":
                        self.assertIsNone(saved)

    def test_unobservable_terminal_state_invalidates_public_live_equality(self):
        law = {("same", 0, True): F(1, 6), ("same", 1, True): F(1, 3),
               ("same", 2, False): F(1, 2)}
        saved = condition(law, lambda h: h[0] == "same")
        child = condition(law, lambda h: h[0] == "same" and h[2])
        self.assertNotEqual(saved, child)
        self.assertEqual(child, {("same", 0, True): F(1, 3),
                                 ("same", 1, True): F(2, 3)})
        # Existence of a live actual history does not remove the terminal
        # atom from the stored model posterior.
        self.assertIn(("same", 0, True), saved)
        self.assertIn(("same", 2, False), saved)

    def test_stored_prior_must_be_propagated_instead_of_reset(self):
        prior = {0: F(9, 10), 1: F(1, 10)}
        reset = {0: F(1, 2), 1: F(1, 2)}
        kernel = lambda h: {(h, "seen"): F(h + 1, 3),
                            (h, "other"): 1 - F(h + 1, 3)}
        saved = condition(bind(prior, kernel), lambda h: h[1] == "seen")
        restarted = condition(bind(reset, kernel), lambda h: h[1] == "seen")
        self.assertEqual(saved[(0, "seen")], F(9, 11))
        self.assertEqual(restarted[(0, "seen")], F(1, 3))
        self.assertNotEqual(saved, restarted)

    def test_actual_selected_round_not_average_or_new_round(self):
        first = {(0, "seen"): F(1, 10), (1, "seen"): F(3, 10),
                 (0, "other"): F(3, 5)}
        second = {(0, "seen"): F(3, 10), (1, "seen"): F(1, 10),
                  (1, "other"): F(3, 5)}
        mixed = {h: (first.get(h, 0) + second.get(h, 0)) / 2
                 for h in first.keys() | second.keys()}
        saved = condition(first, lambda h: h[1] == "seen")
        child = condition(first, lambda h: h[1] == "seen")
        wrong_round = condition(second, lambda h: h[1] == "seen")
        wrong_average = condition(mixed, lambda h: h[1] == "seen")
        self.assertEqual(saved, child)
        self.assertEqual(saved[(0, "seen")], F(1, 4))
        self.assertEqual(wrong_round[(0, "seen")], F(3, 4))
        self.assertEqual(wrong_average[(0, "seen")], F(1, 2))
        loss = F(1, 7)
        self.assertEqual(min(saved.values()) * loss, F(1, 28))
        self.assertNotEqual(min(wrong_average.values()) * loss, F(1, 28))

    def test_public_support_does_not_supply_hidden_history_support(self):
        model = {("seen", 0): F(1)}
        actual = {("seen", 0): F(1, 5), ("seen", 1): F(4, 5)}
        saved = condition(model, lambda h: h[0] == "seen")
        factual_unknown = condition(actual, lambda h: h[0] == "seen")
        self.assertNotEqual(saved, factual_unknown)
        self.assertNotIn(("seen", 1), saved)
        self.assertEqual(sum(p for h, p in actual.items() if h not in saved), F(4, 5))


if __name__ == "__main__":
    unittest.main()
