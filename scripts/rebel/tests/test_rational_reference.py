"""Adversarial exact tests for the full two-stage reference, independent of Lean."""
import sys
import unittest
from fractions import Fraction as Q
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import rational_reference as ref


class RationalReferenceTests(unittest.TestCase):
    def test_complete_histories_and_information_memory(self):
        self.assertEqual(len(ref.HISTORIES), 85)
        self.assertEqual(len(set(ref.HISTORIES)), 85)
        self.assertEqual(len(ref.SITES), 10)
        self.assertTrue(all(ref.FIBERS[key] for key in ref.KEYS))
        self.assertEqual(ref.information(0, (0, 0)), ref.information(0, (0, 1)))
        self.assertNotEqual(ref.information(0, (0, 0, 0, 0)),
                            ref.information(0, (0, 0, 1, 1)))

    def test_zero_one_round_and_negative_count(self):
        empty, _, average0 = ref.run(0)
        _, plays, average1 = ref.run(1)
        self.assertEqual(len(plays), 1)
        self.assertEqual(average0, {key: ref.fallback(*key) for key in ref.KEYS})
        self.assertEqual(average1, average0)
        self.assertEqual(plays[0], ref.profile_from_regrets(empty))
        with self.assertRaises(ValueError):
            ref.run(-1)

    def test_matcher_zero_negative_and_positive_parts(self):
        fallback = ref.pure(1)
        self.assertEqual(ref.regret_match((Q(0), Q(0)), fallback), fallback)
        self.assertEqual(ref.regret_match((Q(-2), Q(-1)), fallback), fallback)
        self.assertEqual(ref.regret_match((Q(2), Q(3)), fallback), (Q(2, 5), Q(3, 5)))
        self.assertEqual(ref.regret_match((Q(-2), Q(3)), fallback), ref.pure(1))

    def test_off_path_site_retains_counterfactual_regret(self):
        _, _, baseline = ref.run(0)
        profile = dict(baseline)
        for who, info in ref.KEYS:
            if info[0] == 1:
                profile[who, info] = ref.pure(1 if who == 0 else 0)
        site = (1, 0, 1, 0)
        histories = ref.FIBERS[1, site]
        self.assertTrue(all(ref.own_reach(profile, 1, h) == 0 for h in histories))
        self.assertTrue(all(ref.counterfactual_reach(profile, 1, h) > 0 for h in histories))
        self.assertGreater(ref.local_regret(profile, 1, site)[1], 0)

    def test_simultaneous_snapshot_differs_from_alternating_mutant(self):
        regrets, _, _ = ref.run(0)
        correct = ref.update(regrets, 0)
        mutant = dict(regrets)
        first_snapshot = ref.profile_from_regrets(regrets)
        # Player 1 is the initially losing player. Updating player 0 first is
        # an ineffective mutation at round zero because its policy stays put.
        for key in ref.KEYS:
            if key[0] == 1:
                mutant[key] = ref.local_regret(first_snapshot, *key)
        wrong_snapshot = ref.profile_from_regrets(mutant)
        for key in ref.KEYS:
            if key[0] == 0:
                mutant[key] = ref.local_regret(wrong_snapshot, *key)
        self.assertNotEqual(correct, mutant)
        self.assertEqual(correct[0, (0, 0)][1], -1)
        self.assertEqual(mutant[0, (0, 0)][1], 1)

    def test_own_reach_average_is_not_coordinate_mean(self):
        first = {key: ref.pure(0) for key in ref.KEYS}
        second = {key: ref.pure(1) for key in ref.KEYS}
        average = ref.weighted_average([first, second])
        self.assertEqual(average[0, (0, 0)], (Q(1, 2), Q(1, 2)))
        self.assertEqual(average[0, (1, 0, 0, 1)], ref.pure(0))
        self.assertNotEqual(average[0, (1, 0, 0, 1)], (Q(1, 2), Q(1, 2)))

    def test_shared_iteration_randomness_is_not_independent_average(self):
        # Same iteration for both players always matches first-round actions.
        # Private independent iteration draws match only half the time.
        first = {key: ref.pure(0) for key in ref.KEYS}
        second = {key: ref.pure(1) for key in ref.KEYS}
        average = ref.weighted_average([first, second])
        shared_match = Q(1)
        independent_match = sum((average[0, (0, 0)][a] * average[1, (0, 0)][a]
                                 for a in ref.BITS), Q(0))
        self.assertEqual(independent_match, Q(1, 2))
        self.assertNotEqual(shared_match, independent_match)

    def test_recursive_and_independent_terminal_evaluators_agree(self):
        _, plays, average = ref.run(3)
        for profile in plays + [average]:
            for law in profile.values():
                self.assertEqual(sum(law), 1)
                self.assertTrue(all(weight >= 0 for weight in law))
            for who in ref.BITS:
                self.assertEqual(ref.value(profile, who), ref.normal_form_payoff(profile, who))
            self.assertEqual(ref.value(profile, 0) + ref.value(profile, 1), 0)

    def test_all_1024_policies_per_player_are_checked(self):
        _, _, average = ref.run(3)
        self.assertEqual(1 << len(ref.SITES), 1024)
        for who in ref.BITS:
            best, mask = ref.brute_force_best_response(average, who)
            self.assertGreaterEqual(best, ref.normal_form_payoff(average, who))
            index = {info: n for n, info in enumerate(ref.SITES)}
            self.assertEqual(best, ref.normal_form_payoff(average, who,
                             lambda info: (mask >> index[info]) & 1))


if __name__ == '__main__':
    unittest.main()
