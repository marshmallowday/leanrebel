"""Exact two-stage hidden-type CFR and an independent normal-form checker.

This is a regression oracle for the Lean numerical frontend, not a substitute
for its kernel-checked Protocol refinement. Every observation key preserves
own-action memory and excludes the opponent's private type. The full reference
prior is the canonical example's uniform distribution on four type pairs.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
from typing import Callable

Info = tuple[int, ...]
History = tuple[int, ...]
Law = tuple[Q, Q]
Policy = dict[tuple[int, Info], Law]
Regrets = dict[tuple[int, Info], Law]
BITS = (0, 1)
TYPES = tuple(product(BITS, repeat=2))
JOINTS = tuple(product(BITS, repeat=2))
HISTORIES: tuple[History, ...] = (
    ((),)
    + tuple(TYPES)
    + tuple(t + a for t in TYPES for a in JOINTS)
    + tuple(t + a + b for t in TYPES for a in JOINTS for b in JOINTS)
)


def information(who: int, history: History) -> Info:
    """An active full-AOH key; inactive observations have no decision table."""
    if len(history) == 2:
        return (0, history[who])
    if len(history) == 4:
        return (1, history[who], history[2 + who], int(history[2] == history[3]))
    raise ValueError('Only active decision histories have information keys')


SITES: tuple[Info, ...] = tuple((0, t) for t in BITS) + tuple(
    (1, t, a, won) for t, a, won in product(BITS, repeat=3)
)
KEYS = tuple((who, info) for who in BITS for info in SITES)
FIBERS = {
    (who, info): tuple(h for h in HISTORIES if len(h) in (2, 4) and information(who, h) == info)
    for who, info in KEYS
}


def pure(action: int) -> Law:
    return (Q(1), Q(0)) if action == 0 else (Q(0), Q(1))


def fallback(who: int, info: Info) -> Law:
    # The canonical baselinePlan: first false; then player 0 guesses own type,
    # while player 1 selects true. This is a fallback, not a policy restriction.
    return pure(0 if info[0] == 0 else info[1] if who == 0 else 1)


def regret_match(score: Law, default: Law) -> Law:
    positive = tuple(max(q, Q(0)) for q in score)
    mass = sum(positive, Q(0))
    return (positive[0] / mass, positive[1] / mass) if mass > 0 else default


def profile_from_regrets(regrets: Regrets) -> Policy:
    return {key: regret_match(regrets[key], fallback(*key)) for key in KEYS}


def own_reach(policy: Policy, who: int, history: History) -> Q:
    if len(history) == 2:
        return Q(1)
    if len(history) == 4:
        return policy[who, information(who, history[:2])][history[2 + who]]
    raise ValueError('Expected an active prefix')


def counterfactual_reach(policy: Policy, who: int, history: History) -> Q:
    return Q(1, 4) * own_reach(policy, 1 - who, history)


def terminal_payoff(who: int, history: History) -> Q:
    first = 1 if history[2] == history[3] else -1
    final = 1 if (history[4] == history[1]) == bool(history[5]) else -1
    return Q((first + final) * (1 if who == 0 else -1))


def value(policy: Policy, who: int, history: History = ()) -> Q:
    """Recursive exact chance / simultaneous continuation evaluation."""
    if not history:
        return sum((value(policy, who, types) for types in TYPES), Q(0)) / 4
    if len(history) == 6:
        return terminal_payoff(who, history)
    laws = tuple(policy[player, information(player, history)] for player in BITS)
    return sum((laws[0][a] * laws[1][b] * value(policy, who, history + (a, b))
                for a, b in JOINTS if laws[0][a] and laws[1][b]), Q(0))


def local_regret(policy: Policy, who: int, info: Info) -> Law:
    fiber = FIBERS[who, info]
    baseline = sum((counterfactual_reach(policy, who, h) * value(policy, who, h)
                    for h in fiber), Q(0))
    gains = []
    for action in BITS:
        alternative = dict(policy)
        alternative[who, info] = pure(action)
        gains.append(sum((counterfactual_reach(policy, who, h) * value(alternative, who, h)
                          for h in fiber), Q(0)) - baseline)
    return (gains[0], gains[1])


def update(regrets: Regrets, round_index: int) -> Regrets:
    """All local updates read one immutable previous-round profile."""
    snapshot = profile_from_regrets(regrets)
    result = {}
    for key in KEYS:
        gain = local_regret(snapshot, *key)
        result[key] = tuple((round_index * regrets[key][a] + gain[a]) / (round_index + 1)
                            for a in BITS)
    return result


def weighted_average(plays: list[Policy]) -> Policy:
    average = {}
    for who, info in KEYS:
        representative = FIBERS[who, info][0]
        weights = [own_reach(play, who, representative) for play in plays]
        mass = sum(weights, Q(0))
        average[who, info] = (
            tuple(sum((w * play[who, info][a] for w, play in zip(weights, plays)), Q(0)) / mass
                  for a in BITS) if mass else fallback(who, info)
        )
    return average


def run(rounds: int) -> tuple[Regrets, list[Policy], Policy]:
    if rounds < 0:
        raise ValueError('Iteration count must be nonnegative')
    regrets = {key: (Q(0), Q(0)) for key in KEYS}
    plays = []
    for round_index in range(rounds):
        plays.append(profile_from_regrets(regrets))
        regrets = update(regrets, round_index)
    return regrets, plays, weighted_average(plays)


def normal_form_payoff(policy: Policy, who: int,
                       target: Callable[[Info], int] | None = None) -> Q:
    """Independent terminal-tuple summation. Never calls value/local_regret.

    When target is supplied, its choices are deterministic functions of the
    complete local information key. All of its ten decisions remain available.
    """
    total = Q(0)
    for t0, t1, a0, a1, b0, b1 in product(BITS, repeat=6):
        types = (t0, t1)
        first = (a0, a1)
        last = (b0, b1)
        win1 = int(a0 == a1)
        probability = Q(1, 4)
        for player in BITS:
            info1 = (0, types[player])
            info2 = (1, types[player], first[player], win1)
            if target is not None and player == who:
                probability *= int(first[player] == target(info1)) * int(last[player] == target(info2))
            else:
                probability *= policy[player, info1][first[player]] * policy[player, info2][last[player]]
        reward = (2 * win1 - 1) + (1 if (b0 == t1) == bool(b1) else -1)
        total += probability * reward * (1 if who == 0 else -1)
    return total


def brute_force_best_response(policy: Policy, who: int) -> tuple[Q, int]:
    """Enumerate all 2^10 complete pure policies, not the smaller Plan helper."""
    site_index = {info: index for index, info in enumerate(SITES)}
    best = None
    best_mask = 0
    for mask in range(1 << len(SITES)):
        score = normal_form_payoff(policy, who,
                                  lambda info, mask=mask: (mask >> site_index[info]) & 1)
        if best is None or score > best:
            best, best_mask = score, mask
    assert best is not None
    return best, best_mask


def report(rounds: int) -> dict[str, object]:
    _, plays, average = run(rounds)
    root = value(average, 0)
    best = [brute_force_best_response(average, who) for who in BITS]
    gains = [best[0][0] - root, best[1][0] + root]
    return {'rounds': rounds, 'completed_rounds': len(plays), 'histories': len(HISTORIES),
            'information_sets_per_player': len(SITES), 'pure_policies_per_player': 1 << len(SITES),
            'root_value': str(root), 'best_response_values': [str(item[0]) for item in best],
            'best_response_masks': [item[1] for item in best],
            'deviation_gains': [str(gain) for gain in gains], 'nash_conv': str(sum(gains, Q(0))),
            'proof_status': 'independent exact regression; not a Lean refinement proof'}


if __name__ == '__main__':
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds', type=int, default=3)
    args = parser.parse_args()
    print(json.dumps(report(args.rounds), indent=2))
