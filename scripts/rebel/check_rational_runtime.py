"""Execute Lean's rational solver and cross-check its complete output.

This deliberately compares separate implementations. The independent normal
form checker evaluates the actual Lean-produced profile against all 1024 pure
policies of each player. Passing is regression evidence, not a refinement proof.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
from fractions import Fraction as Q
from pathlib import Path

import rational_reference as ref

ROOT = Path(__file__).resolve().parents[2]
ROUNDS = (0, 1, 2)


def execute() -> str:
    directory = ROOT / '.lake' / 'rebel'
    directory.mkdir(parents=True, exist_ok=True)
    probe = directory / 'RationalRuntime.lean'
    probe.write_text(
        'import GameTheory.ReBeL.Rational.HiddenTypes\n'
        'def main : IO Unit := do\n'
        '  for rounds in [0, 1, 2] do\n'
        '    GameTheory.ReBeL.Rational.HiddenTypes.printProfile rounds\n', encoding='utf-8')
    completed = subprocess.run(['lake', 'env', 'lean', '--run', str(probe)],
                               cwd=ROOT, text=True, capture_output=True, timeout=300)
    if completed.returncode != 0:
        raise RuntimeError(f'Lean runtime failed:\n{completed.stdout}\n{completed.stderr}')
    return completed.stdout


def parse(text: str) -> dict[int, ref.Policy]:
    profiles: dict[int, ref.Policy] = {rounds: {} for rounds in ROUNDS}
    for line in text.splitlines():
        fields = line.strip().split(',')
        if len(fields) != 10:
            raise ValueError(f'Unexpected runtime output: {line!r}')
        rounds, who, stage, own_type, own_first, result, n0, d0, n1, d1 = map(int, fields)
        if rounds not in profiles or who not in ref.BITS or stage not in ref.BITS:
            raise ValueError(f'Invalid output coordinates: {fields}')
        if d0 <= 0 or d1 <= 0:
            raise ValueError('Nonpositive rational denominator')
        info = (0, own_type) if stage == 0 else (1, own_type, own_first, result)
        key = (who, info)
        if key not in ref.KEYS or key in profiles[rounds]:
            raise ValueError(f'Duplicate or unknown information coordinate: {key}')
        law = (Q(n0, d0), Q(n1, d1))
        if sum(law) != 1 or min(law) < 0:
            raise ValueError(f'Invalid probability law: {law}')
        profiles[rounds][key] = law
    for rounds, profile in profiles.items():
        if set(profile) != set(ref.KEYS):
            raise ValueError(f'Incomplete profile for T={rounds}')
    return profiles


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    output = execute()
    profiles = parse(output)
    records = []
    for rounds in ROUNDS:
        actual = profiles[rounds]
        expected = ref.run(rounds)[2]
        if actual != expected:
            mismatch = {str(k): {'lean': list(map(str, actual[k])),
                                 'reference': list(map(str, expected[k]))}
                        for k in actual if actual[k] != expected[k]}
            raise AssertionError(f'Exact Lean/reference mismatch at T={rounds}: {mismatch}')
        value = ref.normal_form_payoff(actual, 0)
        best = [ref.brute_force_best_response(actual, who) for who in ref.BITS]
        gains = [best[0][0] - value, best[1][0] + value]
        records.append({'rounds': rounds, 'compared_local_probabilities': 40,
                        'root_value': str(value), 'best_response_values': [str(b[0]) for b in best],
                        'best_response_masks': [b[1] for b in best],
                        'deviation_gains': [str(g) for g in gains],
                        'nash_conv': str(sum(gains, Q(0))), 'pure_policies_per_player': 1024})
    report = {'source_sha': os.environ.get('GITHUB_SHA'), 'status': 'pass',
              'scope': 'actual Lean runtime cross-check; not the full semantic refinement',
              'histories': 85, 'records': records, 'lean_output': output}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))
    print('RATIONAL_RUNTIME_PASS')


if __name__ == '__main__':
    main()
