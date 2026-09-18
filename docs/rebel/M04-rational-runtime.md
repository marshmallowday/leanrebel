# M04 exact Lean runtime cross-check

## Observed evidence

Source commit: `9de0eb35e50e39e42636d31a8caebd7fdb203012`.
GitHub Actions run: `35344865143`, job: `105598962403`.
Artifact: `10546339223` (contains `rebel-rational-runtime.json`).
The runtime step printed `RATIONAL_RUNTIME_PASS` on 2026-09-18 at 12:30:24 UTC.

The generic Lean `HistoryTable` solver, instantiated with the two-stage
hidden-type runtime table, was executed through `lake env lean --run`.
All 40 local action probabilities at each of T=0, T=1 and T=2 exactly matched
an independently implemented Python Fraction solver. The checker then used
its separate normal-form terminal enumeration to evaluate the actual
Lean-produced profiles against every one of 1024 pure local policies per player.
Own-action memory is included: each player has two first-stage and eight
second-stage information sets. The table retains 85 legal history prefixes.

| Completed rounds | Root value for player 0 | Best-response values (0,1) | Deviation gains (0,1) | NashConv |
|---|---|---|---|---|
| 0 | 1 | (1,1) | (0,2) | 2 |
| 1 | 1 | (1,1) | (0,2) | 2 |
| 2 | 0 | (0,1) | (0,1) | 1 |

T=1 averages only the unupdated round-zero fallback. T=0 separately returns
the fallback without pretending there is a probability law on an empty sample.
The 46 Python tests, including off-path counterfactual regret, wrong shared
iteration randomness, naive coordinate averaging and an effective alternating
update mutation, all passed in the same run.

## Precise scope

This is executable regression and independent exhaustive-response evidence,
not a proof that the runtime history/information encoding is the canonical
full-AOH game. The overall workflow at this source SHA failed later in
`RationalEvaluation.lean` at a list-map cast conversion; normal/slow lint and
the transitive axiom audit were therefore not completed on that source.
The cast conversion was repaired at `afe45211767c32bfe8badf5cc6d58c3ee959cbc6`.

General real CFR, its canonical approximate-Nash theorem and the real hidden-type
instance compiled in this run. Arithmetic refinement of rational regret matching
also compiled. General continuation, counterfactual and complete-iteration
refinement are being validated separately; none of these facts is inferred from
a successful runtime test. The runtime Row/Site encoding must still receive its
own checked decoding correspondence before this evidence can close M04.
