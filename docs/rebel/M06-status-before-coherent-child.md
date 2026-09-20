# ReBeL status — M06 in progress; M05 accepted

## Active restart checkpoint

Continue on `rebel/m06-envelope-checkpoint-20260921`; read its actual remote HEAD.
The complete proof source is `5aeb2d18027e6c89b0a5889fbca7192f322d6783`, retained
on `rebel/m06-counterfactual-envelope-20260921`. This checkpoint changes only
evidence documents and does not disturb that source's running full checks.
The inherited base is ce55384a01cd91b6d8070314074f46690462a25f. All seven saved
implementation/repair commits are descendants with no rewritten history.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098, accepted through M05.
M06-status-before-envelope.md preserves the previous STATUS byte-for-byte.

## Exact-source validation actually inspected

At 5aeb2d18, run 35539104136 / job 106153413336 PASSED all steps: 68 targets,
3,394 Lake build jobs, then supplemental validation of 30 modules and 324
complete unique transitive-axiom records. Every recorded module lint passed.
All axiom sets are contained in propext, Classical.choice, Quot.sound.
There are no compiler error or warning records. The three new modules own
32 audited records including generated/private helpers, nine general theorems
and seven example theorems. See M06-envelope-validation.md and
M06-envelope-axioms.txt for exact log/archive hashes and declaration records.

Source inventory 35539104109 / 106153374527 passed. Full repository CI
35539104112 / 106153412444 and full ReBeL compiler/lint/axiom run
35539104111 / 106153374451 remain in progress at this recording checkpoint.
Re-read their exact-source final results before any acceptance. The latter's
width, static architecture, ledger/inventory/fixtures and independent rational
runtime checks already passed; these do not imply full-workflow success.

All six changed code/registration/auditor files match the exact source snapshot.
All 76 existing Python tests, coverage/inventory structure and line-width
checks (506 Lean files) passed. These do not replace Lean proof validation.
Original 3,054 coverage rows, prior imports/targets, pins and audit gates remain.
The base ce55384a full repository and ReBeL checks have now succeeded, with
177 modules and 3,593 inspected axiom records; this is separate baseline evidence.

## New source-directed bridge

CFRDResolveEnvelope compares resolved OPPONENT payoff with the incumbent MODEL
continuation at positive opponent-reference information/live fibers. Perfect
recall reweights the bound to the actual unknown-opponent prefix, including
off-model reach. Stopped fibers contribute zero. Model-value numerical accuracy
and a conditional child-value upper bound combine additively on the same kernel.

CFRDEnvelopeSafety then combines the focal player's full regret with the
opponent's PREFIX-ONLY regret. Both are instantiated from the actual CFR-D
recurrence. The resulting lower bound has
A*predictionError + C/sqrt(T) + focalChildLoss + envelopeLoss,
without a switching-probability penalty or fixed-opponent no-loss premise.
This does NOT remove the earlier penalty for arbitrary independent re-solving:
the new local envelope is still a sufficient solver obligation, not something
assumed by the source paper or automatically supplied by two Nash policies.

The live HiddenTypes instance retains the actual finite-child noisy trace
(numerical bias 1/8, child loss 1/4) and derives the envelope from its constructed
child contract. Separate matrix controls show that an opponent model ceiling
can coexist with losing one unit of fixed-opponent exploitation, and that a
bad legal candidate breaks the ceiling. A same-PBS mixed-game control gives
two exact Nash choices with different positive-mass type values. This refutes
a proof shortcut, not coherent ReBeL recursion. Zero-fuel stopping is preserved.

## Remaining original M06 construction and coverage

Construct a COHERENT recursive child policy/value family at the actual carried
model PBSs and relate it to the parent's sampled continuation. Existing delayed
child sampling and cfrDChildResolve_eq can transfer the same family; independently
reselecting Nash is not a substitute. Derive the local opponent envelope or
prove an appropriate aggregate recursive guarantee. The sufficient pointwise
condition need not be necessary for an original-algorithm proof.
The finite child remains an adaptive real-arithmetic complete-plan reference,
not the paper's information-set CFR or an executable numerical refinement.
M06-envelope-semantics.md records the construction boundary and source plan.

SEARCH-CFRD/SEARCH-ERROR gain the bridge above, but original SEARCH-FRONTIER,
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 parent obligations remain pending.
Keep prediction, child, finite-outer and optional replacement errors separate,
keep printed/corrected Theorem 3 distinct, and retain every prior counterexample.
No M06 completion or complete-framework acceptance is claimed.
