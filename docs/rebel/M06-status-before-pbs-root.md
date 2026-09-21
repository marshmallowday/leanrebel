# ReBeL status — M06 in progress; M05 accepted

## Active restart checkpoint

Continue on `rebel/m06-coherent-checkpoint-20260921`; read its actual remote HEAD.
The complete proof source is `93b60fbdc3fe6539a7688124baa9be80b86602c1`, retained
on `rebel/m06-coherent-recursion-20260921`. This checkpoint changes evidence
and STATUS only, leaving the proof source's full verification undisturbed.
The actual inherited base was ff7f61510c38a5681c06a7431a7811e3f6fbcbf7;
older failed repairs are already inherited or superseded. Do not replay them.
All seven implementation/restart/repair commits are descendants, without
force updates or history rewriting. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098, accepted through M05.
M06-status-before-coherent-child.md preserves the inherited STATUS byte-for-byte.

## Inspected exact-source validation

At 93b60fbd, target run `35545208144`, job `106169798608`, PASSED every step:
73 declared targets, 3,399 Lake build jobs, all 35 supplemental module lints,
and 356 complete unique transitive-axiom records. Every axiom list was checked
against only propext, Classical.choice and Quot.sound. No Lean error or warning
record occurs. The five new modules own 32 audited records, 14 general theorems
and eight example theorems. M06-coherent-child-validation.md records exact
source/archive/log hashes and failures; M06-coherent-child-axioms.txt is an
explicitly labelled normalized excerpt containing all 32 new-module records.

The exact source snapshot matches the five new Lean files and the three
registration/auditor files. All 76 existing Python tests pass with warnings
as errors, as do ledger/inventory structure and width checks (511 Lean files).
All original imports/targets and 3,054 coverage rows remain. Dependencies,
workflows, allowed axioms and architecture gates are byte-unchanged.

Full repository CI `35545208101` / `106169800893` and full ReBeL
`35545208160` / `106169767571` remain running at this recording checkpoint.
The latter's width, static architecture, ledger/inventory/fixtures and rational
Lean runtime checks have passed. These intermediate steps and supplemental
success are not full-workflow success. Re-read exact-source final results.
The evidence head has separate checks. No M06 acceptance or main integration.

The inherited ff7f6151 full CI and full ReBeL validation passed, with 180 modules
and 3,625 inspected allowed-axiom records. The single-cut intermediate e965412c
also passed its separate target/supplemental run (33 modules, 346 records),
but had an umbrella import typo not exercised by that target. It is fixed in
the final source. The stage proof also required definitional reduction and
removal of a forbidden transport tactic; no statement or gate was weakened.

## Constructed coherent execution refinement

CFRDCoherentDraw actually samples legal deterministic finite plans from the
same computed behavioral profile. Each unilateral history law equals its source
at EVERY legal root against any unknown behavioral opponent, including off-model
roots. The resolver preserves stopping and derives the opponent-reference
envelope from the same parent's child contract.
CFRDFiniteCoherent instantiates the actual perturbed outer CFR-D recurrence
and its constructed finite posterior-budgeted children, without a supplied
child Nash, mass floor, probability budget or continuation-quality certificate.

CFRDCoherentStages retains the original private parent index, all subsequent
draws and the canonical model-belief state. It redraws from that same family
at each active stage. For any finite schedule covering the remaining fuel,
the whole execution law equals the parent's continuation. Its finite-solver
security bound is A*predictionError+C/sqrt(T)+2*childLoss, with no switching-rate
or stage-count penalty. This is an aggregate law, not individual pure-plan
safety or no loss relative to every previously sampled pure plan.

Eight controls include a genuinely randomized source unequal to every sampled
pure profile, a live off-model history, zero fuel, actual biased finite-child
law/envelope/security, and two live strategic rounds separated by zero fuel.
The general multi-stage theorem covers arbitrary private memory and absent
model beliefs. The model law is never equated to the unknown opponent's true law.

## Remaining original M06 construction and coverage

This is a refinement of one FIXED computed family, not independent solving of
a different game at a later PBS. It does not identify finite predrawing with
uniform child-CFR-iteration sampling. The original recursive information-set
CFR policy/value family and its correspondence to the parent continuation
still need construction. Existing delayed-child-sampling APIs remain relevant;
independent Nash reselection and per-draw safety are not valid shortcuts.
The underlying finite child remains an adaptive real-arithmetic complete-plan
reference, not the paper's fixed-T information-set variant or executable refinement.

M06-coherent-child.md records this scope and coverage journal. Original
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 parents remain pending.
Preserve prediction error, positive child loss, outer finite-T error and the
separate bounded-refresh variant. Keep printed/corrected Theorem 3 distinct
and retain all existing counterexamples. No complete-framework acceptance.
