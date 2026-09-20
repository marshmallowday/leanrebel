# ReBeL status — M06 in progress; M05 accepted

## Active restart

Continue on `rebel/m06-refresh-checkpoint-20260921`; read its remote HEAD.
The proof source is `ae60d4105b67c478c23d594bca4cd7587c140ecb` on preserved
`rebel/m06-bounded-refresh-20260921`. The checkpoint adds only evidence docs,
leaving the proof source's running full validations undisturbed.
The validated inherited base was a39599e3b47b1e50ca78d5a6385aa24035d25738,
which already included the finite-child repair f4671e42. Do not replay old
failed patches or revert to earlier chat checkpoints. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. No force update or main integration.
M06-status-before-bounded-refresh.md preserves the exact inherited STATUS.

## Inspected exact-source validation

At ae60d410, target run 35535271115/job 106143057959 PASSED all 65 M06 targets
(3,320 Lake jobs), then all 27 supplemental module lints and 292 transitive
declaration audits. Every complete axiom record was inspected and lies within
propext, Classical.choice, Quot.sound. The four new modules account for 49
records, including generated equations/private helpers; the source adds 12
general theorems and seven example theorems. There are no error/warning records.
See M06-bounded-refresh-validation.md and M06-bounded-refresh-axioms.txt.

Source inventory 35535271079/job 106143057820 passed. Full repository CI
35535271071/job 106143096344 and full ReBeL compiler/lint/axiom run
35535271126/job 106143099577 are still running at this evidence checkpoint.
Re-read their final results before any original-obligation acceptance. The
ReBeL width, static architecture, ledger/inventory/fixture and independent
rational-runtime steps passed, but intermediate steps are not full success.
The new documentation head has separate runs, not the same proof-source jobs.

The inherited a39599e3 full CI and full ReBeL audit passed, with 173 modules
and 3,544 axiom records. Final-source offline tests pass all 76 Python cases,
ledger/inventory structure and line-width checks (503 Lean files). Original
3,054 coverage rows, every prior target/import and all dependency pins remain.
No compiler repair changed a statement, allowed axiom or validation setting.

## Constructed bounded-refresh execution

CFRDRefreshMix derives the actual carried-step/retained-tail expectation and
2*bound*rate replacement loss at every carried state. CFRDFiniteRefresh
computes fresh finite-budget candidates at the CURRENT carried MODEL PBS,
selects the candidate once privately with probability rate and otherwise keeps
the current complete profile. Missing model beliefs retain the current profile;
terminal and zero-fuel stages keep the no-query rule. Fuel and local comparison
premises are derived for an arbitrary finite schedule and actual forward laws.

CFRDFiniteRefreshSafety connects this execution to the actual noisy finite-child
outer CFR-D recurrence with the explicit lower bound
V_ref - (A*predictionError + C/sqrt(T) + 2*childLoss) - stageCount*2*bound*rate.
No child Nash, mass floor, local replacement or recursive-value certificate is
assumed. Candidate approximate Nash is proved separately at a present PBS;
the retain-old mixture is not claimed Nash at that same budget. The model PBS
is not equated to the unknown opponent's true distribution.

Controls cover positive actual replacement loss (exactly rate for a bad legal
candidate), arbitrary existing memory with missing beliefs, a live finite-PBS
candidate, zero-fuel stopping and a two-stage execution's fuel and comparisons.
The bad-candidate control is not presented as the finite solver's actual output.

## Remaining original M06 boundary

This is a BOUNDED-REFRESH VARIANT with an additional conservative penalty. At
large rates or many stages that penalty can make the bound vacuous. It is not
a proof that arbitrary independent re-solving is lossless and not a replacement
for the paper-faithful recursive test-time argument. The finite candidate is
still an adaptive real-arithmetic complete-plan normal-form reference, not
fixed-T information-set CFR or an executable numerical refinement.

Next close the original solver's recursive counterfactual/global-security
argument and its source correspondence without assuming that two Nash policies
preserve value against each fixed opponent. Keep prediction error, child loss,
outer finite-T error and optional replacement loss separate. Preserve the
printed and corrected Theorem 3 statements and all prior counterexamples.

SEARCH-CFRD/SEARCH-ERROR gain the explicit variant above; original parent rows
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No M06 completion or complete-framework acceptance is claimed.
