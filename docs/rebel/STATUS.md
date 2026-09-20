# ReBeL status — M06 in progress; M05 accepted

## Active restart point

Continue on `rebel/m06-conditional-checkpoint-20260920`; read its remote HEAD.
Its proof source is `af8b63282a49cdfb68df411e5527b6ba3e288d42` on the preserved
`rebel/m06-conditional-loss-20260920` branch. The evidence updates contain no
Lean or dependency changes. All work descends from the checked restart
`b5e15493d6efdc4fa641aeb690e40b24a0764d11`; do not replay older recovery stages.
Main stays `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`, accepted through M05.
M06-status-before-conditional-loss.md preserves the preceding driver STATUS
with identical Git blob `bba1393b0b6cccbaabf9dc6552ac612f023d720c`.

## Exact-source verified dependency slice

On af8b6328, target run `35508389830`, job `106071929602`, PASSED all 51 targets
(3,306 Lake jobs) and the supplemental 13-module validation. All 113 complete
transitive declaration records were inspected and use only `propext`,
`Classical.choice`, `Quot.sound`; all 13 normal/slow module lints passed.
The target log contains no error or warning records. This supplements, rather
than replaces, full repository and ReBeL acceptance checks.

Full repository CI on the SAME proof source has now PASSED: run `35508389747`,
job `106071929220`. Build, reuse-signature checks, Phase 1/2/3 architecture and
reachability audits, full public-library lint and tracked cleanliness all
succeeded. This updates the earlier in-progress observation in
M06-conditional-loss-validation.md without changing the proof source or gates.
Source inventory `35508389752` / `106071929279` also passed.

Full ReBeL `35508389751` / `106071965121` still runs at this update. Re-read its
actual final result and artifact before promoting any original obligation.
No M06 acceptance or main integration is claimed. See
M06-conditional-loss-validation.md and M06-conditional-loss-axioms.txt for
source hashes, run IDs and scoped evidence. The documentation head has its
own CI, separate from the recorded proof source's successful jobs.

The exact Actions source snapshot matches all six changed code/registration/
audit files. All 76 existing Python tests and ledger/inventory structural
checks passed on that snapshot. The original 3,054 expanded rows and all
inherited imports, targets, dependency pins and negative controls are retained.
All 489 non-Experimental Lean sources satisfy the unchanged line-width bound.

## New proof and controls

PBSApproximateOptimality provides four conditional-gap lemmas and a finite-
plan approximate-Nash realization theorem. A type of probability p has
p*gap <= epsilon; only a supported type admits the epsilon/p bound. The
explicit budget epsilon <= p*loss gives the desired conditional loss.
Finite mixed-plan approximate Nash transfers to canonical behavioral PBS
Nash without increasing epsilon and covers all behavioral future deviations.

CFRDApproximateLeaf connects these probability budgets and constructed
zero-own-reach responses through legal public splicing and the actual
reference table to CFRDLeafOptimal at the specified loss. It has three new
general theorems. Its remaining factual approximate-Nash premise is not a
conditional-value inequality or a claimed implemented child algorithm.

Eight compiled example theorems include canonical approximate Nash with root
error p but conditional gain one for arbitrarily small p, exact root Nash at
p=0 with an unconstrained omitted type, and a genuine live HiddenTypes
application of the new leaf contract. The last example specializes the
existing exact child to zero root error; it is not finite-child CFR.

## Inherited verification resolved

The baseline b5e15493 full ReBeL run `35503671838` / `106059741567` succeeded:
161 modules and 3,394 inspected transitive axiom records. The earlier
0b6d3f36 full CI `35503252425` / `106058634035` succeeded, but its ReBeL
`35503252397` was cancelled. These are distinct exact-source observations,
not a relabeling of the cancelled run. The validation document records hashes.

## Remaining M06 construction and coverage

Construct a finite-iteration child solver at the actual PBS/finiteBeliefForm
and derive its error AND probability budgets. The new realization theorem
supplies only its finite-plan-to-behavioral step. Do not infer uniform typewise
loss from root epsilon-Nash or assume a global positive PBS mass floor.
Then construct fresh recursive re-solving at the actual carried PBSs and
transfer its guarantees to the outer depth-limited solver. The exact/noisy
drivers still use their previously documented noncomputable exact children.

Keep numerical prediction error, child loss, optional replacement loss and
outer finite-T error separate, and preserve printed/corrected Theorem 3.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain open.
The updated coverage journal is in M06-conditional-loss.md. No original
source row, evidence or gate is deleted or promoted by this partial result.
