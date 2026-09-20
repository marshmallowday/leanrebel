# ReBeL status — M06 in progress; M05 accepted

## Active restart checkpoint

Resume on `rebel/m06-finite-child-checkpoint-20260920`; read its actual remote HEAD.
The complete proof source is `f4671e429e7a221999e661f862e15f38d2ade700`, preserved on
`rebel/m06-finite-child-20260920`. This evidence checkpoint changes documentation
only, leaving the source branch's running full validations undisturbed.
Main stays `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`, accepted through M05.
The source at restart was 919213d6, not the older c16beb4d chat checkpoint.
No history was rewritten. M06-status-before-finite-child.md preserves its STATUS
byte-for-byte (blob d88f3dc9fadad19f48c31f6d55c8b99a397011f9).

## Exact-source validation inspected

At f4671e42, targeted run `35517749018`, job `106096437386`, PASSED all steps:
61 declared targets, 3,316 Lake build jobs, then supplemental transitive axiom
checks for 243 declarations in 23 modules and all 23 normal/slow module lints.
All complete axiom records were inspected, including private declarations and
multiline records. Every set is contained in `propext`, `Classical.choice`,
`Quot.sound`. No error or warning record occurs in the successful target log.
See M06-finite-child-validation.md and M06-finite-child-axioms.txt.

Source inventory also passed: `35517749009` / `106096437327`.
At this recording checkpoint, full repository CI `35517749006` / `106096472731`
and full ReBeL compiler/lint/axiom run `35517749020` / `106096471791` remain
in progress. Re-read their final results and artifacts. Supplemental success
is not full-workflow success or M06 acceptance. The documentation head has its
own checks, separate from the recorded proof source.

The exact Actions snapshot matches all changed proof and registration files.
All 76 existing Python tests passed with warnings treated as errors, as did
coverage and inventory structure checks. All 499 non-Experimental Lean files
satisfy the unchanged width limit. No source file or old target was removed;
original coverage, dependencies, negative controls and M00-M05 evidence remain.

## New proved finite-child integration

Four modules add 14 general theorems and seven new example theorems.
CFRDFiniteChild computes one finite normal-form regret-matching solve at each
actual factual live PBS, retaining its learned trunk through a public-prefix
splice. Complete played and unilateral-deviation laws transfer approximate
Nash, not merely an equality of played means.
CFRDFiniteContinuation reconstructs the reference type game from the actual
child posterior. Its minimum positive atom supplies a common finite budget
for all supported types. The existing constructed response covers zero-own-
reach types. No child equilibrium, positive mass floor, probability budget or
leaf-quality inequality is supplied as an assumption.
CFRDFiniteDriver consumes these responses in the actual noisy outer recurrence,
deriving numerical accuracy, child loss, approximate Nash and selected-policy
carried security with `A*error+B/sqrt(T)+2*loss`, where child loss is positive.
The seven controls include a live child, factual absence, zero remaining fuel,
the all-query contract, the actual recurrence and numerical bias 1/8 distinct
from child tolerance 1/4. The bias does not claim that every learning trace changes.

The inherited Boolean update control was repaired at 838123ba and passed its
own target/axiom/lint run 35516637178/job 106093582774. The d6db5e46 integration
then exposed an underspecified error-budget argument; f4671e42 states that
budget and posterior explicitly without changing the theorem's assumptions.

## Remaining M06 boundary and next work

The finite child is an adaptive real-arithmetic COMPLETE-PLAN normal-form
reference. It is not fixed-T information-set child CFR or an executable rational
refinement. Its posterior-dependent horizon may be enormous; no global positive
mass floor or finite-time zero child loss is asserted. M06-finite-child.md
records the variant scope and the coverage journal.

Next construct fresh recursive re-solving at the actual carried PBSs and
transfer security through that execution. Current privateCarriedContinue keeps
the selected complete policy. Neither this theorem nor approximate child Nash
alone licenses independent equilibrium replacement. Preserve the existing
replacement counterexamples and prove the resolver's required local comparison
or a stronger appropriate global guarantee, rather than supplying the final
safety inequality as data. Keep the paper's information-set variant distinct.

Numerical prediction error, finite child loss and outer finite-T error remain
separate. The numerical bound is not a guarantee about arbitrary neural training.
Keep printed and corrected Theorem 3 distinct. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 original parents remain pending. No M06 completion
or main integration is claimed by this verified intermediate dependency slice.
