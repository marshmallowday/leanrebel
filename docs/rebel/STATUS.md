# ReBeL status — M06 in progress; M05 accepted

## Resume point

Resume from remote HEAD of rebel/m06-reference-reweight-20260924.
Recovery parent: 8783159df16bbbb505ee0e810d142d2793fba593, based on
66a8b9ecd01a5dbbf120ce1b56479ccec6c1dad7. All remote access and commits
use the GitHub plugin. Main is not a write target.

This checkpoint recovers the previously unapplied CFRDReferenceReweight and
Examples.CFRDReferenceReweight modules. Their exact-SHA compiler, lint and
transitive axiom checks are PENDING, not accepted from source inspection.
All 124 prior M06 targets and 86 prior supplemental modules remain, with two
added to each list. See M06-reference-reweight.md for assumptions and controls,
and M06-reference-reweight-validation.md for checkpoint evidence.

## Accepted predecessors: do not redo

Fresh-chain proof source 46126f37dbaa83a2f064f511e9617843d0ce308a is preserved
on rebel/m06-fresh-chain-20260924, with reviewed documentation at 66a8b9ec.
Independent ReBeL run 35964794487/job 107520978527 now SUCCEEDED, including
all-ReBeL compile/lint/transitive axioms, rational runtime, independent pure
responses and tracked-file cleanliness. The older pending note is superseded.
M06 run 35964794524/job 107520892185 and full CI run 35964794518/job
107520892015 also succeeded. Exact-source audit: 86 modules, 1291 declarations.
See M06-fresh-chain-validation.md and M06-fresh-chain.md for the theorem scope,
compiler repairs and positive/hostile controls. The chain repeats actual child
solves at one fixed cut, deriving reference preservation, final local quality,
measured drift accumulation and noisy-parent root security.

Composition 639e3962, structural recursion a4246792 and review a5e0700f remain
accepted and preserved on their original branches. Their records are in
M06-drift-composition-validation.md and M06-recursive-validation.md.
Finite budget 704e96ff, nested f9d4def1 and repair 751ad17a are not repeated;
see M06-depth-budget-integration.md, M06-nested-depth-validation.md and
M06-structural-recovery.md. Preserve all accepted M05 results.

## Remaining original obligations

Information-local OLD-from-NEW density is structural, not implied by scalar
Nash accuracy or arbitrary later PBS changes. Derive useful posterior
transport/support/first-exit and fresh-model-value drift bounds, then
CarriedResolveStepBounds for the actual repeated independent solves.
A measured drift sum is not a vanishing-rate theorem; unchanged conditionals
do not imply unchanged continuation values. Do not equate modeled PBS with
actual unknown-opponent posterior, erase finite-T or positive prediction
error, or infer learned-network accuracy. Preserve native private-iteration
sampling versus coherent-plan distinctions and the printed/corrected Theorem 3.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
