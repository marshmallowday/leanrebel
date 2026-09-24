# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-recursive-solver-20260924`.
It descends from repair751ad17af36d6ff4f3deea2c1ee513f10dc754d9 on preserved
`rebel/m06-structural-recursion-20260924`. Original source:
6f4cca8321d5d0d1daf143e8805321dd2ff1dcd9; prior review:
d86402210eae417c4114578cff1092fbaa216e86. Preserved nested source:
f9d4def18411b43fc14c508b079fadb0378bd178 on `rebel/m06-nested-depth-20260924`.
Main remains6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098 and is not a write target.
All repository access and commits use the GitHub plugin and existing fork CI.
Unverified edits and skipped audits are never compilation/validation evidence.

## Predecessor validation preserved

First-exit487aaedd passed M06run35941683756/job107450728931,
ReBeL35941683758/job107450798403, full35941683736/job107450816152 and
inventory35941683774. Earlier support recovery01245b31 is separately accepted.
Do not redo these support repairs, first-exit constructions or probability controls.

Finite-budget704e96ff6ed5b73b279191ea2d01629cc331e8d8 passed target35946360278/
job107465069923 including supplemental lint/axioms, full35946360214/
job107465224924 and inventory35946360322. Independent ReBeL35946360239/
job107465227645 was pending at its previous inspection.

Nestedf9d4def1 passed target35947018152/job107467137173 including declared
modules, normal/slow lint and transitive public/private axiom audit:
EXACT_LEAF_AXIOM_AUDIT_PASS; EXACT_LEAF_VALIDATION_PASS modules=88.
Inventory35947018259/job107467137512 and full35947018228/job107467419037
succeeded, including architecture phases, library lint and cleanliness.
ReBeL35947018175/job107467137458 was pending at its previous inspection.
See M06-nested-depth-validation.md for exact-source diagnostics.

## Accepted finite-history repair

At6f4cca83, target35950716593/job107478451359 failed because referenceBudget
used PublicRootType before the Fintype E.History section assumption was in scope.
Repair751ad17a moves that assumption to the first theorem needing it, preserving
earlier law-transfer generality and every proof body, bound and validation gate.
Its target35951624022/job107481206024 now SUCCEEDED: all declared target builds,
transitive public/private axiom audit and normal/slow lint, with
EXACT_LEAF_VALIDATION_PASS modules=89. Full35951624454/job107481206699 also
SUCCEEDED, including architecture phases, public-library lint and cleanliness.
Inventory35951624043/job107481205391 succeeded. Independent
ReBeL35951624061/job107481299594 was still in progress when last inspected.

## Budgeted parent and recursive candidate

Parenta01832184554acc81da55d991f118654ef5c5442 passed all declared target
compilation at35952219144/job107483131698. Its supplemental step was still
running before the successor push; do not infer whole validation from that build.
PBSComposedDepth connects the actual noisy parent to finite round allocation,
chance-root translation and original-PBS all-deviation Nash.

Recursivef375294fa122dcca803319d3466d0a96925e6ce5 failed target35952776340/
job107484869406. The equation elaborator inserted the implicit protocol binder
before the branch tactics, shifting the introduced model/instance/utility/PBS
arguments. A proof-level letI also triggered the style linter. The current
checkpoint makes the changing protocol EXPLICIT in both the solver family
and noise family and uses a proof-local let instance. The resulting downstream
elaboration failures are not accepted proofs. No heartbeat, linter or axiom gate
is disabled; no source proof placeholder is added.

The candidate now recurses on the strict tail of original cut lengths and proves
child accuracy by list induction. Empty schedules use only a legal zero-transition
fallback, not a hidden full-root solver. The same actual finite parent iterates
are privately sampled and decoded. Their original all-history law is equated to
the computed own-reach average against a fixed unknown opponent. The sampler
is installed in the canonical carried-PBS resolver and finite memory runner;
the selected profile retains its own propagated posterior. Missing beliefs and
zero execution fuel preserve the existing no-query behavior.

All three new modules remain registered in the analytic root, M06 targets and
unchanged supplemental public/private axiom and normal/slow lint checks.
The current candidate still needs its own exact-SHA compiler and audit evidence.
See M06-recursive-solver.md and M06-recursive-sampling.md.

## Scope and remaining original obligations

The allocator subtracts numerical and child errors before choosing finite T;
increasing T does not eliminate a nonzero fixed prediction error. Preserve the
positive-noise, nonempty-tail, randomized-deviation, hidden-type, empty-schedule,
zero-width-cut, absent-belief and zero-fuel controls; no test is removed.

Finish candidate validation. Separately derive source-level model-value drift,
useful first-exit/support-defect rates and discharge CarriedResolveStepBounds.
Private carried continuation is not independent repeated re-solving. No equality
of model/actual posterior, learned-network accuracy or executable numerical
refinement is claimed. Preserve printed/corrected Theorem3 distinctions.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
All accepted M05 evidence and original coverage/source qualifications remain.
