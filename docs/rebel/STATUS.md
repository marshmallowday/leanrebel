# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-recursive-solver-20260924`.
This descends from repair751ad17af36d6ff4f3deea2c1ee513f10dc754d9 on the preserved
`rebel/m06-structural-recursion-20260924` branch. Its original source is
6f4cca8321d5d0d1daf143e8805321dd2ff1dcd9; prior review is
d86402210eae417c4114578cff1092fbaa216e86. The preserved nested source remains
f9d4def18411b43fc14c508b079fadb0378bd178 on `rebel/m06-nested-depth-20260924`.
Main remains6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098 and is not a write target.
All remote reads and writes use the GitHub plugin and the existing fork CI
compiler loop. Unverified edits are not compilation evidence.

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

## Structural repair and budgeted parent

Inspected target35950716593/job107478451359 at6f4cca83: only the new composed
child failed. Its referenceBudget used PublicRootType before the required
Fintype E.History instance entered scope. Repair751ad17a moves that assumption
to the first theorem requiring it, preserving earlier law-transfer generality.
No proof body, gate or tolerance was changed. Its target35951624022/
job107481206024, ReBeL35951624061/job107481299594 and full35951624454/
job107481206699 were in progress at the last inspection; source inventory
35951624043/job107481205391 succeeded. Recheck exact runs before acceptance.

PBSComposedDepth now connects a computational child to the actual noisy parent,
finite positive round allocation, chance-root translation and original-PBS
all-deviation Nash. The smaller solver accuracy is an explicit premise, NOT a
recursive implementation by naming it. Next discharge it by structural induction
on a finite cut schedule with zero-transition base and positive-noise controls.
See M06-recursive-solver.md. The new module is included in the analytic root,
all M06 targets, and unchanged supplemental lint/public-private axiom auditing.
This candidate requires its own exact-SHA compiler/audit evidence.

## Scope and remaining original obligations

The allocator subtracts fixed numerical and child errors before choosing T;
increasing T does not eliminate nonzero fixed prediction error. Earlier nested
code installs one depth-limited child per parent update, with full-root CFR as
its deepest backend. Preserve all hidden-type controls: positive outer/inner
errors, nonempty child continuation, randomized deviations, impossible public
observations and zero-fuel fallback.

Finish structural recursion and validation. Separately derive source-level
model-value drift and useful first-exit/support-defect rates and discharge
CarriedResolveStepBounds. Private carried continuation is not independent
repeated re-solving. No model/actual posterior identity, learned-network accuracy
or executable numerical-refinement theorem is claimed. Preserve positive errors,
finite T, zero-reach completion and printed/corrected Theorem3 distinctions.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
All accepted M05 evidence and original coverage/source qualifications remain.
