# ReBeL status — M06 in progress; M05 accepted

## Resume point

Resume from the remote HEAD of `rebel/m06-recursive-reviewed-20260924`.
This review checkpoint changes DOCUMENTATION ONLY relative to proof source
`a42467929bbedb0f26bd100e5915d5743ec9025d`, preserved at
`rebel/m06-recursive-solver-20260924`. The separate branch prevents this
recording commit from cancelling that exact source's independent ReBeL run.
Read its latest CI before any next proof edit. Do not redo accepted recursion.

The proof branch descends from repair751ad17af36d6ff4f3deea2c1ee513f10dc754d9
on `rebel/m06-structural-recursion-20260924`; original source was
6f4cca8321d5d0d1daf143e8805321dd2ff1dcd9. Preserved nested source is
f9d4def18411b43fc14c508b079fadb0378bd178 on `rebel/m06-nested-depth-20260924`.
Main remains6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098 and is not a write target.
All repository access and commits use the GitHub plugin and existing fork CI.
Unverified edits and skipped/cancelled audits are never accepted evidence.

## Exact-source validation at a4246792

M06 target35954274909/job107489146383 SUCCEEDED. All declared targets,
including all three new proof/control modules, compiled. The complete job log
was inspected: EXACT_LEAF_AXIOM_AUDIT_PASS declarations=961 and
EXACT_LEAF_VALIDATION_PASS modules=92. Every registered module passed normal
Batteries lint and slow defLemma lint. The transitive axiom audit includes public,
private and generated declarations, with the unchanged three-axiom whitelist.

Full35954275026/job107489156548 SUCCEEDED: complete library build, inventory and
compiler-resolved reuse signatures, architecture Phases1/2/3 and reachability
probes, public-library lint, and tracked-file cleanliness. Inventory35954274949/
job107489146497 and exact-source snapshot35954274920/job107489146729 SUCCEEDED.

Independent ReBeL35954274920/job107489146886 was still IN PROGRESS at this
recording checkpoint. Its line-width gate, static architecture, ledger/inventory,
adversarial fixtures and rational runtime with independently checked pure
responses had succeeded; the all-ReBeL compile/lint/axiom step was still running.
Do not turn this pending whole-workflow result into a success claim. The original
proof branch is left untouched so this run can finish without cancellation.
The target and full-CI successes above are independently completed evidence.

## Accepted predecessors — do not redo

First-exit487aaedd passed M06run35941683756/job107450728931,
ReBeL35941683758/job107450798403, full35941683736/job107450816152 and
inventory35941683774. Support recovery01245b31 is separately accepted.

Finite-budget704e96ff6ed5b73b279191ea2d01629cc331e8d8 passed target35946360278/
job107465069923 including supplemental lint/axioms, full35946360214/
job107465224924 and inventory35946360322. Independent ReBeL35946360239/
job107465227645 is confirmed SUCCESS, including the entire ReBeL proof surface,
rational runtime and independent responses, architecture and cleanliness.

Nestedf9d4def1 passed target35947018152/job107467137173 with normal/slow lint and
public/private transitive axiom audit: modules=88. Full35947018228/job107467419037
and inventory35947018259/job107467137512 succeeded. Independent ReBeL35947018175/
job107467137458 is confirmed SUCCESS. See M06-nested-depth-validation.md.

Repair751ad17a moved the existing finite-history instance before its first use in
referenceBudget. No theorem body or bound changed. Target35951624022/
job107481206024 passed all named builds and supplemental normal/slow lint with
public/private axiom audit: modules=89. Full35951624454/job107481206699 and
inventory35951624043/job107481205391 succeeded. Independent ReBeL35951624061/
job107481299594 is NOW CONFIRMED SUCCESS, including all-module compile/lint/axioms,
rational runtime with independent responses, and tracked-file cleanliness.

## Newly derived recursive solver and actual private sampling

PBSComposedDepth connects the actual noisy parent to finite round allocation,
chance-root translation and original-PBS all-deviation Nash. PBSRecursiveDepth
recurses on strict tails of finite lists of original cut lengths. Each current
parent obtains factual JOINT child PBSs, allocates positive mass-scaled targets,
and computes a nonempty finite iteration count. The zero-transition base uses
the legal fallback, not a hidden full-root CFR. Child accuracy is proved by list
induction, never supplied as a Nash/recursive-accuracy certificate in solver data.
The remaining numerical-noise premise is explicit; a concrete allowance-sized
nonzero family is proved bounded and positive at every positive allocation.

The actual parent iterations, with those same recursive children, supply private
uniform sampling. Their complete original-history law agrees with the own-reach
average against every fixed unknown opponent; individual iterations need not be
Nash. The canonical carried resolver pairs the selected profile with the model
posterior it actually propagates. Missing beliefs and zero execution fuel preserve
the original fallback/stopping semantics. Training cuts and execution fuel are
separate. All controls and declarations are in the three registered modules.

See M06-recursive-solver.md for the mathematical review and explicit error/T
allocation; M06-recursive-validation.md records the exact compiler loop and
acceptance boundary. M06-recursive-sampling.md retains the historical sampler
checkpoint. No audit entry, test, dependency/toolchain pin, warning gate,
heartbeat limit or axiom whitelist was weakened.

## Remaining original M06 obligations

First inspect the preserved independent ReBeL run; do not redo the successful
M06 target and full-CI checks. Then derive source-level fresh-model-value drift,
useful first-exit/support-defect rates and CarriedResolveStepBounds for the actual
repeated solve process. The recursive local Nash theorem does not compare old
and new conditional value vectors, and private carried continuation is not
arbitrary independent re-solving. No identity between model and actual posterior,
learned-network accuracy or executable numerical-refinement theorem is claimed.
Increasing T does not eliminate an unallocated fixed prediction error.

Preserve all positive-error, hidden-type, randomized-deviation, empty-schedule,
zero-width-cut, no-belief, zero-fuel and zero-own-reach controls. Preserve the
printed/corrected Theorem3 distinction and all accepted M05 evidence.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending;
coverage.json and the original roadmap are not promoted by this checkpoint.
