# ReBeL status — M06 in progress; M05 accepted

## Resume from the scalar-stability checkpoint

Documentation branch: rebel/m06-scalar-checkpoint-20260925.
Validated source: 5a9fc55e6b944abb16ec7f2e16e80deb0db341f3 on
rebel/m06-scalar-tail-repair-20260925. Checkpoints add documentation only;
the source branch stays fixed so its independent CI is not cancelled.
The prior target-evidence checkpoint is b48ea151b5dc1c7965286d03277af4de54a93b1d.
Read M06-scalar-full-ci.md, M06-scalar-stability-evidence.md,
M06-scalar-stability-review.md and the companion coverage, source and axiom
JSON files. Main and all predecessor source refs are unchanged.

## Implemented and validated source slice

PBSValueStability adds seven theorem interfaces. Two approximate Nash outputs
at one joint PBS have scalar difference at most the sum of their errors.
The actual finite information-set CFR, requested-budget and allocated noisy
solve interfaces discharge their own Nash premises. For every tolerance>0,
the explicit half-tolerance cutoff controls ANY two later averaged outputs,
even with different legal fallbacks. This is a solver-iteration cutoff, not
a training-episode count; belief, payoff and horizon remain fixed.

The HiddenTypes consumers use finite budgets1/4 and1/8 and arbitrary sufficiently
late outputs at tolerance1/8. The exact-Nash chance-game control has equal
scalar values but every valid coupling costs1/2. This prevents conflating
scalar output accuracy with small directed coupling cost or conditional rates.

Target run36113477726/job108001998137 completed SUCCESS at the source above.
All136 targets compiled. Downloaded logs show
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1560 and
EXACT_LEAF_VALIDATION_PASS modules=98, with98 individual lint passes.
All33 new declarations, including generated/private ones, use only allowed
axioms: propext, Classical.choice and Quot.sound. New module counts are7 and26.
Source and log hashes were checked against received bytes and retained in JSON.
On the exact source export, all83 Python tests and ledger/inventory checks
passed. Inventory run36113477708 and source snapshot108001998376 also succeeded.

## Full CI resolved; independent ReBeL still running

Full CI36113477728/job108001998743 now completed SUCCESS. The downloaded
artifact10855041558 identifies this exact source; Phase1/2/3 each end VERIFIED=1,
Phase2 reports TRANSPORT_ANALYSIS_SOURCE=0, and GameTheory.LintAll passed.
The job also passed whole-library build, inventory/compiler-signature checks
and tracked-file cleanliness. M06-scalar-full-ci.md supersedes the earlier
pending full-CI paragraph in the target-evidence checkpoint.

Independent ReBeL36113477739/job108001998664 was re-read after full CI finished.
It passed preliminary architecture, ledger and rational solver steps and was
still in its all-ReBeL compiler/lint/transitive-axiom step. Read that exact-SHA
result before integration or further dependent implementation. No final
independent success or background monitoring is claimed.

## Preserved failures and remaining M06 work

The source lineage is2e1de273 ->4ddb211c ->ce75519c ->737704a9 ->0382af93 ->5a9fc55e.
Initial example elaboration failure and the later two-token architecture
failure are preserved with run/job/artifact identities and focused repairs.
Both intermediate repaired targets passed their own audits; those passes were
not substituted for the final source's checks. No inherited theorem, target,
test, gate, dependency pin or axiom allowance was weakened or removed.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Native/late-training CONDITIONAL vector rates, native first-exit, later
independent carried-PBS re-solving and CarriedResolveStepBounds remain.
Preserve actual private seed/history laws, off-path cases and model-versus-
actual beliefs. Keep finite-T residuals when oracle error is zero and keep
the printed and corrected Theorem3 readings separate. M06 is NOT complete.
