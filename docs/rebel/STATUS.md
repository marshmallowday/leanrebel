# ReBeL status — M06 in progress; M05 accepted

## Resume from the scalar-stability checkpoint

Documentation branch: rebel/m06-scalar-checkpoint-20260925.
Validated target source: 5a9fc55e6b944abb16ec7f2e16e80deb0db341f3 on
rebel/m06-scalar-tail-repair-20260925. This checkpoint changes documentation
only and keeps the source branch fixed so wider CI is not cancelled.
Read M06-scalar-stability-evidence.md, M06-scalar-stability-review.md,
M06-scalar-stability-axioms.json, M06-scalar-stability-source.json and the
scoped M06-scalar-stability-coverage.json. Main is unchanged.

## Implemented and target-validated result

PBSValueStability adds seven theorem interfaces. Two approximate Nash outputs
at one joint PBS have scalar difference at most the sum of their errors.
The actual finite information-set CFR, requested-budget and allocated noisy
solve interfaces discharge their own Nash premises. For every tolerance>0,
the explicit half-tolerance iteration cutoff controls ANY two later averaged
outputs, even with different legal fallback policies. The count is not a
training-episode count; belief, payoff and game horizon remain fixed.

The HiddenTypes consumers use finite budgets1/4 and1/8 and arbitrary sufficiently
late outputs at tolerance1/8. The exact-Nash chance-game control has equal
scalar values but every valid coupling costs1/2. This prevents conflating
scalar output accuracy with a small directed coupling cost.

Target run36113477726/job108001998137 completed SUCCESS at the source above.
All136 targets compiled, and actual downloaded logs show
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1560 and
EXACT_LEAF_VALIDATION_PASS modules=98. All98 individual lint markers passed.
All33 new declarations, including generated/private ones, use only allowed
axioms: propext, Classical.choice and Quot.sound. The two new module counts
are7 and26. Source hashes and log hashes were checked against actual bytes.
On the exact source export, all83 Python tests and ledger/inventory checks
passed. Inventory run36113477708 and the exact-source snapshot also succeeded.

## Wider checks still to inspect

Full CI36113477728/job108001998743 has passed the build, source/signature checks
and Phase1/2; Phase3, library lint and cleanliness were still unfinished at the
last read. Independent ReBeL36113477739/job108001998664 passed its preliminary
architecture, ledger and rational solver steps and was still running its
all-ReBeL compiler/lint/transitive-axiom step. Do not count either as final
success until read. No background monitoring is implied by this checkpoint.

## Preserved failures and remaining M06 work

The lineage is2e1de273 ->4ddb211c ->ce75519c ->737704a9 ->0382af93 ->5a9fc55e.
Initial example elaboration failure and the later two-token architecture
failure are preserved with run/job/artifact identities and focused repairs.
Both intermediate repaired targets passed their own audits, but those target
passes were not substituted for the final source's independent checks.
No inherited theorem, target, test, gate, pin or axiom allowance was weakened.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Native/late-training CONDITIONAL vector rates, native first-exit, later
independent carried-PBS re-solving and CarriedResolveStepBounds remain.
Preserve the actual private seed/history law, off-path cases and model-versus-
actual belief boundary. Keep finite-T residuals when oracle error is zero and
keep the printed and corrected Theorem3 readings separate. M06 is NOT complete.
