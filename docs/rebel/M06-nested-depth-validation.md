# M06 nested-depth exact-source validation

## Current source and review checkpoint

Proof/configuration source: f9d4def18411b43fc14c508b079fadb0378bd178.
Tree:50eb13caab8a41f70b48ede4cea8d46e454d565e.
Preserved source branch: rebel/m06-nested-depth-20260924.
Documentation-only review: rebel/m06-nested-depth-review-20260924.
The review descends from the proof source through documentation-only commits.
It changes no Lean file, validation script, workflow, dependency, test, tolerance
or computational limit. All remote operations and Git writes use the GitHub
plugin, never local Git. The source branch is unchanged to preserve running CI.

## New nested source: compiler and supplemental validation SUCCESS

At exact sourcef9d4def18411b43fc14c508b079fadb0378bd178, M06 run35947018152,
job107467137173 is COMPLETED SUCCESS. Both 'Compile the declared M06 targets'
and 'Supplemental compiler, lint and transitive-axiom validation' completed
successfully, followed by diagnostics and artifact publication.

The completed job's full decoded log was inspected with truncated=false.
It identifies the exact source SHA and Lean4.33.1 and reports successful builds
for the inherited finite-budget modules and all three new modules:

- GameTheory.Analysis.ReBeL.CFRDDepthChild;
- GameTheory.Analysis.ReBeL.CFRDNestedDepthDriver;
- GameTheory.Analysis.ReBeL.Examples.CFRDNestedDepth.

The unchanged supplemental command python3 scripts/rebel/audit_exact_leaf.py
then audited every owned public/private declaration transitively, retaining only
propext, Classical.choice and Quot.sound. The log reports26 owned declarations
for CFRDDepthChild,5 for CFRDNestedDepthDriver and21 for Examples.CFRDNestedDepth,
and EXACT_LEAF_AXIOM_AUDIT_PASS. Every normal/slow Batteries lint invocation
passed, including all three new modules. The final marker is
EXACT_LEAF_VALIDATION_PASS modules=88.

This completed result supersedes the compiler-only/pending-supplemental snapshot
at568cb8fd and the earlier failed22b15778 candidate. It validates the nested
child construction, coupled parent guarantees and concrete controls through the
existing targeted compiler and supplemental audits. It does NOT assert that
the independent repository-wide checks passed or that M06 is complete.

Initial attempts to obtain the running job's log returned Azure BlobNotFound.
Those transient unavailable logs were neither proof failures nor acceptance
evidence. The subsequently published complete log, not the unavailable endpoint,
is the evidence for the successful compiler and supplemental validation above.

## Independent new-source repository-wide checks: still pending

ReBeL run35947018175/job107467137458 passed line width, static architecture,
ledger/inventory/adversarial fixtures and the executed rational solver checks.
Its complete compiler/lint/transitive-axiom audit step remained in progress at
the latest inspection; cleanliness and publication had no final results.
Source snapshot job107467137602 succeeded.

Full repository CI run35947018228/job107467419037 remained in progress.
Inventory/reuse and Phase1 architecture passed; Phase2 architecture/reachability
was running. Phase3, full-library lint and cleanliness had no final results.
Inventory run35947018259/job107467137512 succeeded.

Inspect final outcomes for these exact f9d4def1 runs before full acceptance.
Do not substitute predecessor successes or documentation-descendant runs.

## Preserved budget repair: target and full CI succeeded

Source704e96ff6ed5b73b279191ea2d01629cc331e8d8 is retained on the separate
rebel/m06-depth-budget-integration-20260924 branch. M06 run35946360278,
job107465069923 completed successfully INCLUDING the supplemental exact-source
lint/transitive-axiom validation. Full repository CI35946360214/job107465224924
also succeeded, completing Phase1/2/3 architecture checks, public-library lint
and tracked-file cleanliness. Inventory35946360322/job107465069843 succeeded.
The independent ReBeL35946360239/job107465227645 remained in its full proof
audit at inspection. These results supersede its earlier pending target snapshot.
They validate the repaired budget slice, not the subsequent nested source.

The earlier e9d651b2 target35945479753/job107462340355 failed on a redundant
ring tactic, undistributed sum-of-player algebra and a folded-round expression.
Repair704e96ff changes those proof steps only. All inherited definitions,
accuracy hypotheses and tests remain unchanged. The original divergent budget
branch at2c9bfd52 is preserved; only its two new modules, not stale first-hit
files or obsolete status, were incorporated into the accepted first-exit lineage.

## Initial nested candidate: rejected, superseded by repaired-source validation

Source22b15778ec0a8d6a50874176a4bd285665c46257 added the nested child/parent
modules and their full build/audit coverage. M06 run35946558196/job107465692425
failed at CFRDDepthChild.lean:207:90 because field notation was split directly
after `.law.`. The later line247 'declaration uses sorry' diagnostic was compiler
recovery from the parse failure, not a source-written placeholder. No sorry/admit
was present. Its downstream driver/examples were not accepted.

ReBeL35946558227/job107465692283 rejected three lines of width101,101,104
before compilation. It did not run its full proof audit. These failures are not
passes. Currentf9d4def1 rejoins `.law.positiveMassFloor` and wraps those lines;
child definitions, theorem statements and proof steps are otherwise unchanged.
The driver is unchanged. The repaired source now passes its declared-target
compiler and supplemental audits; independent repository-wide checks are separate.

## Positive-error controls and nonempty child continuation

The current examples retain every prior control and add parentCut1/childCut1/
remaining1. The parent cut is after chance; the child and its continuation each
contain a real decision. Its child perturbation is a positive half-allocation
for that1+1 root, while outer bias1/8 and requested child loss1/4 are retained.
Both all-query completed child optimality and finite-T all-deviation Nash are
instantiated. The earlier2+1+0 split retains a real parent and real child decision
with a terminal final suffix. Neither claims three decisions in this protocol.

Both split controls, live-table identity, complete prefix law, randomized
unilateral law, impossible observation, zero remaining fuel and positive child
prediction controls passed the targeted compiler and supplemental audits.
The companion finite-budget controls still test the actual four-point joint law,
feasible/infeasible target guards, positive fixed numerical/child errors and
nonempty finite counts.

## Trust and scope

The analytic root, M06 target list and audit_exact_leaf.py retain every old entry
and add all new modules. The audit includes every owned public/private declaration
and the unchanged propext/Classical.choice/Quot.sound whitelist. No gate, linter,
heartbeat, dependency pin, approximation bound or test is weakened or removed.

The construction adds one nested depth-child solve, not arbitrary-depth recursive
solving or independent repeated re-solving safety. Source-specific model-value
drift, first-exit/support-defect rates and CarriedResolveStepBounds remain open
obligations in this repository. Neither the noisy predictor family nor the
noncomputable real-valued allocator is a learned-network or executable refinement
guarantee. All original coverage rows remain pending; see M06-nested-depth.md.
