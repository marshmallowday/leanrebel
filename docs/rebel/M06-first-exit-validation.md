# M06 first-exit exact-source validation checkpoint

## Source identity

Proof/configuration source: `487aaedd795d5d3a8b41a608c6a4e13d1967cb1c`.
Source tree: `cd56360fd5072334d1c7878cde9e5674ef7a018a`.
Preserved branch: `rebel/m06-first-exit-20260924`.
Documentation-only review branch: `rebel/m06-first-exit-review-20260924`.
The review commit has source487aaedd as its direct parent and changes only docs.
All remote reads, writes and ref changes use the GitHub plugin.

## Target compiler and supplemental validation: SUCCESS

M06 target run35941683756/job107450728931 completed successfully at exact source
487aaedd795d5d3a8b41a608c6a4e13d1967cb1c. The completed job's full decoded log
was inspected with truncated=false. It explicitly identifies the source SHA and
Lean4.33.1, then reports successful builds for:

- GameTheory.Math.Probability.FinDistFirstHit;
- GameTheory.Analysis.ReBeL.PBSCarriedDepthFirstHit;
- GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepthSampling.

The declared-target build completed successfully. The unchanged command
python3 scripts/rebel/audit_exact_leaf.py then reported
EXACT_LEAF_AXIOM_AUDIT_PASS, a lint report with no errors, and
EXACT_LEAF_VALIDATION_PASS. The job completed diagnostics and artifact publication
successfully. This validates the new first-exit general theory, its noisy PBS
connection and the concrete controls through the existing supplemental audit.

This completed result supersedes the earlier snapshot where compilation had
passed but the supplemental audit was running. The earlier in-progress log
endpoint returned BlobNotFound; the subsequently available complete log, not
that transient error, is the evidence used here.

## Independent repository-wide checks: not yet accepted

At the latest inspection, ReBeL run35941683758/job107450798403 had passed
line-width, static architecture, ledger/inventory/adversarial fixtures and the
executed rational solver checks. Its complete compiler/lint/transitive-axiom
step remained in progress. Source snapshot job107450798669 succeeded.

Full repository CI run35941683736/job107450816152 remained in progress.
Its inventory/reuse check and Phase1 architecture step had passed; the Phase2
architecture/reachability step was running. Later phases and full-library lint
had not yet produced final results.

Inventory run35941683774/job107450728949 succeeded.

These are observed results, not predictions. Inspect these exact source487aaedd
runs before full acceptance. The source branch is left unchanged so recording
this checkpoint does not cancel its checks. Documentation-only descendant checks
are separate runs; never mislabel them as the source487aaedd validation.

## Recovery evidence, separate from the new source

At source01245b31164eabcb7012e98b36d57b470496dd8e, inspected M06 target
35939097445/job107442786882, ReBeL35939097447/job107442786889, repository CI
35939097488 and inventory35939097484 all succeeded. The independent ReBeL
job explicitly completed compilation/lint/axiom audit and tracked-file cleanliness.
This accepts the earlier concrete-support repair, not the new first-exit extension.

Candidate9165ff11 failed target35940857858/job107448326120 at the unreduced
Option.isSome point-mass probability. Repair9537c4f3 changes only that simp set;
487aaedd retains it and adds the probability-directory trigger. The latter source
has now passed both compilation and the supplemental audit, superseding the
earlier candidate failure. See M06-first-exit-diagnostics.md.

## Reproduction and trust boundary

Run the unchanged commands from .github/workflows/rebel-m06-dev.yml on the exact
source: compile scripts/rebel/m06-targets.txt, then audit_exact_leaf.py. That
script includes both extended proof modules and the example module, enumerates
all owned declarations including private ones with Lean.collectAxioms, permits
only propext/Classical.choice/Quot.sound, and runs the existing Batteries linters.
The independent repository-wide ReBeL and CI workflows remain required.

No sorry, new axiom, conclusion-shaped safety certificate, changed numerical
bound, raised heartbeat, dependency upgrade, removed test or weakened gate is
introduced. The first-exit charge is not a learned/executable error estimate or
a proof of the source's recursive safety rate. All four original M06 coverage
rows stay pending; see STATUS.md and the semantic review in M06-first-exit.md.
