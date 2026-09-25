# M06 scalar stability — full CI resolved

## Superseding result

This update follows target-evidence checkpoint
b48ea151b5dc1c7965286d03277af4de54a93b1d. It supersedes the unfinished Full CI
paragraph in M06-scalar-stability-evidence.md, preserving that earlier record
of what had actually completed at checkpoint creation.

Source5a9fc55e6b944abb16ec7f2e16e80deb0db341f3 now has SUCCESS for full CI
run36113477728/job108001998743. The job's whole-library build, exact source
and toolchain identification, compiler-resolved inventory/reuse signatures,
Phase1, Phase2 and Phase3 architecture/reachability gates, GameTheory.LintAll
and tracked-file cleanliness steps all succeeded. The Windows-only setup step
was correctly skipped on Linux; no acceptance check was skipped or weakened.

Artifact10855041558 was downloaded using the GitHub plugin. ZIP SHA256
4f298f89ecf6b1b4f0990b6936cc830637e72227eabc33d59ec472d47353c51f
was checked against its received bytes. ci-source.txt identifies the exact
source above. Each phase log ends VERIFIED=1; the Phase2 log explicitly reports
TRANSPORT_ANALYSIS_SOURCE=0, resolving the previous two-change-tactic failure
without relaxing the expected count. The lint log reports successful
GameTheory.LintAll build and lint; the inventory log reports23 compiler-resolved
reuse signatures and3054 structurally checked ledger items. Individual log
hashes are preserved in M06-scalar-full-ci.json.

## Already inspected target evidence

The same source has targeted run36113477726/job108001998137 SUCCESS:
136 targets compiled,98 supplemental lint/audit modules,1560 transitive axiom
records, and33 new declarations in the two new modules. Every recorded axiom
belongs to {propext, Classical.choice, Quot.sound}. See the retained
M06-scalar-stability-evidence.md and M06-scalar-stability-axioms.json.
All83 Python regression tests also passed on the exact source export; those
numerical diagnostics are not substituted for the Lean evidence.

## Independent ReBeL check still pending

Independent ReBeL run36113477739/job108001998664 was re-read after full CI
completed. It was still in its all-ReBeL compiler/lint/transitive-axiom step.
Its preceding width, static architecture, source/toolchain, dependency,
ledger/adversarial and rational-solver steps succeeded. The source-snapshot
job108001998376 also succeeded. No final independent SUCCESS is claimed.

Read this exact-SHA independent result before integration or a new dependent
proof slice. Source branch rebel/m06-scalar-tail-repair-20260925 remains fixed.
The documentation branch rebel/m06-scalar-checkpoint-20260925 records this
state without cancelling the source's CI. No background follow-up is implied.

## Mathematical scope retained

The verified interfaces compare scalar values of actual averaged solver
outputs at the SAME joint PBS. The explicit cutoff controls every pair of
sufficiently late solver iteration counts, not training episodes, individual
native strategies or changed-belief conditional values. The sharp equal-mean,
exact-Nash counterexample has directed coupling cost1/2 for every valid joint.

The canonical parents SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 remain pending. Native conditional rates, first-exit rates, later
independent carried-PBS re-solving and CarriedResolveStepBounds remain.
Main is unchanged and M06 is NOT complete. Earlier failures and all predecessor
refs, gates, tests, dependency pins and strict axiom allowances are preserved.
