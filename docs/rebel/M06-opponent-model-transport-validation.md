# M06 opponent/model transport — exact-source validation

## Source and provenance

Validated source: `334f259f450e6ce1818cb1037214bd849ffc98ed`, branch
`rebel/m06-conditioned-query-20260925`, commit time 2026-09-26T21:06:58Z
(2026-09-27 in Japan). This record closes the validation task left pending by
M06-opponent-model-transport.md; it does not close M06 or Theorem 3.

All repository reads, artifact downloads and commits used the GitHub plugin.
The source-only artifact was extracted offline without Git commands or GitHub
HTTP. Source artifact 10915577893 has archive SHA-256
`ee1a912f92bbefdeebf84e717301c5e5055d3e0a15a229d776c15f8a3cebea7e`;
its source-commit.txt contains the exact validated SHA. Source tar SHA-256 is
`b5fb841815f0f6e6648fa96f9c2d5dbcb8d034af9c67177474d099e40e471f6a`.

Source blobs inspected:
- GameTheory/Math/Probability/FinDistKernelVariation.lean:
  `91bda118b150a1c74887dc46ef25fd8800fed562`.
- GameTheory/Analysis/ReBeL/PBSOpponentModelTransport.lean:
  `a16ac2033694fb53f7ab4d75b0fa3637a56a6c0b`.
- GameTheory/Analysis/ReBeL/Examples/PBSOpponentModelTransport.lean:
  `8cb6ad833a3250905ca3527187c3bf8d67bc058a`.

## Executed validation

Target run 36271821127, job 108487104213:
https://github.com/marshmallowday/leanrebel/actions/runs/36271821127/job/108487104213

Artifact 10915643683, archive SHA-256
`03e1d21a915ddd80a50aa289263ee5c398242135b5e520ced8f9b290023a3c28`;
m06-targeted.log SHA-256
`2b29e2380a41d7a917630a81e382bea6e19820493022aa42695e7dd69656aeff`.
The log starts with the source SHA and Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. The declared M06 targets compile.
The unchanged audit_exact_leaf.py completes normal/slow lint of 110 modules
and 1,733 transitive declaration audits. The three new modules contribute
6, 22 and 21 audited declarations respectively (including generated helpers).
EXACT_LEAF_VALIDATION_PASS modules=110 is present.

All-ReBeL run 36271821152, job 108487174934:
https://github.com/marshmallowday/leanrebel/actions/runs/36271821152/job/108487174934

Artifact 10916636527, archive SHA-256
`dece75783b7f820e5c85c467dde3a3c0e589cd86e43f1e659df2655b2fe11ddc`;
rebel-validation.log SHA-256
`57282d7b4ed551893b042327ef7f8380881eea17aabb81c9e312961ac8250e1e`.
Actual markers: REBEL_AXIOM_AUDIT_PASS declarations=4904 and
REBEL_VALIDATION_PASS modules=253. Fixture, rational-runtime and cleanliness
steps succeeded. The separate math module is explicitly linted by the target
auditor; the global ReBeL roots add the two new ReBeL modules.

Both actual logs' multiline axiom sets were parsed independently: 1,733 and
4,904 records, with no dependency outside propext, Classical.choice, Quot.sound.
Every one of the 22 declarations in the slice coverage occurs in the inspected
records. This is not a source grep or an inferred compiler-trust claim.

Full CI run 36271821124, job 108487337344:
https://github.com/marshmallowday/leanrebel/actions/runs/36271821124/job/108487337344

Artifact 10916087967, archive SHA-256
`b0078515a15e70bb74e0394161b97ad291a043fee37ad57e24a730e73c6a173f`.
ci-source.txt matches the source SHA. All three actual phase logs end VERIFIED=1;
Phase 2/3 include deep reachability probes. The actual public lint log reports
4,047 jobs and successful GameTheory.LintAll lint. Inventory retains 3,054 items
and original statuses; compiler reuse reports 23 signatures. Full build and
tracked-file cleanliness steps succeeded. Source-inventory run 36271821169
also succeeded. No local Lean or PowerShell execution is claimed.

## Semantic review

Finite history carriers are explicit where atomVariation is summed; no
finiteness is retained on the supported-posterior lemma that does not use it.
Kernel perturbation averages differences under the first, ACTUAL input law;
the other kernel contracts the incoming-law discrepancy. Induction uses
canonical runBehavioralFrom_add, so stopping and zero fuel are not replaced by
an invented transition semantics. The actual profile is exactly
Profile.update unknown who (chosen who); the stored PBS advances under chosen.
The initial actual/model discrepancy is not discarded.

A supported model outcome constructs a possible public observation and its
actual conditioned joint PBS containing the history. Its contrapositive bounds
both impossible-observation and hidden-support failures. Public conditional
transport is averaged under the actual public law and keeps the established
explicit support-defect cost. A total fallback is not declared a posterior.

The live example uses the real budget-1/8 information-set CFR child and an
arbitrary actual history point mass. Matched source/profile has zero charge.
Finite-law controls exhibit half-unit incoming/kernel variation, quarter-mass
lost support, and the false zero charge produced by an unrelated model prefix.
Those controls are not claimed to be CFR-generated regret tables.

This proves a computable transport charge, not its smallness under independently
changing opponents. It does not transfer the native gap to changed type kernels,
identify an independently re-solved carried PBS, establish a vanishing first-exit
rate, or discharge recursive safety/CarriedResolveStepBounds. SEARCH-FRONTIER,
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending. M07 is not started.
