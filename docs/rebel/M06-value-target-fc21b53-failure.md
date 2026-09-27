# M06 root value-target batch: fc21b53 failure and grouped repair

Failed source: fc21b53175a5b65f7a7bfc3ff5dd74a8c2627972.
Branch: rebel/m06-kernel-value-repair-20260927.
The current read-only GitHub preflight reconfirmed marshmallowday with
admin/push permission, that branch HEAD, and main
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Continue this M06 branch because
its actual root-target batch is the source of these diagnostics.

## Observed exact-SHA results

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36333997905 / 108661231972](https://github.com/marshmallowday/leanrebel/actions/runs/36333997905) | build failure |
| ReBeL checks | [36333997907 / 108661231970](https://github.com/marshmallowday/leanrebel/actions/runs/36333997907) | build failure |
| M06 targeted | [36333997908 / 108661231843](https://github.com/marshmallowday/leanrebel/actions/runs/36333997908) | build failure |
| Source inventory | [36333997909 / 108661231868](https://github.com/marshmallowday/leanrebel/actions/runs/36333997909) | success |

Complete decoded logs were fetched through the GitHub plugin. All three
build failures report the same diagnostics in CFRDValueTarget.lean:
- Lines 48/52: the conditional law's dependent if was not reduced. Its
  literal singleton-preimage proposition did not match the simplifier rule
  supplied through the local event alias.
- Lines 47/51: consequent unused dif_pos/dif_neg simp arguments.
- Line 85: field_simp already closed the arithmetic goal; ring was unused.
- Lines 145/179: recall is a parser keyword, so the two theorem binders
  failed to parse. The later unknown profile/fallback/theorem and no-goal
  diagnostics are downstream of that parse failure.

ReBeL checks passed static architecture (TRANSPORT_ANALYSIS_SOURCE=0) and
line width (LIBRARY_LINES_OVER_100=0), rational Lean solver/runtime, ledger
and inventory checks, and 176 Python tests in 10.030s. The independent
inventory job passed 176 tests in 9.986s and tracked-file cleanliness.
The frontier journal's pinned sources were accepted by the ledger validator.
This is not a substitute for the new core/example build and full lint/axioms,
which were not reached successfully.

Artifact metadata inspected: targeted 10936942372
(sha256:a5b08c17b8a3b0586d6511be700d9b2d864be1f30fac39b43b4bfff72675bfc6),
global validation 10936898447
(sha256:1541f542f25ecd1a889a62fd79e84414b9c9389304baf354e7e34298867b1275),
source snapshot 10936258716
(sha256:426c2c0fbf0849b1b251e67d7ddf622a9431be3f38d4a1f410d01720d25ee6c4).
Snapshot job 108661232177 succeeded. CI and inventory had no artifacts.
Binary archives were not downloaded; full decoded job logs provide diagnostics.

## One grouped source repair

The case split now gives possible its explicit singleton-preimage type.
A local conditional-law equality unfolds condOnFibre with dsimp only and
rewrites the dependent branch with that exact proof, following the accepted
conditioning proof style. Both expectation occurrences use that equality.
The reserved binders become hrecall. The trailing ring is removed.
The previously unparsed terminal-backup proof also uses one simp only per
live/stopped branch, avoiding repeated if rewrites.

Mathematical statements, target definitions, support conventions, finite-T
and noise boundaries are unchanged. No tests, workflow, audit, journal
acceptance status or specification are weakened. This is the repair phase
of the combined 13-file batch, not a new small-feature validation cycle.

The repaired source requires its own exact-SHA Actions. Expected surface
remains 158 targets, 120 targeted / 263 global modules, and 176 Python tests.
The accepted e123cb8 predecessor's 1990/5138 axiom records do not validate
the new source. M06 remains incomplete; after this repair passes, resume
large dependency-ordered implementation batches.
