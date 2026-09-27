# Exact 35d0 primitive-rate global validation accepted

Source: 35d0bc04dcc12c3badad5a577f5218b5cc6d9a75.
Global run 36287339585 / job 108530593276 completed successfully, including
static architecture, widths, fixtures, runtime, complete compiler/lint/axioms
and tracked-file cleanliness. Source snapshot job 108530593429 succeeded too.
Artifact 10920889550 was downloaded through the GitHub connector and all complete
records were inspected; metadata success alone was not treated as an axiom audit.

ZIP SHA-256: c97a2b3ad7029a4b42383a8c96af3af5459d81099d92e894ce4264446e5ef86a.
rebel-validation.log: ad7233a31281e458609d9f33d7415bf9639859561675bd1d1b834a10143687f3.
rebel-architecture.log: 9e3abd1a1e20a09f93bb14031449e13bf526ff6d9cc28972b061a2a90dd5e06e.
rebel-rational-runtime.json: faf834f1a8a1c89b58ac2503e4cab1986204e044e8c8bfb7511affe6d0b5cdef.

The validation log begins with exactly 35d0. All 5,003 complete REBEL_AXIOMS
records were parsed including multiline lists; all names are unique, there are
no incomplete record headers, and the count agrees with REBEL_AXIOM_AUDIT_PASS.
Every dependency is among propext, Classical.choice and Quot.sound. All 254
explicit module names match the 254 complete normal/slow REBEL_LINT_PASS names
and REBEL_VALIDATION_PASS. The four new core GameTheory.ReBeL primitive-rate
names are present. The generic FinDist math declarations are covered by the
separately accepted 35d0 TARGET, not silently counted in the global namespace filter.

The actual architecture report ends VERIFIED=1 and retains the frozen zero
analysis transport/outside-owner representation/placeholder/custom-axiom counts.
The actual rational-runtime JSON says source_sha=35d0 and status=pass; it remains
a numerical cross-check, not a proof of a full external runtime refinement.

Full CI 36287339593 / job 108530515400 separately succeeded through its Lean
action, inventory/reuse signatures, all three architecture/reachability gates,
full library lint and tracked cleanliness in the fetched job-step metadata.
This is distinct from inspecting a full-CI raw log. Target acceptance remains
M06-primitive-support-target-accepted.md (1,853 records / 111 modules).
The previous pending observations remain in the owning coverage as history.

This acceptance applies to 35d0 only, not the new depth-native-gap candidate.
It does not discharge primitive leakage smallness for an unrestricted solver,
changed-PBS value transport or the original pending Theorem 3 obligations.
M06 remains incomplete.
