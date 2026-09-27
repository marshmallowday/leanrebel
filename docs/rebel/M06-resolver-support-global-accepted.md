# Exact 3dfa global validation accepted

Source `3dfa8c78375218bae5a323803f889b06342aecc2`, branch
`rebel/m06-resolver-support-20260927`. This complements the separately accepted
TARGET review in M06-resolver-support-target-accepted.md. It does not validate
any newly added finite-schedule source.

## Complete artifact inspection

GLOBAL run 36281726986 / job 108514756082 completed successfully, including
compiler, normal/slow lint, transitive axioms, architecture, rational runtime,
fixture/inventory and tracked-file cleanliness steps. Artifact 10920070597
was downloaded via the GitHub connector and its complete logs were inspected.

- Artifact: `rebel-validation-3dfa8c78375218bae5a323803f889b06342aecc2`.
- ZIP SHA-256: `e5aae2673ac44d4157f7a9afa3c5fc80e8d686b1427d870bbcf47bb5f0d0a5fa`.
- `rebel-validation.log` SHA-256:
  `990ec962151137a50d6ed04262697150f3054d69291cb17b90a7ef100a912b29`.
- All 4,962 record starts have complete closing-bracket axiom records, including
  multiline records. Declaration names are unique and every dependency set is
  contained in `{propext, Classical.choice, Quot.sound}`.
- All 253 distinct module lint passes are present, together with final
  `REBEL_AXIOM_AUDIT_PASS declarations=4962` and
  `REBEL_VALIDATION_PASS modules=253` markers.
- All seven new native support declarations and all four controls individually
  occur in the complete allowlisted records. No actual compiler warning/error
  diagnostics were found. Declaration names ending in `_error:` are axiom
  output labels, not compiler errors.
- `rebel-architecture.log` SHA-256:
  `9e3abd1a1e20a09f93bb14031449e13bf526ff6d9cc28972b061a2a90dd5e06e`.
  It ends in `VERIFIED=1`; analysis transport and forbidden trust counts are zero.
- `rebel-rational-runtime.json` identifies exact 3dfa and status pass: 85
  histories, rounds 0/1/2, 40 local probabilities per round and 1,024 pure
  policies per player. This is runtime cross-checking, not a refinement proof.

The separately queried FULL CI run 36281726988 / job 108514874942 reports
success, including all Phase 1/2/3 gates, complete-library lint and clean
tracked files. This full-CI observation is from job/step metadata, not a claim
that its full archive was downloaded. Inventory 36281726972 also succeeded.
Cancelled duplicate runs on a different checkpoint branch are not substituted
for these exact source-branch runs.

## Scope

This closes the inherited native support slice's pending target/global review.
Its small-leakage and security obligations remain open; support inclusion is
not posterior equality. The new finite-schedule source at 370384f660a3c57e8f08e98bcf40e3f7528020bb
requires its own validation. No dependency pins, theorem statements, negative
controls, audit consumers or architecture budgets are weakened. M06 remains
incomplete, and no original paper source obligation is marked verified here.
