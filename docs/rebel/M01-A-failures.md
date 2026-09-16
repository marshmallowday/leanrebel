# M01-A observed compiler-loop failures

These failures are retained as evidence of actual feedback, not counted as
successful validation. M01-B is gated on completing M01-A.

## First probe: nonexistent import in pinned Mathlib

Commit: b8a728be73d468c65657649683ec61776a4d02cb.
Run: 35138332030. Job: 104936239317.
The full job log was inspected. Lean installed successfully:
4.33.1, compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
The ledger structure checker passed (60 pending items), but the actual narrow
build failed because Mathlib.Data.Rat.Order does not exist in pinned Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. All dependent diagnostic modules
therefore failed, and the axiom/lint checks did not run.

Repair: use the inspected, existing Mathlib.Algebra.Order.Field.Rat module.
The proof statements and adversarial examples are not weakened.
The full log also showed that saving a 2.52 GB complete .lake cache delayed
this small compiler probe by over five minutes. The dedicated diagnostic job
now requests only its actual Mathlib dependency closure and does not save the
entire workspace cache before validation. Full builds remain separate gates.

A later layout-only revision, 906de02d6c438e146028a9adebae7e9d51a25da8,
still contained the bad import and is not a repaired compiler result.

## Second probe: proof build passes, auditor syntax fails

Commit: 58e8a7db7178e7769ebeed5ce0a735a79de1000a.
Run: 35139613312. Job: 104940800828.
The full job log was inspected. Targeted dependency caching succeeded (800
files). The actual narrow build succeeded at 2026-09-16T19:19:32Z:
GameTheory.Tests.ReBeLSourceDiagnostics, 816 build jobs, no proof placeholders.
The generated auditor then failed at line 8 because `prefix` is a Lean syntax
keyword and cannot be used as an ordinary local identifier. Axiom collection
and lint did not execute; a successful proof build alone is not M01-A closure.

Repair: rename the local to `modulePrefix`. Also cache EnvironmentHeader's
module-name array once, rather than reconstructing it for every declaration.
The pinned Environment.lean API was inspected: ModuleIdx.toNat and
EnvironmentHeader.moduleNames both exist in v4.33.1.

The proof module has Git blob 9b346667d5dad982083a7681f6e24e68063133a4,
92 source lines, and maximum line length 83. The exact-source artifact was
retrieved and SHA-256 checked before local structural/semantic inspection.
Independent rational arithmetic gives f(z)=1/4, plane(z)=0, midpoint value
1/3 and average endpoint value 3/8. These are semantic controls, not a
replacement for the missing axiom/lint run. The replacement auditor must
receive its own successful exact-SHA run before acceptance.
