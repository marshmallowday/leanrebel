# Exact 35d0 primitive-rate compiler checkpoint

Source: 35d0bc04dcc12c3badad5a577f5218b5cc6d9a75, preserved on
`rebel/m06-primitive-support-checkpoint-20260927`. Continue the documentation
review descendant on `rebel/m06-primitive-support-validation-20260927` rather
than reverting to d6c5 or main. The evidence commit does not change Lean code,
fixtures, dependencies, workflow configuration or validation gates.

## Actual validation observations

TARGET run 36287339648 / job 108530477785 completed its entire declared-target
compiler step successfully. Its subsequent normal/slow lint and transitive-axiom
step was still running when inspected. This is a compiler-step pass, NOT final
target acceptance; obtain and inspect the complete final artifact and every
axiom record before accepting the new slice. All seven core declarations and
five new control theorems are included in the existing target modules.

GLOBAL run 36287339585 / job 108530593276 separately passed line widths, frozen
static architecture, ledger/inventory/fixtures and rational-runtime steps. Its
compiler/lint/axiom step was still running. The exact-source snapshot job
108530593429 succeeded. FULL CI run 36287339593 / job 108530515400 remained in
its Lean action step when separately inspected. INVENTORY run 36287339601 /
job 108530477522 completed successfully. Do not infer any missing final result
from a different run, source, target-only pass or green source-inventory job.

## Exact snapshot and arithmetic controls

Source artifact 10921345479 was downloaded through the GitHub connector.
ZIP SHA-256: 271adb161ea6f7c1f69c3d65683d4695b1e977cfff003f2fc4b2251965b5ba5c.
Its source-commit.txt identifies exactly 35d0, and the extracted source TAR has
SHA-256: 866b96ae875e4e850260009b83ee7effd0575328309f7bbfe57df22d9f5aa3ee.

The two Lean source blobs were independently checked:
- FinDistFirstHit: 3f74f22db81ef4e80819bb04e04c9169aae1cc46;
  SHA-256 dc853bd2a9582ff4d84d0183be30ac641de6dcb579d0ae2b1aa6d12f1e4cf9ea.
- PBSCarriedSupport: 87d245e0e49df16c5a44b71a18fe34b4c47e2472;
  SHA-256 35c902b492ae2c8c369fafdaae7aa37aee860bdbe6e2d01bf26a833b4a8c8393.

The source comparison confirms precisely one publicTrace signal-index repair
and its line wrap versus d6c5; the generic math and every control are unchanged.
Both modules remain in m06-targets.txt, audit_exact_leaf.py and the global
analysis umbrella. There are no new source-width violations or placeholders;
this textual inspection is NOT a transitive-axiom audit.

On the exact unmodified extracted 35d0 snapshot, all 134 Python tests passed
under `python -W error -m unittest discover -s scripts/rebel/tests -v`.
The new seven fixtures include 2,187 inhomogeneous schedule cases. The test log
SHA-256 is 7194f628b8edbf3ccc414bdea08c675f83650bbd51fc028d0ca58ccfce058825.
Both check_coverage.py and check_inventory.py passed structural checks on the
same source. No local Lean execution or local git operation was performed.

## Scope and preserved evidence

M06-primitive-support.md gives the semantic review and explicit primitive
leakage premises. The first-hit budget charges only good-state transitions
before another stage input, not repeated bad visits or the final output.
The private selected model, joint PBS and actual incoming state law remain
paired, and the same unknown opponent is used throughout. Primitive smallness
for unrestricted finite-T CFR is not established by these conditional lemmas.

The complete d6c5 failure is preserved in M06-primitive-support-d6c5-failure.md.
The inherited 4784 target/global acceptance is complete and separately recorded:
1,823 target axiom records / 111 lint modules; 4,988 global records / 254 lint
modules, all allowlisted. Those results do not validate 35d0's new code.

Next inspect 35d0's final target artifact and independently its global/full CI.
Changed-PBS native/late signed value gaps and source-specific
CarriedResolveStepBounds remain open, together with the four original source
obligations. M06 is incomplete. No background monitoring is implied.
