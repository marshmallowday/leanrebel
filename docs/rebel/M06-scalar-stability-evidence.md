# M06 scalar output stability — exact-source validation checkpoint

## Resume and source identity

Documentation branch: rebel/m06-scalar-checkpoint-20260925.
Source branch: rebel/m06-scalar-tail-repair-20260925.
Source commit: 5a9fc55e6b944abb16ec7f2e16e80deb0db341f3.
The documentation checkpoint descends directly from that source and changes
no Lean source, test, target list, workflow or dependency. Source refs remain
fixed so that documentation does not cancel their independent CI runs.

The original resume point2e1de273b9164743decdd8a283b3249f34bf5600 and accepted
value-coupling source4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5 are preserved.
Their STATUS text is retained in STATUS-before-scalar-stability.md. The old
independent ReBeL run36103763078/job107971751432 was re-read as SUCCESS.

## Current exact-SHA target results

M06 targeted proof feedback run36113477726/job108001998137 completed SUCCESS.
The136 declared targets compiled. The supplementary script then built its
98 modules, collected transitive axioms of every declaration in those modules,
and ran Batteries lint for each module. The downloaded actual log ends with

    EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1560
    EXACT_LEAF_VALIDATION_PASS modules=98

Every one of the1560 parsed dependency records is contained in
{propext, Classical.choice, Quot.sound}; every one of the98 modules has its
individual EXACT_LEAF_LINT_PASS marker. No error or warning lines occur in
the captured Lean target log. New module counts are7 for PBSValueStability
and26 for its example, including all generated/private declarations.
The33 new individual dependency records are in M06-scalar-stability-axioms.json.

The log identifies Lean4.33.1, toolchain commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Artifact10855021036 was downloaded
through the GitHub plugin. Its ZIP SHA256 is
05ccd421a2e5384733aab475c842d4caeb3511e49e961081bcc190e275b5fcad;
the actual m06-targeted.log SHA256 is
1bd210f699a446f06d2d3afeb578104be581a45a2f5e01c9ca72dea5bf93a9b9.
Both hashes were computed from the received bytes, and the embedded source
SHA was checked before attributing success to this source.

## Source and regression verification

Snapshot job108001998376 in run36113477739 succeeded. Artifact10854072229,
downloaded through the GitHub plugin, has ZIP SHA256
0deefbc51a183e064e8352d6ada2391b40365b6aaaaaa57ee0277c6e3b525f18
and embedded TAR SHA256
318629d756d4e461c36af3374d93b0f0f56ff40c8fce40cba664c11955c00af4.
The embedded source and both hashes were verified. The two Lean files,
umbrella, target list, audit consumer and two test files matched the prepared
bytes exactly; their individual hashes are in M06-scalar-stability-source.json.

On that exact exported source, the following offline commands succeeded:

    python scripts/rebel/check_coverage.py
    python scripts/rebel/check_inventory.py
    python -W error -m unittest discover -s scripts/rebel/tests -v

All83 tests passed: all76 inherited tests plus7 new tests. The new tests include
6561 exact-rational game/profile pairs and108 squared cutoff checks, with
mean-preserving spread, missing zero-sum and different-game boundary controls.
These are regression diagnostics, not a proof of numerical runtime refinement.
The canonical ledger remains3054 items with its prior status counts unchanged.
Inventory CI run36113477708/job108001998430 also succeeded at this source.

## Wider CI at this checkpoint

Full CI run36113477728/job108001998743 has passed its whole-library build,
source/toolchain identification, inventory/compiler-signature checks and
Phase1/2 gates. Phase3, whole-library lint and cleanliness were still unfinished
at the last read. Do not turn those partial successes into final SUCCESS.

Independent ReBeL run36113477739/job108001998664 has passed its line-width,
static architecture, exact-source/toolchain, dependency, ledger/adversarial
and rational solver steps. Its all-ReBeL compiler/lint/transitive-axiom step
was still in progress. Check that exact-SHA result before integration.
Neither unfinished workflow is implicitly monitored after this interaction.

## Preserved compiler and architecture loop

- 4ddb211c018100011c31407b3ed90a0aa67e4164 records resumption and the resolved
  old independent gate before source edits.
- ce75519c49043af2b8a640efc82ffa6cfa7e3dca restores the prior candidate.
  Run36111759855/job107996586904 failed in the example, while the main five
  theorem module compiled. Artifact10853309041 and its hash are retained in
  M06-scalar-tail-validation.md. Its lint/axiom step was skipped, not passed.
- 737704a90113d99ac135cbd6455ecf2bb7a563e3 repairs explicit Fin3 distinctions,
  abbreviation-sensitive matching and expect_map arguments. Its target
  run36112574506/job107999160253 passed1557 declaration and98-module checks.
  Artifact10854042269 ZIP SHA256 is
  2daa542e83102ab3a4b3905a74cd4240f66df4374159f889037755544ea10a93.
  The download was inspected; target success alone was not full acceptance.
- 0382af933e2520c3eb152fe98ae9b45f73c4601d adds the explicit uniform scalar
  tail cutoff and arbitrary-late-output consumer. Target
  run36112787339/job107999829165 passed1560 declaration and98-module checks.
  Artifact10853504444 ZIP SHA256 is
  a4be5d1002370a8331c607959c6e6312eec6e19ea9411327d11daa6334f13d86.
  Its independent ReBeL run36112787359/job107999916653 FAILED the unchanged
  architecture gate because two change tactics exceeded the zero budget.
- 5a9fc55e6b944abb16ec7f2e16e80deb0db341f3 removes those two tactics only.
  Explicit proof terms retain every theorem statement and all earlier tests.
  This source's own target and static architecture checks passed as above.

No failure is hidden by suppression, deletion, expected-count adjustment or
force-push. All GitHub reads, writes, commits and ref changes used the GitHub
plugin. Local work was limited to offline artifacts, hashes and tests, not Git.

## Semantic and acceptance boundary

See M06-scalar-stability-review.md for the cross-profile proof, all retained
assumptions and exact declarations. The computed cutoff concerns solver
iteration counts, NOT the number of training episodes. Horizon and belief
are fixed. Scalar Cauchy control is not conditional value-vector stability.

The source proves same-PBS scalar output estimates, finite-budget and explicit
noisy-depth comparisons, and the sharp exact-Nash coupling counterexample.
It supplies no native-iteration rate, changed-belief rate, first-exit theorem
or CarriedResolveStepBounds. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 stay pending. M06 remains incomplete, main is not changed, and
the printed/corrected Theorem3 and finite-T/zero-oracle distinction are retained.
