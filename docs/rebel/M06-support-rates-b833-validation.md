# M06 support rates — inspected b833 implementation evidence

## Source and checkpoint scope

Implementation: `b833d49b430ac44c433658f3cc72fd130ff0a87f`.
Implementation branch: `rebel/m06-support-rates-20260927`.
Evidence checkpoint: `rebel/m06-support-rates-checkpoint-20260927`.

The checkpoint changes documentation only. Its parent is the exact repaired
implementation above; it preserves the in-progress implementation-source
global audit instead of cancelling it by a same-branch documentation push.
No audit or workflow is disabled, skipped or weakened. Its new HEAD has its
own CI identity and is not called already validated. The implementation's
three Lean source blobs and Python fixture match the coverage manifest and
are unchanged by this checkpoint. All repository access and writes use the
GitHub plugin; local operations inspect downloaded bytes and run Python, not
Git commands or direct GitHub HTTP.

M06-support-rates-validation.md retains the earlier baseline and failed f14
attempt. Its repair-pending statements describe that earlier checkpoint;
the exact b833 target/full-CI results below supersede them, not the historical
failure. M06-support-rates.md remains the semantic review and explicit
premise/scope boundary. M06 and the original paper safety obligations remain
pending.

## Exact-source target — actual output inspected

Run 36277876540; job 108503997685; artifact 10917649066; job success.
Verified artifact ZIP SHA-256:
`641ecf4edd5dfd7d500d1bda9f6d87ee3ee2db7f6fa242ef6c953169f5818f30`.
Raw m06-targeted.log SHA-256:
`f7a826619086fc1214a2926c9c7cda29605f7ce28b3bb9dd87e50fc6af106b7f`.

The actual log starts with b833 and Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Both builds complete successfully
(3,475 and 3,467 jobs). All 110 distinct configured modules have matching
lint-pass and module-axiom-pass markers, including normal and slow lint.
The full 1,774 complete axiom records were parsed, checked for unique names
and compared with both the per-module declaration totals and the final audit
count. Every set is contained in propext, Classical.choice, Quot.sound.
The log ends with EXACT_LEAF_VALIDATION_PASS modules=110. No Lean compiler
or lint error/warning diagnostic was found. All three changed modules and
all 16 new public declarations occur in the actual output.

M06-support-rates-axioms.log copies those 16 complete declaration records,
including their original line wrapping, from the actual target log. They
all report the three allowlisted axioms. This is a selected excerpt, not
all 1,774 records or an independent newly run audit. Excerpt SHA-256:
`188f6cc81602781922d1e70632d21a8f8354c6f74427c6a91b62f357cf826d09`.

The earlier f14 failure is not reclassified as success. Its missing
not-false simplification and set-indicator normalization mismatches were
repaired without changing statements, premises, original code or gates.
The new actual compiler/lint output, not the mathematical plausibility of
the repair or the integration parent's pass, establishes this result.

## Full CI — actual job and artifact output inspected

Run 36277876544; job 108504133348; artifact 10918131435; job success.
Verified ZIP SHA-256:
`ef4abbb5cff82fa89e3161b41206972b27fb170cf91847718a4cd0265ac629ec`.
The actual job checks out b833 and completes the full library build,
compiler-backed inventory, phase 1/2/3 architecture, full lint and tracked-file
cleanliness. The artifact's ci-source.txt independently identifies b833.
The following are hashes of the actual ZIP entry bytes:

- ci-source.txt: `3e86a6bf878d501673f9bfa2d12329a0f100a01efa8b35cd777052f6738297b7`
- ci-inventory.log: `8e2ef7126029de8530870829372808582c6ada37a1ecd529b7fbbe87463151d8`
- ci-lint.log: `de33a6529311a116ce348782d4359ee4ef6b07fd3a7df333c6fa5ce64af9da33`
- ci-phase1.log: `27e3ad05672a11917f23549bdaf591eb06f333115b37b156fbeeb6a258572d7b`
- ci-phase2.log: `bd26f72d86e1419a87d29896137dbaaf091fb71b728ffcc2168bbeead440701c`
- ci-phase3.log: `1328da901759ab2f0d7bcbc3b07e7edc53f3b762e50c5011f6812ad661fdeb34`

ci-lint.log contains the successful 4,047-job lint-target build and
`Linting passed for GameTheory.LintAll.`. Inventory reports
REUSE_COMPILER_TYPES_PASS declarations=23 and INVENTORY_STRUCTURE_PASS 3054;
these do not prove source applicability. All three architecture logs report
VERIFIED=1; phase 3 reports maximum library line length 100 and zero lines
over 100. Equal inventory/architecture log hashes across baseline and repair
are not reused source evidence: the new job and source file identify b833,
while unchanged audit statistics legitimately produce equal output bytes.
Runner Node/action deprecation warnings are infrastructure messages, not
suppressed Lean diagnostics. Not every infrastructure message is warning-free.

## Source inventory and local arithmetic

Run 36277876557; job 108503997761 succeeded. Its actual job log identifies
b833 and includes the pinned-source/inventory checks and all 112 passing
Python tests. The original 3,054 source items and pending obligations were
not changed to accommodate the implementation.

The exact repaired source also passed local Python discovery with warnings
as errors, 112 tests. The local log SHA-256 is
`374348b7705b000b4374eaa1a39bb34c1bf4dc3c81a8df6c2056b26d4c567508`.
The five new support controls include 16,384 exhaustive exact-rational
finite-kernel cases, supported reweighting, zero-fuel incoming defects,
wrong-prefix undercharging and rare/impossible model outcomes. These tests
are arithmetic/adversarial evidence, not a replacement for Lean proofs.
No local Lean, Lake or PowerShell execution is claimed.

## Exact source snapshot

Run 36277876590; source job 108504099412; artifact 10917737140 succeeded.
Verified ZIP SHA-256:
`3a4bd7474fe4b5f1e6f30374189b13f63a611d310a4baf227da4ada2a4d2b79a`.
Verified rebel-source.tar SHA-256:
`4811209dd154b071b6fc3d45a94183e8f168cd30148cc09d018c774ab8bda02b`.
source-commit.txt matches b833. The archive has no .git directory; all four
implementation blob hashes were recomputed from its bytes and match the
subordinate coverage manifest. Source inspection is not local compilation.

## Global ReBeL — still pending at this checkpoint

Exact b833 run 36277876590; diagnostics job 108504099546.
Its architecture, source/inventory tests and rational runtime steps have
completed, but the compiler/lint/transitive-axiom stage is still running.
Only the source snapshot artifact is available at this checkpoint. The final
global compiler artifact has NOT yet been inspected and global success is
NOT claimed. The separate evidence branch leaves this source run undisturbed.

The next check is to fetch this run's jobs and artifacts through the GitHub
plugin, then inspect the exact source SHA, successful build, all 253 lint
markers, every complete axiom record, final REBEL_VALIDATION_PASS,
architecture and rational runtime artifacts. Retain and repair any real
failure; do not fill an expected declaration count into a missing log.
The earlier 7326 global pass belongs to the integration baseline only.
Documentation-HEAD workflow results likewise must be distinguished from b833.

## Semantic result and uncompleted bridge

The accepted target result is a fixed-profile finite-continuation support
rate using canonical FinDist and actual runBehavioralFrom kernels. Its zero
rate requires explicit primitive support inclusions; it does not assert that
arbitrary independent re-solving or every unknown opponent satisfies them.
The live child consumer removes only incoming unsupported mass, not all
opponent-model discrepancy. A genuine supported model posterior is not an
identification with the actual posterior.

Full schedule first-exit composition, small quantitative leakage rates,
changed-PBS native/late gaps and the signed CarriedResolveStepBounds value
inequality remain separate obligations. No dropped finite-T term, event-mass
floor, learner convergence or child Nash premise is substituted for safety.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
