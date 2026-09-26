# M06 support-rate continuation — validation checkpoints

## Starting point and branch choice

Work starts from the latest integration source
`7326f1e40011b1d4329f09e743491cc7bc7e5746`, not main or the older
public-event branch. The continuation branch is
`rebel/m06-support-rates-20260927`. It preserves the integration source and
both of its parent histories. A separate branch allowed the integration-wide
ReBeL audit to finish without branch-local concurrency cancellation caused
by a new source push. No main update or force push is used.
All GitHub access, artifact downloads and repository writes use the GitHub
plugin. Local operations inspect plugin-downloaded source/artifact bytes
and run non-Git checks; no local Git command or direct GitHub HTTP is used.

## Baseline target — actual evidence inspected

Source: `7326f1e40011b1d4329f09e743491cc7bc7e5746`.
Target workflow: 36275563682; job: 108497496370; artifact: 10916654865.
Verified ZIP SHA-256:
`2eb39d8abe4ed4291a8cdcebaf62ad1e36e798c9f44ebdc4180c6d540b37e63f`.
Extracted m06-targeted.log SHA-256:
`38cff79000dba001308a1724e275bf6ed670f7fc1dc79d0958f62a8adaac8435`.

The actual log identifies 7326f1e4 and Lean 4.33.1. Both builds succeeded
(3,475 and 3,467 jobs), with 110 module lint passes and
EXACT_LEAF_VALIDATION_PASS modules=110. All 1,739 complete axiom records were
parsed; their sets are contained in propext, Classical.choice, Quot.sound.
All six newly integrated tail/example declarations occur in the output.
No compiler error/warning diagnostic or failed target gate was found.
These are combined-source results, not reused parent results or M06 completion.

## Baseline source snapshot

ReBeL run 36275563642, source job 108497538243, artifact 10916773484.
Verified ZIP SHA-256:
`04f9f5b65db04b0e147767f136e02d9d09552996bfe9eca5e373c81c55a69838`.
source-commit.txt matches 7326f1e4. Verified tracked-source TAR SHA-256:
`ec6a4a5b3c19af78d53aa6e84b62d0ad678cc686d26a96890d1d5c5310d9a762`.
The archive contains no .git directory and was extracted for review, not
represented as a local Lean installation or a compiled result.

## Baseline full CI — actual evidence inspected after first checkpoint

Run 36275563654; job 108497657992; artifact 10917472902.
Verified ZIP SHA-256:
`eba37ed51c5dd87253ac7d8bf05fbb37cf0ee6375c374b1cc190a58160e80ede`.
The actual job log identifies source 7326f1e4 and Lean 4.33.1, with a successful
4,277-job full library build, compiler-backed inventory checks, phase 1/2/3
architecture gates, full lint and tracked-source cleanliness.
Artifact logs were also inspected; their SHA-256 values are:

- ci-inventory.log: `8e2ef7126029de8530870829372808582c6ada37a1ecd529b7fbbe87463151d8`
- ci-phase1.log: `27e3ad05672a11917f23549bdaf591eb06f333115b37b156fbeeb6a258572d7b`
- ci-phase2.log: `bd26f72d86e1419a87d29896137dbaaf091fb71b728ffcc2168bbeead440701c`
- ci-phase3.log: `1328da901759ab2f0d7bcbc3b07e7edc53f3b762e50c5011f6812ad661fdeb34`
- ci-lint.log: `12ac86ac3e785f859a66bdb7ae6fab8d45f24b7f2b88f6ebfe1449237add3a2b`

Inventory has REUSE_COMPILER_TYPES_PASS declarations=23 and
INVENTORY_STRUCTURE_PASS 3054; neither claims source applicability. All three
architecture logs have VERIFIED=1, no placeholders/custom axioms, and the
line-width gate reports zero oversized lines. Full lint reports success.
Runner Node/action deprecation warnings are infrastructure messages, not
suppressed Lean warnings. No claim that every job-log message is warning-free.

## Baseline global ReBeL — actual evidence inspected after first checkpoint

Run 36275563642; diagnostics job 108497538005; artifact 10917776193.
The job completed successfully. Verified ZIP SHA-256:
`bdf30fbdcdd07a4de46bb7df6a155afea79c0f8ff39beecc257f052f3010ff7c`.
rebel-validation.log SHA-256:
`5637e3e5f7523390012994586613a1d0493fb2211a8f0b6502a216c7d5b30ccc`.
The actual log starts with 7326f1e4, records a successful 3,511-job build,
253 discovered modules, 253 lint passes and REBEL_VALIDATION_PASS modules=253.
All 4,910 complete REBEL_AXIOMS records were parsed against the three-axiom
allowlist, with no forbidden dependency. The actual architecture artifact
reports VERIFIED=1. The rational runtime report identifies the same SHA and
status pass: 85 histories, 40 local probabilities at each of 0/1/2 rounds,
and all 1,024 pure policies per player. This runtime cross-check is not a
semantic-refinement proof.

## Feature checkpoint f14ec3 — failed target retained explicitly

Feature source: `f14ec3bddd5e61ba3e4eb505cd2c73a37f7f3068`.
Target run 36277385486; job 108502646650; artifact 10916689581.
Verified ZIP SHA-256:
`f23a75632bd174f216baea774e67e25cadb611e21b96d9c5dba4029dbc41a2ff`.
Actual m06-targeted.log SHA-256:
`ae4fae95ce236c20b132dc55b757cd1715e4223ea923116231c39f5d58a78732`.

The exact-source Lean 4.33.1 compiler rejected FinDistKernelVariation.
At line 65, simplifying a negative support premise left `not False` unresolved,
and le_refl consequently became unused. At lines 80, 102 and 103, probability
indicators written using set membership did not normalize to the literal
not-in-support predicate during rewrite/matching. This was a real failed
build, not an accepted theorem. Downstream support consumers and target audit
did not run. The repair normalizes Set.mem_ofPred_eq explicitly and keeps both
sides as expectations until their predicates agree. Statements, premises,
original source, tests, imports and every validation gate remain unchanged.
The repair's compiler, normal/slow lint and transitive-axiom results are PENDING.

Feature source snapshot: run 36277385489, source job 108502809111,
artifact 10917474236. Verified ZIP SHA-256:
`25b6c71fe93bc3a6a6d4cc52cfdc888222f49af974494b5fb541d2c27dec4750`.
Verified TAR SHA-256:
`d3852220d4b99cc6d8e70ba863ff6c1517aa171c61ec198cc00aa9b4ccc8f59e`.
source-commit.txt matches f14ec3. The four feature source files' object hashes
match the committed blobs; only the intended three Lean files, Python fixture
and four status/review/checkpoint files differ from the integration baseline.

Feature source inventory run 36277385509 / job 108502646851 succeeded; its
actual job log was read. It checks out f14ec3 and pinned official source
7960a42750f3407ea9eb2c3333d4c2a7961f6df4, reports 53 official files / 2,578
syntax occurrences, 50 page records / 25 edition pairs, 3,054 unchanged ledger
items, and all 112 Python tests pass. These provenance/arithmetic checks do not
repair or replace the failed Lean proof. The newly added support tests include
16,384 exhaustive exact-rational cases. Prepared-source local Python tests also
passed; log SHA-256 is
`75e53650f1907528d1da58bb492bc9fa5c280d81631e68f60f5a753f605f8b4f`.

Other feature-source resume IDs are global ReBeL run 36277385489 / job
108502809229 and full CI run 36277385501. Their diagnostic states at the proof
repair must not be treated as success; inspect exact logs if needed. A source
repair may cancel obsolete same-branch runs. The completed 7326 baseline audit
is unaffected by continuation-branch writes.

## Remaining semantic boundary and next checks

Read M06-support-rates.md and the subordinate coverage file. First inspect the
repair commit's exact-SHA workflows and repair any remaining proof/lint error.
Do not substitute a parent pass or Python arithmetic for its own Lean audit.
This is a fixed-profile finite-continuation support-rate dependency. The full
independently re-solved schedule, small quantitative leakage rates, changed-PBS
native/late gaps and CarriedResolveStepBounds remain separate obligations.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No learner convergence, support floor or dropped finite-T term claims safety.
