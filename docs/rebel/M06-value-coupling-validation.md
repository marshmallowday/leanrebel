# M06 directed payoff coupling: compiler loop

## Preserved initial source and failure

Initial source commit: `2315de77ab803044df1781da60edc9dfae57d124`.
Target run: `36102450137`; job: `107967658356`; conclusion: FAILURE.
The job used Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

The exact-source snapshot artifact `10849926260` was downloaded through the
GitHub plugin. Its ZIP SHA256 is
`930231d0c0f2595eda93a83a48926577a974145110a80808b5478f8b2b8fb80b`.
Its source-commit.txt matches the initial source SHA. All three new Lean files
and all three harness edits match the locally inspected bytes exactly.

Target diagnostic artifact `10850295940` was downloaded through the same
plugin. ZIP SHA256:
`2945bc9b1729639d71f401080278f3c7a73f755d296b15f8d0071dbd509b89b2`.
The full log was inspected. It reports exactly one source error, at
GameTheory/Math/Probability/FinDistValueCoupling.lean:28:2:
`simpa only [expect_const] using lower` did not unfold the target's
`directedValueCost` definition. The expected lower-bound expression and the
conclusion therefore did not match under that simplification.

The dependent new ReBeL module and its example were NOT validated by this
failed build. Supplemental lint and transitive axiom audit were skipped.
Do not report the run as successful or infer acceptance from unchanged
predecessor modules compiling.

## Focused repair

Add `directedValueCost` to the explicit simp-only list in the nonnegativity
proof. No statement, premise, conclusion, definition, example or consumer is
weakened. The repaired math blob is
`96ec781982fb90ab484008b34b92a5f9d9c0d8c5`; its locally computed blob hash matches
the GitHub plugin's create_blob result.

The repair requires its OWN exact-SHA target build, lint and transitive axiom
inspection. At this checkpoint those results are pending. Existing source
branch is `rebel/m06-value-stability-20260925`; the initial failed commit stays
in its history. No local Git command or local GitHub request was used.

## Static results (not Lean validation)

Coverage and inventory structure checks passed for 3054 expanded entries.
All 76 Python tests passed under `python3 -W error -m unittest discover -s
scripts/rebel/tests -v`. The target list retains 131 old targets plus 3 new;
the supplemental audit retains 93 old modules plus 3 new. The analytic umbrella
also only appends the new modules. Existing coverage.json is unchanged and its
M06 parent statuses remain pending. No gate, whitelist, pin or test is removed.

M06 remains incomplete. The scoped companion ledger distinguishes this
conditional coupling bridge from the still-required native small-value-rate,
late-training, first-exit and carried-PBS re-solving obligations.

## Second compiler result and consumer repair

Repaired-math source: `6d2ede1e302e3acab3639b906c3830f225c628fb`.
Target run `36103010338`, job `107969383203`: FAILURE. The full downloaded
artifact `10850680906` has ZIP SHA256
`6cfc06cc2a0853f8caef79299d7febff2c479129628964eb0009df30a7520871`.
Its log explicitly reports that FinDistValueCoupling and CFRDValueCoupling
compiled. The example then failed at line141 with `dsimp made no progress`.
This is a different failure from the first attempt; the math repair worked.
Supplemental lint/axiom validation was skipped because the example failed.
Inventory run `36103010297` succeeded, which does not replace Lean validation.

The next repair removes only `dsimp only at comparison` before the existing
arithmetic proof. No theorem statement, marginal condition, cost bound,
positive/negative control or harness target changes. The new example blob is
`6a061ab78e262e928850bb5c556d32fccee467b3`.

## Third candidate identity

Source commit: `4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5`.
Source tree: `6138146dce7e2c24165b1157f92b4ccaf623e573`.
Target run `36103763186`, job `107971683742`.
Independent ReBeL run `36103763078`.

The source artifact `10849759412` was downloaded through the GitHub plugin;
its ZIP SHA256 is
`7414d668e008adf136c3e0c12c70334b5b59691079560e22cd136780ae79b0c9`.
The embedded source-commit.txt matches the third candidate exactly. All three
new Lean files, the analytic umbrella, the M06 target list, the supplemental
audit script, and unchanged canonical coverage.json byte-match the reviewed
local source. New module blobs are:

- FinDistValueCoupling: `96ec781982fb90ab484008b34b92a5f9d9c0d8c5`.
- CFRDValueCoupling: `3e8c3a97fa25523ec08bc12da5ac1ef6c4a5c97c`.
- Example: `6a061ab78e262e928850bb5c556d32fccee467b3`.

The final outcome below supersedes the pending labels in historical entries,
not the preserved failure history.

## Validated conditional slice at the third candidate

The target job `107971683742` in run `36103763186` completed SUCCESS at source
`4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5`. Both the declared-target compilation
and the constructed-child validation steps succeeded. The downloaded
artifact `10851055531` has ZIP SHA256
`7aabb2cc78b9d223d955436d75db1fe2cdd54e6764dba6167fe47b1f5e83ea4d`.
The extracted `m06-targeted.log` has SHA256
`25e35940c344bf8faa6e6dc9bb73accb91696d9e6e14d500cc93fd01537ce11e`.
Its first line is exactly the validated source SHA; the pinned toolchain is
Lean 4.33.1, compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

The actual commands were:

```text
lake build $(cat scripts/rebel/m06-targets.txt)
python3 scripts/rebel/audit_exact_leaf.py
```

All 134 declared targets were included. The latter script separately built
its 96 retained/new modules, audited every declaration's transitive axioms,
and ran the normal/slow Batteries linters. The full log was inspected and
all 1527 complete axiom lists were independently parsed, including wrapped
lines. Every set is contained in {propext, Classical.choice, Quot.sound}.
There are exactly 96 distinct module lint-pass markers and no source error
or warning diagnostics. The final exact markers are:

```text
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1527
EXACT_LEAF_VALIDATION_PASS modules=96
```

New module counts are FinDistValueCoupling=6, CFRDValueCoupling=3 and its
example=27, including private/generated declarations. All three have explicit
module axiom and lint passes. `M06-value-coupling-axioms.json` preserves all
36 new-module axiom outputs, not just a statement that the tool passed.
The plain text log has 9064 lines and 623735 bytes; the artifact hash above
anchors the retained full output.

The exact-snapshot source was also rechecked offline: ledger/inventory
structure passed again, and all 76 Python tests passed under `-W error`.
These remain structural/numerical checks, separately from the Lean proof.
Inventory CI `36103763176` completed SUCCESS at the same source SHA.

## Wider gates and resumption boundary

At checkpoint assembly, independent ReBeL run `36103763078` (diagnostics job
`107971751432`) was still in progress in the all-ReBeL compile/lint/axiom step.
Its source snapshot, static architecture, ledger/adversarial fixtures and
rational-solver response checks had succeeded. Do not treat this partial
progress as the all-ReBeL validation pass; inspect that exact run before
continuing. No background monitoring or later report is implied.

Full CI `36103763182`, job `107971742837`, subsequently completed SUCCESS.
The downloaded audit artifact `10851056189` has ZIP SHA256
`5bb448cc49b933cb9225fe6c9cb12b566572d7da7169307107caf00872ed553a`.
Its ci-source.txt is exactly the validated source SHA. All three inspected
architecture logs end with VERIFIED=1. The public-library log records
`Linting passed for GameTheory.LintAll`; the job also passed the full build,
inventory/compiler-signature checks and tracked-file cleanliness gate. The
Windows-only setup step was intentionally skipped on the Linux runner. The
full-CI success is distinct from the independent ReBeL census still running.

The documentation checkpoint is on `rebel/m06-value-checkpoint-20260925`,
based directly on the validated source. The original source branch
`rebel/m06-value-stability-20260925` stays at the tested SHA so these in-flight
source checks are not canceled by documentation updates. The checkpoint
changes only documentation/evidence. Main and predecessor branches are not
moved. Checkpoint provenance and all failed compiler attempts remain in GitHub.

The accepted scope is the conditional payoff-coupling bridge and its hostile
controls, NOT M06 completion. Native small-value/late-training rates, later
independent carried-PBS re-solving, native first-exit bounds and
CarriedResolveStepBounds remain open implementation obligations. The canonical
M06 parent statuses are unchanged. See the companion coverage and semantic
review for exact assumptions, source locators and limitations.
