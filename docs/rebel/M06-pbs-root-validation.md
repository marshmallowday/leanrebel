# M06 PBS-rooted CFR exact-source validation

## Scope and immutable source

This evidence accepts the six-module dependency slice at
`d693b30eddbf5a2d523c92d2308f51879f4c28d4` (tree
`535d6a356d30ff3f0788b27ad193450b0d846f20`) for its stated native rooted-game
and original-to-root execution theorems. It does not accept the four original
M06 parents, a reverse solver-output correspondence, recursive independent
re-solving safety, or an executable refinement.

The proof source remains on `rebel/m06-pbs-cfr-20260921`. The evidence-only
child checkpoint is on `rebel/m06-pbs-checkpoint-20260921`; read its actual HEAD.
The source is 11 linear saved commits beyond inherited checkpoint
`8c065784a76ad1de8fc6542dad336f4edfe9f66f`. Main remains M05's
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. No force update or history rewrite.

GitHub source, commits, branch updates, workflow results and artifacts were
accessed through the GitHub plugin. Offline processing only inspected the
plugin-provided archives and ran Python/static checks; no local git operations
or local direct GitHub access were used. Lean compiler evidence comes from the
actual repository workflows, not a local substitute.

## Successful exact target, lint and axiom evidence

Run `35550519612`, job `106184279972`, completed with SUCCESS, including all
steps. Its actual head SHA is the proof source above. Artifact `10618207018`
contains the inspected complete `m06-targeted.log` (246,149 bytes).

| Evidence | SHA256 |
|---|---|
| Target artifact ZIP | 9813376fc13b853fb214c7b8f75c6fe33c9f1403b833d4dfbc09834f963d8fd0 |
| Complete target log | 700fc6f7bcfbce7b802d3858d0d4601584c1ce77f1b6c8232c1bb38a5e19a41f |
| Source artifact ZIP, artifact 10618181457 | c796b4e308bb2dfb1c1e312ca51d3f8235ccfad84ccae3a4b5deee544abfd137 |
| Source tar inside that artifact | 8ff99fd64423c09a132099b3449353a3ab9eb5f40a725a73e5a87f9f7ae4ccb2 |

The source artifact belongs to run `35550519618` and its recorded commit marker
matches d693b30e. The source contains 79 declared M06 targets; the target build
completed 3,405 Lake jobs and the supplemental dependency build 3,397 jobs.
All 41 named supplemental modules passed every normal/slow Batteries linter.
There are no Lean error or warning records. The final markers are:

```
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=468
EXACT_LEAF_VALIDATION_PASS modules=41
```

All 468 complete dependency lists were parsed, including wrapped records, and
the declaration names are unique. Every axiom is in exactly the allowed set
{propext, Classical.choice, Quot.sound}; no additional axiom is allowed. Of
these, 112 records belong to the six new modules, including generated/private
declarations. M06-pbs-root-axioms.txt retains all 112 as a labelled normalized
excerpt, not as an alleged byte-identical raw log.

| New module under GameTheory.Analysis.ReBeL | Audited records | Source SHA256 |
|---|---:|---|
| PBSRootProtocol | 27 | 2a095157ca75030d825747ad02d3a938b2eede77b6936657df62e8a0d5320c42 |
| PBSRootInformation | 11 | 34bbd2e30f1d1d30a2fe6c7f60160ffaa0db9f465adcfb7b9f49478b89cdc20d |
| PBSRootCFR | 14 | 8f3c52d0fd5db86f49811180e059f281852d1e2cfc33765264e1449b2ab4fdb5 |
| PBSRootExecution | 17 | 09b426b9377e63eff0b88f8502d6c4b9c6f34134d4241c01156adbe4a2c06f25 |
| PBSRootBehavioral | 11 | 5cce7fdbbcc20e500d03d004544514f4b2ddf5481d8987a488e94032dc729ee4 |
| Examples/PBSRootCFR | 32 | e68cc7f5b5ad0c99f54ffbf33d98aed40096a239cdf50622c6cd7dabdd1cbd95 |

The authored six modules contain 23 general theorem declarations and seven
example theorem declarations. The 112 audit records also include definitions,
instances and generated declarations; those counts must not be confused.

## Wider validation and unchanged gates

Full repository CI `35550519628` / job `106184318263` and full ReBeL run
`35550519618` / job `106184325607` remain RUNNING at this evidence recording.
The latter's line-width, static architecture, ledger/inventory/adversarial
fixtures and independent rational Lean runtime steps passed. These successful
steps, the source snapshot, and the targeted supplemental audit do not imply
full-workflow success. Re-read the exact-source final results before integration.
The evidence-only child has its own workflow state and is not substituted for
the proof source's results.

Both full workflows of the inherited 93b60fbd proof source were checked to
actual completion: repository `35545208101` / `106169800893` SUCCESS and ReBeL
`35545208160` / `106169767571` SUCCESS. Older pending status text is historical.

Offline exact-source checks also passed: all 76 existing Python tests with
warnings as errors, coverage and inventory structure, and line-width inspection
of 517 non-Experimental Lean files. These checks are not Lean kernel evidence.
The new modules and registrations match the exact source archive. Removing
only the six appended module registrations makes the analysis umbrella, M06
target list and supplemental auditor byte-identical to their inherited source
versions. No previous import, target, audit consumer or counterexample was
removed. The expanded original coverage ledger remains 3,054 rows unchanged.

Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and Batteries
4488d40d070b9700d4d5a6aa342f0d40c31b2a2d remain pinned as inherited. Workflows,
architecture gates, allowlisted axioms, prior proof files and prior tests are
unchanged. The only modified old Lean file is the import-only analysis umbrella.

## Repair provenance, not suppressed failures

The saved source path includes failed compiler checkpoints. They remain in
history and are not claimed as successful. Initial root support binders and
rank inference required explicit types. Local menus needed Option reduction.
Repository architecture required reducible carrier adapters and removal of an
authored transport tactic; the gate itself was not altered. Runner proofs
needed explicit protocol arguments and removal of redundant closing commands.
The behavioral chooser proof was restructured at a general indexed trace to
avoid dependent elimination failure, then corrected to retain its state index.
No theorem conclusion or substantive hypothesis was weakened by these repairs.

At `b6e802f66eb351ff77fba3b2e1275e930e1a9f29`, run `35549994477` /
job `106182824917` passed all target compilation and all 468 axiom records,
but the whole job FAILED because three local-instance docstrings were missing.
Only 37 of the 41 module lints had completed at that point. Artifact
`10617929523` has ZIP SHA256
dab7fd120cca11cc4e65bc9bcaeff904d1bc909d0e61ef29855f0a194fc936cf.
The raw preceding log SHA256 is
1e6cdc2b848b8ee4aa4376d7c550378d2b7f0427a6f666cbfe7a6c72e6916953.

The final d693b30e adds those three explanatory comments and the corresponding
fixture instance's comment. Exact archive comparison verifies that these four
comments are the only change from b6e802f6: no proof or gate changed. The final
run nevertheless recompiled and reran all 41 lints and the complete axiom audit.
Every named axiom dependency record equals its b6e802f6 counterpart. No nolint,
sorry, admitted fact, unsafe evaluation or relaxed architecture gate was used.

## Next original M06 obligations

M06-pbs-root-coverage.md records the exact semantic boundary. Decode arbitrary
new native CFR output at a genuine PublicBelief back to an original full-AOH
policy, using the common public cut; prove every baseline and unilateral law
and expectation before transporting the native Nash bound. Then construct the
parent's counterfactual/type-conditioned child value and iteration families and
the independent recursive re-solving correspondence. Preserve positive error,
zero-reach completion, finite-T residuals and the printed/corrected Theorem 3
separation. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending, and the inherited finite-plan/coherent-redraw constructions remain.
