# M06 coherent execution: exact-source validation and restart evidence

This is a verified execution-refinement dependency slice, not acceptance of
M06 or the original recursive child-CFR correspondence.
Proof source: `93b60fbdc3fe6539a7688124baa9be80b86602c1`, preserved on
`rebel/m06-coherent-recursion-20260921`. Continue from the evidence branch
`rebel/m06-coherent-checkpoint-20260921`; read its actual remote HEAD.
Evidence-only commits do not change proof source or interrupt its full checks.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098` (M05 accepted).

## Saved stages and continuity

All source commits descend from the actual restart
`ff7f61510c38a5681c06a7431a7811e3f6fbcbf7`; older chat checkpoints were not
replayed. No force updates, history rewriting or main integration occurred.
The preceding STATUS is preserved byte-for-byte in
M06-status-before-coherent-child.md, blob d0bc31710bd781b20e1b18e61849eaa91bced8b9.

| Commit | Saved stage |
|---|---|
| af8078daf32f152ce3e4c75f05076a4481e44673 | Baseline validation and coherent-child restart. |
| 89eef8e585ed86968cd0c2a2361147a0ddaf9ecd | Finite-plan draws and every-root unilateral laws. |
| e965412ccad7ee42f03e50a4d6b6dfb832c3c3d1 | Actual finite-child noisy recurrence, envelope/security, six controls. |
| fe38ca1de17c8a1e4083b34def9b3c92145842bc | Arbitrary finite schedules and two multi-stage controls. |
| d095b2cff48922e34eb28d5df8e66168bf68b148 | Restore the inherited Examples.ValueKink umbrella import. |
| 393f2c1a43317928b7d176ac60c130c0a2a6d185 | Repair stage projections and zero-fuel induction base. |
| 93b60fbdc3fe6539a7688124baa9be80b86602c1 | Replace a disallowed transport tactic with definitional simplification. |

## Successful target-SHA compiler, lint and axiom checks

Lean toolchain remains 4.33.1, pinned as inherited. The commands were
`lake build $(cat scripts/rebel/m06-targets.txt)` followed by
`python3 scripts/rebel/audit_exact_leaf.py`, with unchanged strict audit rules.

At 93b60fbd, run `35545208144`, job `106169798608` completed SUCCESS:
73 M06 targets; 3,399 Lake build jobs; 35 supplemental module lints; 356
complete unique transitive-axiom records. The entire target log contains no
Lean error or warning records and ends `EXACT_LEAF_VALIDATION_PASS modules=35`.
All axiom lists, including wrapped and generated/private records, are subsets
of `propext`, `Classical.choice`, `Quot.sound`. The five newly added modules own
32 audited records and contain 14 general theorems and eight example theorems.
Individual pure-plan safety is not one of these theorems.

- Artifact ID: 10615849050.
- Archive: m06-targeted-93b60fbdc3fe6539a7688124baa9be80b86602c1.
- ZIP SHA256: 3eac48ca1a51df83c1d64ce1286de08ad96c65af2e0b990cb1e82e279f1f358a.
- Raw complete log SHA256: 9edad14c6095086cbdf9e1ce23c5751448a3052548ac17f35e01e8e7942e26ae.

M06-coherent-child-axioms.txt is a labelled normalized excerpt containing all
32 new-module records, not a file claimed to have the full raw-log hash.

The single-cut predecessor e965412c independently passed target run
35544309611/job 106167437931: 71 targets, 3,397 Lake jobs, 33 supplemental
modules and 346 complete axiom records. Its target ZIP hash is
3cf3f4d1cda670aa49093886c38d8426c8b6a920d05e8a478441c9ff9f81ef90;
raw-log hash 680bb19614b63ad2a03bd2ad72c8a1662834e1490e24faf7f640bfe226548c86.
This did not validate its accidentally mistyped umbrella import. That defect
was caught by source comparison and fixed in d095b2cf, not concealed or inherited
as a successful full build. The final umbrella preserves every original import.

## Full workflows at the recording checkpoint

| Source | Gate | Run / job | Observation |
|---|---|---|---|
| 93b60fbd | Full repository build/lint/architecture | 35545208101 / 106169800893 | Running; not accepted as completed. |
| 93b60fbd | Full ReBeL compiler/lint/transitive axioms | 35545208160 / 106169767571 | Running; not accepted as completed. |

The latter's width, static architecture, pinned dependency fetch, ledger and
adversarial fixtures, and independently checked rational Lean execution have
passed. These intermediate steps do not constitute full-workflow success.
The documentation checkpoint has separate checks; do not confuse their SHAs.

## Failures and repairs preserved

At fe38ca1d, target 35544641444/job 106168271815 rejected a carried-stage
conditional after insufficient reduction of its fuel/resolver projections,
and the nil induction proof did not close the zero-step runner. The nil case
is now reflexivity. Projection reduction occurs before conditional rewriting.

At 393f2c1a, full ReBeL 35544968401/job 106169172521 correctly failed the
frozen `TRANSPORT_ANALYSIS_SOURCE` gate (expected 0, got 1): the attempted
proof repair used `change`. Its target compilation succeeded but the later
supplemental job was cancelled by the next repair; it is not a successful
complete run. Final 93b60fbd instead uses `dsimp only` on the definitions.
The original architecture script and expected budgets are byte-unchanged,
and the static gate passed at this exact final source. No theorem statement,
allowed axiom or verification gate was weakened to repair either failure.

## Reproducible source and offline checks

Exact-source snapshot: artifact 10616636654 from run 35545208160;
ZIP SHA256 54ca25282a3d726a6ee224c7e39d2355becd9b6aea89ce880564d8f95bcd15c3.
Its source-commit.txt is 93b60fbdc3fe6539a7688124baa9be80b86602c1.
All five new proof/example modules and the three registration/auditor files
were compared byte-for-byte against that snapshot. Offline work used only
plugin-retrieved data, without local git or direct GitHub network access.

On this exact snapshot, all 76 existing Python tests pass with warnings as
errors. Coverage and inventory structure checks pass; 511 non-Experimental
Lean files have zero UTF-16 line-width violations. These tests are not Lean
kernel evidence. The original 3,054 expanded coverage rows remain unchanged;
the 64 verified/41 qualified/five refuted/406 context/one empirical/2,537 pending
counts are not completion percentages. All original targets/imports remain.
The toolchain, Lake dependencies, workflows and phase2-audit.ps1 are byte-identical
to the base. Only five new modules were added to each registration list.

| New source | Git blob | SHA256 |
|---|---|---|
| CFRDCoherentDraw | `dade3daff9a4504e2ea0d6bd4cfd3d37b03de19a` | `135f81f660b8a0ef0f6b2aaa39fe91f50f4ea7bf56720dbccfb760394232386e` |
| CFRDFiniteCoherent | `48c6f3eb78f5448cb4e485e47cb2f3b39298f763` | `e33d13bbfafb59311fd91e393489fbb4d9e350179c5efd37fd1d30b9879d136d` |
| CFRDCoherentStages | `8658d335b5a03d975e226a8fbee3e565dc90e5f4` | `fac320537d2c0a5b61cb586d6ac8c22af9fc53e9dfc91e504f2b0f8606b0555f` |
| Examples/CFRDCoherentDraw | `05b27bf94998ba91e6af1214a4e6d60d3954d571` | `88afed8a550c842b40b6aa1ee4c10b5f0da43025f9bfa7f846029b979c0ce771` |
| Examples/CFRDCoherentStages | `b8156d71971bb7538447414426d1fa6a687cdd63` | `5dde1a5154a1e05b0277b2acc3cf5e5407f70f3965ab11b0517a3d0e91daf7f0` |

## Inherited acceptance and semantic boundary

Baseline ff7f6151 full CI 35539749429/job 106155158791, full ReBeL
35539749435/job 106155159018 and inventory 35539749439/job 106155158854 succeeded.
Its full ReBeL log covers 180 modules and 3,625 complete unique allowed-axiom
records; raw log hash 9ab08735c82fd6c8755b8b57f1f758ac938052d70ebe295550de8761e1ab3cbb.
Source and validation archives were respectively 10614042882 and 10614632588,
with hashes recorded in M06-coherent-child-restart.md. This is baseline evidence,
not a substitute for the new source's checks.

M06-coherent-child.md records the proof statements and source correspondence.
The execution now genuinely draws deterministic plans and may redraw them at
multiple live stages while retaining actual private memory and model updates.
Its underlying behavioral family remains the one indexed by the original
private parent iteration. Whole-law identities yield the actual finite-child
security bound without a switching-rate or stage-count penalty.

The original source's coherent recursively computed child-CFR iteration/value
family remains to be constructed at newly reached PBSs. This predrawing
refinement is not uniform child-iteration sampling or independent re-solving.
No original M06 parent row is promoted. Preserve numerical error, child loss,
outer finite-T error and the separate bounded-refresh variant; preserve the
printed/corrected Theorem 3 distinction and every replacement counterexample.
