# M06 counterfactual envelope: exact-source validation and restart evidence

This records a compiled dependency slice, not acceptance of M06 or of the
paper-faithful recursive solver. The exact proof source is
`5aeb2d18027e6c89b0a5889fbca7192f322d6783`, preserved on
`rebel/m06-counterfactual-envelope-20260921`.
The documentation-only restart branch is `rebel/m06-envelope-checkpoint-20260921`.
Read its actual remote HEAD before editing. No force update or main integration.

## Saved stages

All seven implementation/repair commits descend from
`ce55384a01cd91b6d8070314074f46690462a25f`, with zero commits behind that base.
The previous STATUS is archived as M06-status-before-envelope.md with identical
blob `3912632e8a153cfe02a603b078e5165461aa2520`. Main remains
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`, accepted through M05.

| Commit | Stage |
|---|---|
| b6eb062198f55cdb689d366429350fad7568fbda | Save the source-directed envelope scope and initial CI observation. |
| 52daf0719da1afae0e61e4d91ba447b6ca75b64b | Save the opponent-reference envelope and prefix-law bridge. |
| 12f801cd8d7265cbbfbbdee08c77e018e864bffc | Add the new target without removing any inherited target. |
| 4f00e36b4bc6af877ba66d7c169fbcc47d0fdfd2 | Add the global/actual-driver proof, controls, complete registrations and restart record. |
| 1f287213478a704ea9317499f342deb4525c58c7 | Use canonical expectation linearity; add the positive-type Nash non-implication control. |
| 4b2546171d71ae6f836a34b93f43f0447a35558a | Discharge the two concrete Fin 3 comparisons without changing their statements. |
| 5aeb2d18027e6c89b0a5889fbca7192f322d6783 | State the zero-sum helper's type directly, retaining the frozen zero-transport budget. |

## Successful target and supplemental checks

Exact-source run `35539104136`, job `106153413336`, completed SUCCESS.
The pinned toolchain reports Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Commands are `lake build $(cat scripts/rebel/m06-targets.txt)` followed by
`python3 scripts/rebel/audit_exact_leaf.py`.

All 68 declared targets built: `Build completed successfully (3394 jobs).`
The supplemental module build also succeeded (3386 jobs). All 30 recorded
Batteries module-linter runs passed, including the traced simpNF and
unusedArguments checks. All 324 complete, unique transitive axiom records
were inspected, including multiline records and private/generated declarations.
Each set is a subset of `propext`, `Classical.choice`, `Quot.sound`.
The final marker is `EXACT_LEAF_VALIDATION_PASS modules=30`.
There are no compiler error or warning records in this successful target log.

| New module | Inspected declarations |
|---|---:|
| CFRDResolveEnvelope | 11 |
| CFRDEnvelopeSafety | 6 |
| Examples/CFRDEnvelope | 15 |

These 32 records include generated equations and private helpers; the authored
source adds nine general theorems and seven example theorems. Module ownership
is taken from the compiled environment, not inferred from name prefixes.
M06-envelope-axioms.txt is a labelled normalized excerpt of all 32 new-module
records, not the byte-identical complete target log.

- Target artifact ID: `10614740458`.
- Artifact name: `m06-targeted-5aeb2d18027e6c89b0a5889fbca7192f322d6783`.
- ZIP SHA256: `f8df7f5f601f15787695a1565d091d4b98b1da1c6caf5d9d743d884f7c0efc55`.
- Full raw target-log SHA256: `e5b6a49209b5331f915f919d2d144903162102ec978e4a6f01e25d718c9cb57b`.

## Other exact-source checks at this recording checkpoint

| Source | Check | Run / job | Observed result |
|---|---|---|---|
| 5aeb2d18 | Source inventory | 35539104109 / 106153374527 | SUCCESS |
| 5aeb2d18 | Full repository build, lint, architecture | 35539104112 / 106153412444 | Running; not claimed passed. |
| 5aeb2d18 | Full ReBeL compiler, lint, transitive axioms | 35539104111 / 106153374451 | Running; not claimed passed. |

The latter's line width, static architecture, ledger/inventory/adversarial
fixtures and rational Lean runtime with independent response checks already
passed. They are intermediate successes, not completed full verification.
The evidence branch has separate runs; later documentation checks must not
be confused with the exact proof-source run IDs above.

## Observed failures and unchanged gates

At 12f801cd, run 35537380417 rejected the retained control's function rewrite;
the generic stopped-fiber/reweighting/prefix proofs had built. Functional
extensionality repaired the rewrite without weakening its statement.
At 4f00e36b, run 35538009258 rejected an unavailable expect_neg identifier;
expectation of negation was instead derived from canonical expect_smul.
At 1f287213, run 35538490501 built both general modules and rejected only two
concrete finite-index comparisons in the examples. Explicit decidable Fin 3
inequalities repaired them at 4b254617.

The full ReBeL job on 4b254617, 35538795507 / 106152552209, rejected a source
`change` tactic under the frozen Analysis transport budget. The next repair
states the helper equality's type directly. The actual final-source static
architecture step passes. Neither the measured budget nor its checker was
changed. No theorem statement, allowed axiom, action/dependency pin or lint
setting was relaxed, and no adversarial test was removed.

## Reproducible source and offline checks

Source snapshot artifact `10614021651` comes from run 35539104111 and names
exact commit 5aeb2d18027e6c89b0a5889fbca7192f322d6783.
Snapshot ZIP SHA256: `70a30e3d5b6d6d88deea1b4c8117b527ecbd12be823b0deb6c07ab2582283433`.
Contained source TAR SHA256: `95daa633809b7f5cd2a649f57c8c80e565ee6d7000b784df9faf3ba35367ce5f`.
The source marker and archive hash were checked. All six changed code,
registration and supplemental-auditor files match the authored bytes exactly.
Offline processing uses plugin-downloaded source only, not local Git or direct
GitHub access.

`python -W error -m unittest discover -s scripts/rebel/tests -v` passed all
76 existing tests. Coverage and inventory structural checks passed. All 506
non-Experimental Lean files satisfy the unchanged 100 UTF-16-column limit.
All inherited umbrella imports and 65 prior targets remain; three targets
and three supplemental audit consumers were added.
Original coverage.json, lake-manifest.json, lakefile.lean, lean-toolchain,
.github/workflows/rebel.yml and scripts/phase2-audit.ps1 are byte-unchanged.
The 3,054 original coverage rows remain: 64 verified, 41 qualified, five
refuted, 406 context-indexed, one empirical record and 2,537 pending. These
counts are not a completion percentage or a substitute for semantic review.

| File | Git blob | SHA256 |
|---|---|---|
| CFRDResolveEnvelope.lean | 4c5c45038df77a7b8890ec50681bc1f3c11bc3c0 | 88bf0979e0f29ebe5413a0ee82403ad8659ea6279ecf231a1491c8c12887074d |
| CFRDEnvelopeSafety.lean | 8356423e0e0e0379bbc105cb4145dc8f1dfabacf | 8faf9298dab867a6c5b8dcaefa23879d4a586b86c6f2c0bb41b3cfef438f977a |
| Examples/CFRDEnvelope.lean | 0de4d81ce0498cb834dc220888966e7981ce6cf1 | 33a62b8f5e2ad5bd2059bf87039de139dbbfb3fb2d777c745345d4e4cbe222cd |
| Analysis/ReBeL.lean | 8f6bf8c2720246eb6920ba5cf1108b442f958260 | 05aabc728a7c0fa190910b19969da23fb6404b924667463cc9330d939a9f71b0 |
| m06-targets.txt | f2a99648a603028c7855761cf8ff9ce5a002e5aa | c2e08fd2d568a10501380f5dbe76b5dc7a5a7d20e95a86d3a8461b8ef75593fd |
| audit_exact_leaf.py | afb5cda1faa8a145f17b2668bfa4644a85172c56 | 9fa5f953042affa97712069bdcbfcb40cc4d000a9ef55ac3620640117ceb8efa |

## Resolved inherited verification

At the base ce55384a, full repository CI 35535912944 / 106144785492 and full
ReBeL 35535912927 / 106144785441 succeeded. The downloaded latter log contains
3,593 complete unique transitive-axiom records, all in the allowed set, and
ends `REBEL_VALIDATION_PASS modules=177`.
Baseline validation artifact `10613288740` ZIP SHA256 is
`ffd42a08804cc4789209b0ffddafd73c1cc96f26d5820b870b368011575b3b99`;
its full raw log SHA256 is
`119b5a291b3489e4acdd8389c2bbec3ff8ee985827dd063b0722c28ee3574785`.
This resolves the initial running observation without inheriting baseline
success as evidence for later source.

## Semantic acceptance boundary

See M06-envelope-semantics.md for the proved comparator, exact instances and
remaining coherent recursive construction. The new final theorem is a
conditional global-security bridge; the local opponent envelope is still a
sufficient solver obligation. The live finite-child instance RETAINS its
constructed continuation. A separate changed-policy matrix control shows
why preserving fixed-opponent exploitation is unnecessarily strong, while
the same-PBS positive-type counterexample rules out arbitrary Nash selection
as an automatic source of coordinatewise continuation ceilings.
No original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR or SAFE-THEOREM3 parent
is promoted. The bounded-refresh variant and all prior negative controls
remain. No M06 completion, paper-faithful recursive closure or main integration.
