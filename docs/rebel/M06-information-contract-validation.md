# M06 information-set child contracts: exact-source validation

Proof source: 6416eebd9a67645fe94100db744cd4d049d17684.
Preserved source branch: rebel/m06-information-controls-20260921.
Evidence/restart branch: rebel/m06-information-checkpoint-20260921.
The evidence commit changes documents only. It does not replace or cancel
verification of the named proof source, and does not accept M06 as complete.

## Restart continuity and checkpoints

The actual starting source was 30f7dfd33c05a78a70e1a29cb2734cde1af90a02,
not the old b0564668 chat checkpoint. It already contained PBSRootLocalHistory,
PBSRootDecode, PBSInformationCFR and the reverse-decoder controls. Its full
ReBeL run 35557803196/job 106204753163 stopped at a 101-column source line.
The inherited STATUS is saved byte-for-byte as
M06-status-before-information-contract.md, blob dd500031c02ecf8331bf2ea88429d4884a3f2dd2.
Main was retained at 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098 throughout this work.

| Commit | Saved stage |
|---|---|
| 5303cde4f056131faefae72ed2798c1177927f16 | Record the actual inherited source, failure and next construction. |
| 6ee6ae408f80397df17d7d3351d5ea8ad979654c | Wrap the single over-width line without changing its proof or statement. |
| f64cd0b6581dfb83778a84cd1c94aec2ccecc544 | Add finite information-set CFR budget construction. |
| 909455395a64a7733765722dcff1138232b2061f | Register that module in all three validation consumers and save status. |
| a68aea2f1e66b1bc2252e7881e18b79a35b3b25b | Correct the order of addition in the payoff-budget monotonicity proof. |
| c669ef769f1b833fadd8b728b6950b877f6f52be | Connect actual child solves, reference budgets, completion and parent guarantees. |
| 6416eebd9a67645fe94100db744cd4d049d17684 | Add eleven canonical hidden-type controls and all registrations. |

The GitHub compare response reports seven commits ahead and none behind the
starting source. All stages are descendants; no history rewrite or force push.
c669ef76 remains on rebel/m06-information-contract-20260921. A new controls
branch preserved its running checks when the examples were added.

## Exact target job inspected

Run 35560410070, job 106212097997: every step completed SUCCESS.
The plugin-returned complete job log identifies exactly 6416eebd and Lean
4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
The declared 88 M06 targets built successfully in 3,421 Lake jobs. The
supplemental build completed in 3,425 jobs, including its linter executable.

All 50 supplemental modules passed the normal and slow lint sets. The complete
transitive audit passed 568 declaration records. Its final markers are
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=568 and
EXACT_LEAF_VALIDATION_PASS modules=50. The job completed at 2026-09-21T04:32:19Z.
The inspected Lean compilation/audit/lint output has no error or warning record.
The Actions runner separately reports Node action-runtime deprecation warnings;
these are not described as Lean warnings or concealed as a warning-free workflow.

The five new modules own 44 complete records: 12 in PBSInformationBudget,
9 in CFRDInformationChild, 5 in CFRDInformationContinuation, 5 in
CFRDInformationDriver and 13 in Examples/CFRDInformationChild. Every new
record uses exactly propext, Classical.choice and Quot.sound. The full audit
rejects any dependency outside that existing allowlist. The labelled normalized
44-record excerpt is M06-information-contract-axioms.txt; it is not the raw log.

The source adds 18 public general theorems, one private helper theorem and
11 example theorems. Those counts differ from the declaration-record count,
which also includes definitions, generated equations and private declarations.
None of these counts is a complete-framework completion percentage.

## Same-source validation not conflated with the supplemental audit

At the initial evidence recording:

| Source 6416eebd | Run / job | Inspected result |
|---|---|---|
| Target compile, supplemental lint and axioms | 35560410070 / 106212097997 | Completed success. |
| Standalone source inventory | 35560410181 / 106212098735 | Completed success. |
| Full repository build/lint/architecture | 35560410121 / 106212150505 | Running; build, reuse checks and architecture phases 1 and 2 passed. |
| Full ReBeL compiler/lint/transitive audit | 35560410133 / 106212156566 | Running; width, static architecture, ledger/inventory/adversarial fixtures and rational execution passed. |
| Exact-source snapshot | 35560410133 / 106212156827 | Completed success. |

Re-read the final results before integration. Intermediate successful steps
are not final workflow success. The evidence head has its own distinct checks.

## Artifact provenance and integrity limits

Final source archive: artifact 10621857804,
rebel-source-6416eebd9a67645fe94100db744cd4d049d17684, 2,129,264 bytes.
GitHub-reported ZIP SHA256:
5ad22b97f892a398900f2e313492834c4f60ab1df317dd61d3763dc57cd312fd.

Final target log archive: artifact 10621585511,
m06-targeted-6416eebd9a67645fe94100db744cd4d049d17684, 19,311 bytes.
The inspected Actions upload reports ZIP SHA256:
f80f5803215841086198d0397c5b4507e6a2255169941bdd274a60064fdffdc4.

These final archive digests are server-reported, not independently recomputed
locally. The complete target job log was inspected through the GitHub plugin.
No independent SHA256 of its decoded raw text is asserted. Source properties
were checked through immutable plugin file reads, commits and their comparison.

The starting 30f7dfd3 archive, artifact 10620459195, was obtained through the
plugin and its SHA256 was checked independently before the offline runtime
became unavailable:
1b85e369b451932027780df8ac279fb49ce849bf643bff6012cc8e8f03ae6074.
No final-source local compile, Python suite or independent archive hash is
claimed. The compiler, fixtures and rational execution results here are from
the named GitHub Actions jobs, not an unperformed offline test.

## Failures, repairs and unchanged gates

The inherited width repair 6ee6ae40 passed target 35558360214/job 106206318768.
The first registered budget source 90945539 failed target 35559328728/job
106209075746 at one payoff inequality: add_le_add_left arranged the operands
oppositely to the expected expression. a68aea2f uses add_le_add (le_refl _).
No theorem premise or conclusion was weakened. That intermediate source's
target was cancelled by the subsequent push, not recorded as successful.

The parent-contract source c669ef76 passed target and supplemental checks in
run 35560058324/job 106211163908. All five modules at the final controls source
then passed the exact job above, with no further compiler or lint repair.

The comparison with 30f7dfd3 changes only the five new modules, the one-line
inherited formatting repair, five appended entries in each of the umbrella,
target list and supplemental auditor, and documentation. It does not remove
an inherited proof, import, target, test, counterexample, dependency pin,
coverage row or validation gate. The original content-hashed coverage ledger
and full audit logic remain unchanged. The new modules are additive checks.

## Acceptance boundary

This validated dependency slice constructs the posterior-budgeted information-
set child backend and its all-query counterfactual/parent carried contracts.
The independent recursive re-solving correspondence and original test-time
argument remain open in the project ledger. Read the construction and semantic
review alongside this evidence; compiler success is not source-equivalence
of two different algorithms and does not close the original M06 parent rows.
