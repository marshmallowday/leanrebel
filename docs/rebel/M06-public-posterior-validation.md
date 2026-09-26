# M06 public-posterior validation checkpoint

## Source identity and repair history

Work continues on `rebel/m06-conditioned-query-20260925`. The resume point was
`6bc06761937a81eb4468fb3f7f5ec89e019b8ca6`, selected using both pages of the
120-branch enumeration, repository-wide push workflows and a fresh branch-ref
read. Main remains the accepted M05 source, not the active M06 source.

The resume point's actual target run 36262881059 / job 108461920726 failed at
PBSConditionedNativeGap.lean:270. Ordinary rewriting of the projected history
law produced an ill-typed motive because the conditioning witness depends on
that law. No theorem statement or support premise needed to change.

Checkpoint `a76f1f32403f3cc1834d8f39d11b9802626ee592` switched to dependent
simplification after unfolding the named public event and posterior. Target
36264124596 / job 108465401160 then failed at line 273: the preimage of a
predicate set and its explicit predicate-set form still did not match in the
simplified equality. This failed run is not compiler or axiom-audit evidence.
Its actual artifact 10913219197 was downloaded through the GitHub plugin and
read. ZIP SHA256:
f98ab92e6cd69156521b08c9072ff9ce17acf9f83103c0c221f70784183672b0.
Log SHA256:
ca528ff2e10afb5457e7e0cfa6bdeaa9566919bdafc142a8e770d7e00ae67f03.
The log identifies the exact source and Lean 4.33.1.

Checkpoint `5df5e6a049c9550bcc944c3ca8599a3b215605e7` explicitly normalizes
that preimage with `Set.preimage_ofPred_eq` before transporting the law and
its dependent witness. The existing lemma was checked in the pinned Mathlib
commit `0df444a360eaa60ab8c11dca51a86af692955474`,
Mathlib/Data/Set/Image.lean. The older alias `preimage_setOf_eq` is deprecated
in that pin and was not introduced. Both repairs change only the proof and
comments of pbsInformationCFR_public_posterior_history. Statements, public
observations, support witnesses, conditional errors and hostile controls are
unchanged. No workflow, audit configuration, expected count, import, target
list or dependency pin was modified.

## Exact source and offline checks

Source artifact 10913740395 was downloaded through the GitHub plugin. Its
embedded source-commit.txt equals the 5df5e6a source above. ZIP SHA256:
4e0f58c8ce01a054755bf20e87894b42518c14b1897b9ed69a84465de94a865a.
The source TAR SHA256 was independently recomputed and agrees with the
artifact's recorded value:
7879349062ecc473ee5d5d9cf6bc4cb598ad9927233588a8dca4203c5f8d7596.
The a76f1f3 and 5df5e6a archive file sets are equal; their only changed file is
GameTheory/Analysis/ReBeL/PBSConditionedNativeGap.lean.

Exact three-module blobs:
- FinDistSelection.lean: 97ddb4e2458d44f34be85c0f39b74f55bd148654.
- PBSConditionedNativeGap.lean: 289a19a9482d1705f74aa6aa8e5b62742c477da0.
- Examples/PBSConditionedNativeGap.lean: d268c31e0d4f5a7b2d7bc0a70b701f693bc6bdca.

On that exact offline snapshot, check_coverage.py and check_inventory.py
passed with all 3,054 items and the same status counts. All 97 Python tests
passed with warnings treated as errors. The test log SHA256 is
34ad30e7fe83478047ae2aaf23a5630a1021f415312ef8044d55018d25d4f35d.
The unchanged full-library width rule found zero lines over 100 UTF-16 units.
These are structural/rational checks, not local Lean or PowerShell execution.
No local Git operation or direct local GitHub HTTP access was used.

## Exact-source compiler, lint and axiom evidence

The following results all name the exact Lean source
`5df5e6a049c9550bcc944c3ca8599a3b215605e7`, not an earlier proof candidate
or this later documentation checkpoint. The unchanged M06 target build
completed successfully at 2026-09-26T19:07:41Z; its full supplemental validation
completed successfully before publishing its artifact at 19:16:47Z.

M06 targeted run 36264603809 / job 108466761911 passed compilation and the
unchanged supplemental audit: EXACT_LEAF_VALIDATION_PASS modules=107 and
EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1684. All 107 lint-pass markers and
all 1,684 unique declaration axiom records were checked in the actual log,
including wrapped records. Only propext, Classical.choice and Quot.sound occur.
The affected modules have 14, 18 and 26 audited declarations respectively;
each of the candidate coverage manifest's 14 named declarations is present.
The repaired public-posterior theorem uses exactly those three axioms.
The hidden-selection negative control uses only propext and Quot.sound.

Target artifact: 10913471903. ZIP SHA256:
a701c345ba53a42da94a59149d8f7f91c7cbb6fecabf8f6580a9c70a70a4aef9.
Log SHA256:
f308d2d44e41dc7dfcde9d594c851c07a9ebbd296ba67aba0b7c1602ce6ffeb4.
The log identifies Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, and the exact source SHA.

Normal AND slow lint is not inferred just from the repository script's prose.
The unchanged command invokes batteries/runLinter with --no-build --trace.
In pinned Batteries 4488d40d070b9700d4d5a6aa342f0d40c31b2a2d,
scripts/runLinter.lean explicitly calls getChecks (slow := true). That exact
upstream implementation was read through the GitHub plugin. No lint exclusion,
update flag, or dependency change was introduced.

Independent full CI run 36264603829 / job 108466874178 succeeded on Ubuntu.
No separate Windows run is claimed. Its actual
artifact identifies the same source and confirms the full build, public-library
lint, compiler-resolved reuse inventory, Phase 1/2/3 architecture and
reachability audits, and tracked-file cleanliness. Each architecture log
contains VERIFIED=1; Phase 2 and Phase 3 report six and three successful
unreachability probes respectively. Source transport remains Math=1 and
Analysis=0, with zero custom axioms, zero sorry/admit and zero over-width lines.
The full-public lint log ends with successful GameTheory.LintAll lint.
Source inventory run 36264603756 also succeeded for this exact source.

Full CI artifact: 10914355751. ZIP SHA256:
37dc0f1f0cdb1a2664ea866d512798841ab6c372efde6e2cac2bb1821cc7a222.
Per-file CI log hashes are retained in M06-public-posterior-coverage.json.
The 23 compiler-resolved reuse signatures are not a proof of their semantic
applicability; the existing inventory diagnostic retains that qualification.

All-ReBeL run 36264603792 / job 108467000492 also succeeded for the same
source, including the full-module compiler/lint/axiom gate and source cleanliness.
Its actual downloaded log starts with the exact 5df5e6a SHA and ends with
REBEL_VALIDATION_PASS modules=251. All 251 lint-pass markers and all 4,861
unique axiom records were independently parsed, including wrapped records;
REBEL_AXIOM_AUDIT_PASS declarations=4861 agrees. Every dependency set is a
subset of the same three allowed axioms. All 12 ReBeL-namespaced candidate
entries are directly present; the two generic Math entries are directly
covered by the supplemental 107-module audit above. No prior-source count
was reused as new-source evidence.

All-ReBeL artifact: 10913847925. ZIP SHA256:
429b5f6e5eeac6393bf9f1b0a0d4ca3c07b7eb8153f8a59b3fd205e9f7c289e5.
Validation log SHA256:
ea7aa0cc77f015e248f48c57049bf48607bfeae0d889cc6cd57118866cff1b54.
The actual architecture log reports VERIFIED=1 and the unchanged transport
counts. The actual rational-runtime JSON identifies the exact source and pass
status: 85 legal histories, rounds 0/1/2, 40 compared local probabilities per
round and exhaustive checking of 1,024 pure policies per player. Its reported
NashConv values are 2, 2 and 1: this is an execution cross-check with a remaining
finite-T residual, NOT a full semantic-refinement or equilibrium claim. All
four artifact-file hashes are retained in the candidate coverage JSON.

The ledger/inventory/adversarial and rational-runtime steps succeeded in the
same run. The source-validation workflows had all completed before committing
this documentation checkpoint; no in-progress validation was cancelled to
publish the evidence, and no CI-skipping commit directive was used.

The existing umbrella imports and target/auditor lists are unchanged.
No validation gate was replaced by a toy test,
source-text scan, or a prior-source green run. Machine validation does not
replace the semantic scope review below or an independent kernel implementation.

## Semantic review and remaining boundary

The existing positive-support theorem transports conditioning only for a
preimage event. The public specialization reads exactly the canonical public
trace, identifies the actual event probability, and identifies the entire
selected joint HISTORY posterior with PublicBelief.condition of the
computed-average execution. Hidden seed/type data are retained only for proof
bookkeeping; there is no new policy information or posterior independence
assumption. Impossible observations still have no conditioning witness.

The live HiddenTypes consumer uses two genuine CFR iterations, one actual
continuation step and arbitrary fixed legal execution opponents. The finite
noninjective-output control derives a visible event's mass 1/2 and posterior
pure zero. Hidden-selection and absent-visible-output controls remain in the
same compiled/audited example module. These examples are not substituted for
the generic public-posterior theorem.

The native gap is still evaluated at the ORIGINAL compatible full joint TYPE
kernels against the SAME computed average comparison opponent. It is not a
gap at new posterior kernels. In CFRDResolveBelief.lean, resolvedNextState
updates the stored model belief using chosen, whereas carriedResolvedStep
executes Profile.update unknown who (chosen who). The repaired fixed-profile
posterior theorem does not equate these different opponent models. The next
semantic bridge must quantify their support/event and value differences;
it must not silently identify their posteriors.

Independently re-solved carried-PBS identification, quantitative first-exit/
support/event rates, changing-opponent/PBS native and late rates, recursive
safety and CarriedResolveStepBounds remain open. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 stay pending in the original source ledger.
No event-mass floor, exposed seed, discarded finite-T residual or learner
convergence assumption was added. M06 and Theorem 3 remain incomplete; M07
is not started.
