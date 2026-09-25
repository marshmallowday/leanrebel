# M06 native conditional-gap validation checkpoint

## Exact source and continuation

Proof source: `b11dbaffbc58c53ad048929ccb2a4d418b522d19`, retained on
`rebel/m06-native-gap-repair-20260925`. The documentation-only continuation
branch is `rebel/m06-native-gap-checkpoint-20260925`. This record does not
replace exact proof-source attribution with its own documentation commit.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; no integration or
M06 acceptance is claimed. The independently running proof-source global
ReBeL workflow is preserved, not cancelled by this documentation checkpoint.

Initial implementation `0bfa5ce2d1b67f5d14790e82e75e3db986b21fbd` remains
on `rebel/m06-native-conditional-gap-20260925`. Its two example-simplification
failures and static transport-gate failure are documented in
`M06-native-gap-repair.md`. The repair changed proof bodies, not statements,
assumptions, controls, dependency pins or frozen architecture expectations.

## Completed compiler and full-repository gates

| Source b11dbaff | Run | Job | Inspected result |
|---|---|---|---|
| M06 targeted proof feedback | 36129473984 | 108053158616 | success |
| Full repository CI | 36129473637 | 108053238399 | success |
| Source inventory | 36129473791 | workflow metadata | success |
| Independent global ReBeL audit | 36129473569 | 108053157861 | still in progress at checkpoint |

The targeted artifact `10860879140` was downloaded through the GitHub plugin.
Its SHA-256 is
`28c372994b05dd9cc6454fa4f7103874944e7bf3ef60c025d25dc3f92b1a885e`;
the actual `m06-targeted.log` SHA-256 is
`a94c108760e588bd17f043aea9d6c283845c4dbf471fbe43489c0a8d844a5401`.
Its embedded commit is b11dbaff. Both `PBSNativeConditionalGap` and
`Examples.PBSNativeConditionalGap` have successful compiler records, and
all declared M06 targets built. The follow-on inherited exact-leaf check
reports 100 linted modules and 1595 audited declarations.

**Those 100 modules do not include the two new modules.** The inherited
explicit audit script was left unchanged. Its successful result is regression
evidence, not new-module individual lint or transitive-axiom evidence. The
new modules remain in the global ReBeL auditor's automatically discovered
proof surface. Their individual global lint and axiom output is still awaiting
inspection; no inferred or fabricated new-module axiom list is recorded.

Full repository CI also succeeded. Artifact `10861318062`, SHA-256
`a11a41fe125d27d3ec128eb126d363a20b09bc546e90a81ada30f745f92cc216`,
was downloaded and its embedded b11dbaff source checked. The retained logs
show Phase 1/2/3 VERIFIED=1, 23 compiler-resolved reuse signatures, and the
configured `lake lint` passing through the complete-library aggregator.
Job steps also confirm build and tracked-file cleanliness success. The
per-file log hashes are in `M06-native-gap-validation.json`. Configured
full-library lint is distinguished from the pending explicit per-new-module
global lint and transitive axiom audit.

Global ReBeL run 36129473569 / job 108053157861 had passed widths, static
architecture, ledger/fixtures and rational-runtime steps when re-read, and
was still executing its combined compilation/lint/axiom step. Re-read that
exact run and inspect the new modules' actual axiom lists before accepting
this slice. A source snapshot or preliminary success is not that final gate.

## Exact source export and local static checks

Source artifact `10861680777` comes from run 36129473569's successful
snapshot job `108053157969`. Its ZIP SHA-256 is
`71766a6b72a8415e311ec0680ade99b8f087acfcd235cdbb92643efbbe30c39b`;
its source tar SHA-256 is
`7fbbff05d1e3b5ff19357fb28d124b47e414f91a46b72e3b934ba2e2b2462813`.
The embedded commit and both new Lean blob hashes were checked. Source was
obtained through the GitHub plugin, with no local git or direct GitHub access.

On that exact source export all 83 Python tests, coverage/inventory structural
checks and the 578-file public Lean line-width scan passed. The unchanged
global discovery routine finds 247 modules, including both additions; discovery
is not compilation or an axiom audit. Comparing source archives against the
parent proof 5cf1369c confirms that all inherited Lean bytes are unchanged.
The umbrella and M06 target list append exactly the two new modules. All audit
scripts, workflows, dependency pins and primary coverage remain unchanged.
There is no local Lean-compilation claim.

## Semantic review: what the new rate actually bounds

At one fixed canonical joint-belief slice, the supported-type payoff of an
actual privately sampled own-player CFR iteration averages to that of the
computed own-reach averaged policy, against arbitrary fixed opponents. The
proof uses the existing full-history sampler and proves conditional-kernel
support inclusion from the positive own-type mass and the mixture bind.

For the gap theorem, opponents are specifically the computed AVERAGE
opponents. Every sampled own policy is a legal behavioral deviation, hence
its Eq. (1) best-response gap is nonnegative. This sign proves equality of the
mean absolute native gap with the average policy's absolute gap. It is not an
unjustified exchange of absolute value and expectation. The actual CFR bound
and actual positive budget-round computation then bound the own-law mean,
without a minimum type mass. The dominated-query variant explicitly retains
its exact density and cap premises.

The outer type-query distribution and the private uniform iteration law form
a PRODUCT in these theorems. They do not model a later actual posterior of
the root type correlated with the retained iteration seed. A marginal query
density bound alone cannot be substituted for control of that seed/type joint
law. No equality of model and actual posterior, changed-opponent comparison,
independent re-solving guarantee, uniform bound on every type/iterate, or
sampling identity at absent roots is inferred. Compatible off-path kernels
are retained, not replaced by zero values.

The live HiddenTypes T=2 identity and budget-1/8 mean-absolute-gap theorem
instantiate the real formal information-set solver and its native sampler.
They are kernel-checked statements after compilation, not numerical runtime
measurements of the real-valued budgeted solve. The canonical exact-Nash
opponent-sampling control has zero centered mean but mean absolute drift 1/2;
it rules out using signed cancellation after changing opponents. That negative
family is explicitly not asserted to be solver-generated CFR iterates.
The inherited rational-runtime control is a separate executable experiment.

## Predecessor evidence now resolved

The parent proof `5cf1369cf1e886650a90a4e027347dacf589d50b` now has
completed successful independent ReBeL and full CI, resolving its earlier
pending checkpoint. The actual global artifact `10860962602` was downloaded;
its embedded source and hash were checked. Its log reports 245 compiled/linted
modules and 4786 transitive declaration checks. All 4786 actual axiom sets
and all 22 conditional/query-gap journal anchors were inspected; only
propext, Classical.choice and Quot.sound occur. The JSON record
`M06-native-gap-parent-validation.json` retains exact runs, hashes, anchors,
axiom sets and the separate inherited rational-runtime result.

This resolves predecessor evidence only. It is not a new-module global audit
or main-integration claim. Preserve the earlier review, validation and failed
checkpoints rather than rewriting their historical observations.

## Remaining M06 obligations

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
Independent changing-opponent/changing-PBS native and late conditional rates,
actual seed-correlated carried support and first-exit control, appropriate
joint query-density conditions, independent recursive test-time safety and
CarriedResolveStepBounds remain. Keep finite-T error when oracle error is zero
and preserve the printed/corrected Theorem 3 distinction. Learner convergence
must not substitute for the independent test-time safety theorem.
