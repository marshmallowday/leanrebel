# ReBeL status — depth-native tag-law repair submitted; M06 incomplete

Continue rebel/m06-depth-native-gap-20260927. The next source descends from
d15f68b5ca4377f06a69aa5e71c76013770ed766 and retains the original latest
37a4f2c5cc20e285bca054e4a0c544232a218235 via 345bc target acceptance. Main is
still accepted M05. No force push, deletion, dependency or gate change.

## Current repair and next check

D15f target 36288920528 / job 108535044752 failed the tag-law proof at
PBSDepthNativeGap.lean:215:92 and rejected an unused simp argument. The complete
artifact 10921403474 was inspected. The focused repair adds public
FinDist.bind_const to normalize the inner conditional root-law bind before the
outer bind_pure identity. All nine core statements and four examples are kept.
New core blob 29a19748709fdc1269728ee423656f48433b5e00 needs its own exact-source
compiler, normal/slow lint and complete transitive-axiom validation. The old
failure is retained in M06-depth-native-gap-d15f-failure.md and owning coverage.

All 141 Python fixtures and ledger/inventory checks passed on the actual
unmodified d15f snapshot. Both new module names are in the analytic umbrella,
build manifest and 113-module explicit audit; the global consumer includes 256
modules. These are static/arithmetic facts, not acceptance of the new Lean code.
Fetch this branch head's target/global/full runs independently and record exact
IDs; do not substitute d15f static success or older-source audits for new proof.

## Completed inherited validation

35d0 target and GLOBAL are now fully accepted. Its complete global artifact
10920889550 from run 36287339585 / job 108530593276 was inspected: 5,003 complete
unique allowlisted axiom records, 254 complete normal/slow lints, exact source,
frozen static architecture and rational runtime reports. Full CI 36287339593 /
job 108530515400 succeeded separately in job metadata. Owning primitive coverage
and M06-primitive-support-global-accepted.md contain exact hashes and preserve
all prior pending observations. Do not redo those completed checks. Older
4784/3dfa/b833 acceptances and all failed candidates remain intact.

## Remaining scope

The new candidate concerns actual NOISY depth-parent iterates, their fixed
average comparison opponent, and joint seed/type selection by actual execution
events. It retains numerical, positive-child-loss and finite-T terms. It does
not transport to changed conditional PBS kernels or a changed comparison opponent.
Primitive smallness for unrestricted solvers, changed-PBS native/late value rates
and constructed signed CarriedResolveStepBounds remain open. SEARCH-FRONTIER,
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending. M06 is incomplete;
no learner-convergence or background-monitoring premise is used.
