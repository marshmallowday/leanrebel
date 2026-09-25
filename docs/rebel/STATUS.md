# ReBeL status — M06 in progress; M05 accepted

## Resume the scalar-tail architecture repair

Work branch: rebel/m06-scalar-tail-repair-20260925.
Parent source: 0382af933e2520c3eb152fe98ae9b45f73c4601d.
Read M06-scalar-architecture-repair.md, M06-scalar-tail-validation.md,
M06-scalar-stability-validation.md and M06-scalar-stability-coverage.json.

The parent target run36112787339/job107999829165 compiled the complete
136-target list successfully; its supplemental lint/axiom step was still
in progress at repair creation. Independent ReBeL run36112787359 failed
at the static architecture gate: two `change` tactics in the example violated
the unchanged zero-transport budget for Analysis. This commit removes those
tactics only; the explicit proof terms, theorem statements and all gates stay.
The repaired source still requires its own exact-SHA compiler and audit passes.
All predecessor refs and failures are retained. Main is unchanged.

The scalar slice derives abs(V_T-V_S)<=tolerance for every pair of actual
reach-weighted CFR outputs beyond the computed half-tolerance cutoff, at the
SAME joint PBS. Its finite-budget and noisy-depth comparisons, exact-Nash
counterexample to small directed coupling cost, and HiddenTypes consumers
remain. All83 Python tests pass, including108 exact cutoff arithmetic checks
and6561 scalar matrix/profile checks. Numerical tests do not certify Lean.

Predecessor4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5 has independent ReBeL
run36103763078/job107971751432 SUCCESS, re-read through the GitHub plugin.
Its earlier target/full-CI successes remain recorded. This is not evidence
for acceptance of the new source. STATUS-before-scalar-stability.md preserves
the earlier checkpoint text; no old source snapshot is reapplied.

## Remaining M06 work

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
The scalar output result is not a conditional value-vector/native-iteration
rate. Native first-exit, later independent carried-PBS re-solving, actual
private seed/history transport and CarriedResolveStepBounds remain. Preserve
off-path cases, model-versus-actual beliefs, finite-T errors at zero oracle
error, and printed/corrected Theorem3. M06 is NOT complete.
