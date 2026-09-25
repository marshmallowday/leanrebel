# ReBeL status — M06 in progress; M05 accepted

## Resume from the conditional-gap work branch

Work branch: `rebel/m06-conditional-gap-20260925`, based exactly on
`e58eff73bcff5f8a67ccb1745f49bf9e762ba398` from
`rebel/m06-conditional-value-repair-20260925`. Main and all predecessor
branches are unchanged. Re-read this branch head and its exact-SHA Actions
before continuing. M06 is NOT complete.

The predecessor's targeted run `36122926779`, job `108032492682`, finished
FAILURE. Its actual compiler log was inspected through the GitHub plugin.
The mathematical module `PBSConditionalValueStability` compiled; its example
module failed on two unused `simp` tactics at lines 52 and 54, after `rw`
had already closed the exact-Nash goals. This checkpoint removes only those
two redundant tactics. It does not disable lint, weaken any statement,
remove tests, alter dependency pins, or reduce audit coverage. This source
still requires its OWN successful build, lint and transitive axiom audit.

See `M06_CONDITIONAL_VALUE_STABILITY.md` and
`M06-conditional-value-stability-coverage.json` for the semantic slice and
its still-pending acceptance. The failed source and its evidence remain in
history; no initial-source or parent result certifies the repaired source.

## Conditional-value slice being validated

The canonical fixed-slice theorem bounds conditional self-payoff drift by
the maximum of two approximate Nash errors, weighted by own-type mass.
It requires equality of all opposing policy coordinates. Division is used
only for supported types; absent-type kernels are not made zero.

The actual information-set CFR budgeted single-output theorem derives its
Nash premise and bounds its own conditional payoff against that output's
CURRENT-opponent Eq. (1) value. The two-output version retains an explicit
same-opponent premise. The live HiddenTypes example uses budget 1/8.
The canonical zero-sum counterexample has exact root Nash profiles but
conditional value drift one when opponents change. Rare/absent-type
controls are preserved. All modules stay in the umbrella, M06 targets and
explicit exact-leaf audit; the global ReBeL audit also discovers them.

## Preserved predecessor evidence

Initial conditional source: `069bb7e91eab35772670fc6e060d90f42e58ac07`.
Scalar checkpoint: `d2cb889b5538bc9429eb47a7a7e32309d0e31bb7`.
Scalar proof source: `5a9fc55e6b944abb16ec7f2e16e80deb0db341f3`.
Its independent ReBeL run `36113477739`, proof job `108001998664`, was
recorded as successful after inspection in the predecessor checkpoint.
The detailed correction of earlier run attribution is retained in
`M06_CONDITIONAL_VALUE_STABILITY.md`. Preserve `M06-scalar-full-ci.md`,
`M06-scalar-stability-evidence.md`, `M06-scalar-stability-review.md` and
all associated source, axiom and coverage JSON evidence. Parent success is
not exact-source acceptance of the current work.

## Remaining M06 work

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Native/late-training conditional vector rates, native first-exit, later
independent carried-PBS re-solving and CarriedResolveStepBounds remain.
Preserve actual private seed/history laws, off-path cases and model-versus-
actual beliefs. Keep finite-T residuals when oracle error is zero and keep
the printed and corrected Theorem 3 readings separate. No learner
convergence premise may substitute for test-time safety.
