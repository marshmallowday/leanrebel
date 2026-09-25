# ReBeL status — M06 in progress; M05 accepted

## Resume from the query-gap source

Work branch: `rebel/m06-query-gap-20260925`, based exactly on
`fa03b39e497e4d9802d978caab052ce2802ccdc1` from
`rebel/m06-conditional-gap-20260925`. Read this branch's actual head and
exact-SHA Actions first. Main and predecessor branches are unchanged.
M06 is NOT complete. See `M06-query-gap-review.md` and
`M06-conditional-value-stability-coverage.json`.

## New dependency-closed proof slice

The fixed-slice current-opponent conditional Eq. (1) gap now has an absolute
OWN-law mean bound equal to the root Nash error. For an exactly dominated
query law with density capped by C on own support, its query mean is bounded
by C times that root error, without dividing by a minimum type mass.
Actual finite-T and budgeted information-set CFR outputs derive their Nash
premises. The slice and opposing policies do NOT change in this theorem.
No native query-density cap is inferred or assumed inside a certificate.

A live HiddenTypes solve with budget 1/8 exercises the mean bound with its
actual own-type law and density one. A normalized rare-type prior/query pair
in the canonical zero-sum game has root error 1/4 but query error one, with
exact density (4,0). A new absent-query control rules out false domination.
All previous changed-opponent, rare-type and off-path controls are retained.
All additions are inside the two existing umbrella/target/audit consumers.
The NEW source awaits exact-SHA compiler, lint and transitive axiom results.

## Predecessor compiler repair and evidence

The predecessor `e58eff73bcff5f8a67ccb1745f49bf9e762ba398` failed targeted
run `36122926779`, job `108032492682`, solely on two redundant `simp`
tactics in the example's exact-Nash proof. Commit fa03b39e removes those
tactics without weakening the theorem or linter. Its targeted run
`36124896554`, job `108038627933`, PASSED the M06 compilation step;
its lint/axiom step was still running at the last check. Its independent
ReBeL run is `36124896574`. Those runs are preserved on the parent branch.
Do not replace new-source validation with these parent observations.

Plugin-exported parent source artifact `10859251534` had both ZIP/TAR
hashes and embedded commit checked. All 83 Python tests and ledger/inventory
structure passed on that exact export; this does not certify Lean proofs.
Detailed hashes, semantics, source scope and remaining work are in the review.

## Preserved earlier checkpoints

Initial conditional source: `069bb7e91eab35772670fc6e060d90f42e58ac07`.
Scalar checkpoint: `d2cb889b5538bc9429eb47a7a7e32309d0e31bb7`.
Scalar proof source: `5a9fc55e6b944abb16ec7f2e16e80deb0db341f3`.
Its independent ReBeL run `36113477739`, proof job `108001998664`, was
recorded as successful after inspection in the predecessor checkpoint.
Preserve `M06_CONDITIONAL_VALUE_STABILITY.md`, `M06-scalar-full-ci.md`,
`M06-scalar-stability-evidence.md`, `M06-scalar-stability-review.md` and
all associated source, axiom and coverage JSON evidence. Earlier attribution
corrections remain visible; parent success is never new-source acceptance.

## Remaining M06 work

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Native/late-training conditional vector rates, native query-density/first-exit
control, later independent carried-PBS re-solving and CarriedResolveStepBounds
remain. Preserve actual private seed/history laws, off-path cases and model-
versus-actual beliefs. Keep finite-T residuals when oracle error is zero and
keep the printed and corrected Theorem 3 readings separate. No learner
convergence premise may substitute for test-time safety.
