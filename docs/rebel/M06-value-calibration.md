# M06 supported value-calibration checkpoint — 2026-09-25

Parent: c984277c2238e4dd1249ff3ace6fc5444175858a.
Work branch: rebel/m06-value-calibration-20260925.

The parent one-line lint repair passed the declared-target compilation and
constructed exact-child validation in run36093962253/job107942125914.
Other CI jobs must be inspected separately. No global acceptance is claimed.

## Added source-level route

CFRDSourceRates now additionally proves:

- cfrDFreshValueChange_le_calibration: if OLD and NEW continuation values are
  calibrated to one information-local target with errors e_old and e_new under
  their own equal reference laws, their positive signed change is at most
  e_old + e_new.
- cfrDWeightedTransportLoss_le_calibration: the actual correlated private
  iteration/history loss is at most childLoss + e_old + e_new. Calibration is
  needed only at OLD-supported live queries. Perfect recall supplies actual
  support inclusion for an arbitrary unknown opponent; no bound on that
  opponent's density, minimum query mass or whole-outcome-law distance is used.

The new declarations extend an existing M06 target, umbrella import and
supplemental lint/transitive-axiom module. Existing declarations and gates are
retained; no module, exception, dependency or linter setting changes.

## Exact boundary

This is a source-calibration theorem, NOT a proof that scalar Nash error
controls a vector of conditional values. Equal references can be derived for
the implemented same-cut fresh chain. The common-target calibration premises
must still be discharged from the intended oracle/solver; native later-PBS
re-solving and first-exit rates remain open. M06 and its four owning coverage
rows remain pending. Do not replace these premises by an assumed final root
security inequality or claim full-law convergence from value accuracy.

This commit is a proof checkpoint pending its own exact-SHA CI. Extend the
actual noisy finite-parent/two-fresh-child example next, then record completed
compiler, lint, axiom, independent and inventory results separately.
