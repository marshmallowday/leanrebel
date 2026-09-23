# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-sampled-values-20260923`.
This documentation checkpoint directly follows the compiler/lint/axiom-tested
source commit `b3d63c722d94a5aaee60403025a5a71d4b650a4b`. It changes only this
status file and `M06-sampled-values-validation.md`; Lean sources, targets,
audit scripts, dependencies and source-coverage rows are identical to that SHA.
Inspect the new HEAD's own CI status; this note does not invent a pass for it.
Main is unchanged at accepted M05 `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

## Confirmed target-source validation

For `b3d63c722d94a5aaee60403025a5a71d4b650a4b`:

- M06 targeted proof feedback run `35820010308`, job `107049652032`: SUCCESS,
  completed 2026-09-23 04:57:59 UTC. Both the declared-target build and the
  supplemental constructed-child lint/transitive-axiom audit steps succeeded.
- Source inventory run `35820010299`: SUCCESS.
- ReBeL run `35820010297`, job `107049908587`: widths, static architecture,
  ledger/inventory, adversarial controls and rational runtime succeeded.
  The repository-wide compiler/lint/axiom step was still running at last check.
- Full CI run `35820010272`, job `107049651853`: still running at last check.
  A later documentation push may supersede these in-progress runs. Check the
  current HEAD instead of assuming full integration acceptance.

Detailed immutable source/run identifiers and the diagnostic artifact digest
are in `docs/rebel/M06-sampled-values-validation.md`. Supplemental coverage and
semantic boundaries are in `docs/rebel/M06-sampled-values.md`.

## Completed sampled-parent slice

`CFRDInformationSampledDriver` connects completed child sampling expectations
at supported live queries to the actual noisy parent response. Oracle equality
holds at every round and trunk, hence the whole coupled `cfrDState` sequence
agrees with the constructed information-set parent under the SAME perturbation.

The carried security theorem retains prediction error, the finite outer-T
term and twice the positive child loss against any fixed unknown opponent.
It retains the selected continuation; it does not freshly re-solve all later PBSs.

Five compiled controls retain child loss `1/4` and numerical bias `1/8`:
reference-supported/factually absent prediction, actual coupled state, zero
remaining fuel, nonzero prediction accuracy and complete Nash deviations.
Unsupported reference entries keep their existing total convention rather
than acquiring a fabricated sampled posterior.

## Earlier checkpoints — do not redo their completed repairs

`013382138804d944ecd19c1b911d09bd5f02dfc9` on the preserved
`rebel/m06-sampled-parent-20260923` fixes the unchanged off-path live control.
Its targeted run `35817553525` succeeded. Initial `5d7386f` had failed static
transport measurement in run `35814842881`, job `107034060328`.

`ce8c0f044f315f04fa6d9da83279f11df65b7785` introduced the sampled-value parent.
Its target run `35819139077`, job `107047034616`, found two unnecessary
`DecidableEq` section-variable errors. `b3d63c7` scopes the instance correctly
without disabling lint, adds the carried bound and passes the targeted suite.

## Remaining original M06 work

First inspect exact-HEAD CI and finish full integration/audit review. Then
derive the replacement loss for freshly and independently solved carried PBSs
from the actual information-set solver and connect the recursive execution.
The generic `CarriedResolveStepBounds` premise is not already such a derivation.

Handle actual histories outside model support under unknown opponents without
assuming posterior equality, caller-supplied support domination, individual-
iterate optimality or the desired safety conclusion. Coherent re-draws of one
fixed parent family are not fresh child solving. Preserve positive errors,
finite outer T and the printed/corrected Theorem 3 distinction.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending.
No complete-M06, single-draw accuracy or executable numeric-refinement claim.
