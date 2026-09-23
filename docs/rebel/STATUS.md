# ReBeL status — M06 in progress; M05 accepted

## Active sampled-value continuation

Resume from actual remote HEAD of `rebel/m06-sampled-values-20260923`.
The predecessor `rebel/m06-sampled-parent-20260923` remains at
`013382138804d944ecd19c1b911d09bd5f02dfc9` so its full audit is not cancelled.
Main remains accepted M05 at `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.
No main merge, history rewrite, dependency upgrade or weakened audit gate.

## Checkpoints and exact-source diagnostics

- Original `5d7386fe75541819f6f75e955d6c26216c9f39c3`: static failure in
  ReBeL run `35814842881`, job `107034060328`,
  `TRANSPORT_ANALYSIS_SOURCE: expected 0, got 1`.
- `013382138804d944ecd19c1b911d09bd5f02dfc9`: direct proof of the unchanged
  off-path live control removes the unnecessary transport tactic. Targeted
  run `35817553525` succeeded. ReBeL run `35817553518`, job `107042235790`,
  passed architecture, widths, ledger/inventory, adversarial controls and
  rational runtime; full compiler/lint/axiom step still running at last check.
- `ce8c0f044f315f04fa6d9da83279f11df65b7785`: sampled-query expectation to
  noisy-parent state connection, plus three controls and audit inclusion.
  Targeted run `35819139077`, job `107047034616`, reported only two unused
  `DecidableEq` section-variable errors (lines 78 and 123), not proof holes.
  Its diagnostic artifact is `10733130401`. New examples were downstream of
  the failed module and therefore were not yet compiled on that SHA.
- This successor scopes that instance only over the state/safety statements,
  without disabling lint. It adds the explicit carried security bound and
  positive-bias accuracy/Nash controls. Inspect this successor's OWN push
  workflows before acceptance; predecessor success is not successor evidence.

## Implemented candidate and coverage boundaries

`CFRDInformationSampledDriver` connects the same child sampling expectation
used at supported live queries to the actual noisy parent at every round and
trunk. The whole coupled `cfrDState` sequence agrees. The numerical perturbation
is identical in both constructions; no unperturbed comparison trace is used.
The carried execution theorem retains prediction error, the finite outer-T
term and twice the positive child loss against any fixed unknown opponent.

Reference-supported/factually absent queries use computed response completion.
Unsupported vector entries retain their reference convention, not an invented
sampled posterior. Controls retain child loss `1/4` and numerical bias `1/8`,
and cover off-path support, the actual coupled state, zero remaining fuel,
nonzero numerical accuracy and every complete Nash deviation.

See `docs/rebel/M06-sampled-values.md` for the declaration-level coverage map
and semantic review. Original source rows and their content hashes remain
unchanged: this narrow connection is not original-M06 completion.

## Remaining original M06 work

Validate the new exact SHA, then connect independently re-solved recursive
carried-PBS execution. The unknown opponent can produce histories outside
model support; do not assume model and actual posterior equality, supplied
support domination, individual-iterate optimality or final safety. Existing
coherent re-draws of the same parent are not fresh independent child solving.
Preserve positive prediction/child losses, finite outer T, and the
printed/corrected Theorem 3 distinction. Sampling expectations are not a
single-draw error guarantee or an executable numeric refinement.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending.
