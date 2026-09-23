# ReBeL status — M06 in progress; M05 accepted

## Active sampled-value continuation candidate

Resume from actual remote HEAD of `rebel/m06-sampled-values-20260923`.
It descends from `013382138804d944ecd19c1b911d09bd5f02dfc9` on
`rebel/m06-sampled-parent-20260923`. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. No main merge or history rewrite.

## Preserved restart evidence

The original `5d7386fe75541819f6f75e955d6c26216c9f39c3` failed the static
architecture gate in run `35814842881`, job `107034060328`:
`TRANSPORT_ANALYSIS_SOURCE: expected 0, got 1`. Its source snapshot is artifact
`10731240831`; inner tar SHA256 is
`17d22e571d29d16e196af775eba9bd6b281ddb6d1129a0f61eb536cfb74439f1`.

Checkpoint `013382138804d944ecd19c1b911d09bd5f02dfc9` replaces the unnecessary
transport tactic by a direct proof of the unchanged off-path live control.
Its M06 targeted run `35817553525` succeeded. Dedicated ReBeL run `35817553518`,
job `107042235790`, passed static architecture, line widths, inventory,
ledger/adversarial fixtures and rational runtime; its full build/lint/axiom
step was still running when this successor was prepared. Preserve that run
on the predecessor branch rather than cancelling it with this continuation.

## New candidate: sampled values drive the same noisy parent

`CFRDInformationSampledDriver` proves live conditional values survive restoring
the trunk, defines the supported sampled-value response, and connects it to
the constructed information-set oracle at every round and queried trunk.
The equality of actual recursively updated `cfrDState` values follows, with
the SAME prediction perturbation, not an independently chosen play trace.
Unsupported vector entries retain the reference convention; no posterior
identity or sampler interpretation is claimed on an unsupported fiber.

New controls retain child loss `1/4` and prediction bias `1/8`, exercise a
reference-supported/factually absent query, the actual coupled state, and
zero remaining fuel. The new modules and the previously omitted general
completed-query module are added to the supplemental lint/axiom audit.
This candidate needs its OWN target-SHA compiler/lint/axiom evidence before
acceptance. No dependency, test, linter, architecture budget or axiom allowlist
is weakened. The root analysis umbrella and M06 targets include the slice.

## Remaining original M06 obligations

Inspect the new target-SHA runs and discharge any diagnostics. Carry the
sampled-parent construction through its explicit positive-loss security bound,
then connect independently re-solved recursive carried-PBS play against a fixed
unknown opponent. One-PBS and one-query identities are not recursive safety.
Do not identify model and actual posteriors or claim individual-iterate
optimality. Preserve finite outer T and the printed/corrected Theorem 3
 distinction. Sampling expectations are not a single-draw error guarantee.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending
in the unchanged hashed coverage. No numerical-refinement or full-framework claim.
