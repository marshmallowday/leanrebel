# ReBeL status — M06 in progress; M05 accepted

## Active sampled-parent continuation candidate

Resume from actual remote HEAD of `rebel/m06-sampled-parent-20260923`.
It descends from `0b50d5b29414de55ea2be8791242f95f289f3a45` on
`rebel/m06-completed-query-sampling-20260921`. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; no main merge or history rewrite.

## Restart evidence and first repair checkpoint

The predecessor's full CI `35582570746`, job `106278645955`, failed in
`CFRDInformationQuerySampling`: the singleton selection left an `if True`
goal at line 42, and the conditional leaf-gain function was still partially
applied at line 250. This checkpoint repairs only those proof scripts: use
ordinary simplification for singleton selection and explicitly unfold the
leaf-gain function before applying expectation subtraction. No theorem,
assumption, test, linter, dependency pin or axiom allowlist is weakened.
This checkpoint needs its own target-SHA compiler/lint/axiom evidence.

## Existing construction preserved

Factual private/live queries retain actual child iterations with their
public-posterior-dependent count. Genuine reference queries with zero factual
mass use computed response completion. The same sampled query law realizes
`cfrDInformationContinuation` against arbitrary fixed opponents and carries
its derived positive-loss leaf contract. Existing factual-zero controls,
supported-root, independent-index, zero-fuel and private-query controls remain.

## Remaining original M06 obligations

Finish exact-source validation and connect these sampled query values to the
actual noisy parent recurrence. Then establish independently re-solved recursive
carried-PBS play versus a fixed unknown opponent. One-PBS and one-query identities
are not recursive safety. Do not identify model and actual posteriors or assert
individual-iterate optimality. Preserve positive child/prediction losses, finite
outer T, and the printed/corrected Theorem 3 distinction.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending in
unchanged hashed coverage. No numerical-refinement or complete-framework claim.
