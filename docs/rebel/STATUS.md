# ReBeL status — M06 in progress; M05 accepted

## Active sampled-parent continuation candidate

Resume from actual remote HEAD of `rebel/m06-sampled-parent-20260923`.
It descends from `0b50d5b29414de55ea2be8791242f95f289f3a45` on
`rebel/m06-completed-query-sampling-20260921`. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; no main merge or history rewrite.

## Restart evidence and repair checkpoints

The original predecessor's full CI `35582570746`, job `106278645955`, failed
in `CFRDInformationQuerySampling`: a singleton-selection simplification and
a partially applied conditional leaf-gain function. Commit
`e966701836d809cc1b197bce95f874d3a4e01771` repaired those scripts. Its targeted
run `35814111823`, job `107031840693`, explicitly compiled the complete query
sampling module successfully, then exposed an existing control failure:
`Examples/PBSInformationSampling.lean:231` lacked a decidability instance for
the reducible nonterminal predicate. The control now reduces it to `False`
before using `decide`; the test statement and off-path witness are unchanged.

That commit's dedicated audit run `35814111846`, job `107031841089`, stopped
at the preexisting 103-character signature in the same query sampling module.
The signature is now wrapped without changing the declaration. No theorem,
assumption, test, linter, dependency pin or axiom allowlist is weakened.
This newest checkpoint still needs its own target-SHA build/lint/axiom evidence.

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
