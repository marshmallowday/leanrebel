# ReBeL status — M06 in progress; M05 accepted

## Active carried-solver implementation

Resume from actual remote HEAD of `rebel/m06-carried-resolve-20260923`, based
on `e630e689df13eddedafbe3c88c2bf12561b8d1a6`. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. No history rewrite or main merge.
The predecessor's source inventory passed; its full ReBeL audit was still
running at the restart read. Do not infer a full integration pass from that.

## Current source candidate and observed diagnostics

`eb59ccf754862f1e584deeee4eb3a44df39cce60` reached the new resolver in targeted
run `35822279205`, job `107056486306`. A missing direct import for the existing
stopped-run lemma and the resolver's unreduced `none` match caused the failure.
This successor repairs those proof scripts without weakening their statements.

`CFRDInformationResolveRecursion` now adds the whole-schedule missing-model
law, zero additional replacement loss, localization of remaining loss to
available-PBS states, and a derived positive-loss model-root child gain bound.
The actual noisy sampled-value parent is connected to the fresh finite
carried-PBS schedule by `cfrDInformationRecursivePlay`.

Eight proposed controls in `Examples/CFRDInformationResolve` cover a live
positive-tolerance child draw, a genuinely impossible model observation,
nonempty private memory, zero and positive execution intervals, and a
nonconstant payoff difference from wrongly resetting to the initial policy.
All three modules are in the existing Search/Analysis build closure and are
explicitly included in `audit_exact_leaf.py`. Exact-source compiler, normal/
slow lint and transitive-axiom acceptance must still be checked for this HEAD.

## Preserved sampled-value parent

The `b3d63c722d94a5aaee60403025a5a71d4b650a4b` parent source passed M06 run
`35820010308`, job `107049652032`. It connects completed sampled expectations
to the actual noisy parent and retains prediction error, finite outer T and
positive child loss. Details remain in `M06-sampled-values.md` and
`M06-sampled-values-validation.md`; do not redo that completed slice.

## Still open

Fresh solving on supported carried PBSs still needs its derived recursive
opponent-value envelope, including actual histories outside model support.
The generic `CarriedResolveStepBounds` premise and one-query sampling
identities are not that derivation. Missing-PBS fallback alone is not recursive
safety on supported branches or individual-iterate security. Preserve the
original versus corrected Theorem 3 distinction and all positive loss terms.

`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending
in unchanged hashed source coverage. `M06-carried-resolve.md` records this
supplemental slice and its precise remaining semantic boundary.
