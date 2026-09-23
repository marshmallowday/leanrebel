# ReBeL status — M06 in progress; M05 accepted

## Active carried-solver implementation

Resume from actual remote HEAD of `rebel/m06-carried-resolve-20260923`, based
on `e630e689df13eddedafbe3c88c2bf12561b8d1a6`. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. No history rewrite or main merge.
The predecessor's source inventory passed; its full ReBeL audit was still
running at the restart read. Do not infer a full integration pass from that.

## New implementation checkpoint — not yet compiler accepted

`CFRDInformationResolve` constructs actual fresh information-set child draws
from the stored joint PBS and its posterior-dependent conditional budget.
The canonical carried referee retains each new private profile and propagates
the stored belief, rather than resetting to the initial game's model law.
A finite stage schedule uses the full remaining horizon for each child solve.

When the model belief is `none`, the resolver retains the incumbent complete
policy. A candidate full-state one-step identity records this branch without
assuming actual/model posterior equality or caller-supplied support domination.
Next: compile this exact source, prove the whole-schedule missing-PBS identity,
add live/zero-fuel/private-memory controls and explicit transitive axiom/lint
consumers, then inspect the exact-source CI before acceptance.

## Preserved sampled-value parent

The `b3d63c722d94a5aaee60403025a5a71d4b650a4b` parent source passed M06 run
`35820010308`, job `107049652032`. It connects completed sampled expectations
to the actual noisy parent and retains prediction error, finite outer T and
positive child loss. Details remain in `M06-sampled-values.md` and
`M06-sampled-values-validation.md`; do not redo that completed slice.

## Still open

Fresh solving on supported carried PBSs still needs its derived recursive
opponent-value envelope. The generic `CarriedResolveStepBounds` premise and
one-query sampling identities are not that derivation. Missing-PBS fallback
alone is not recursive safety on supported branches. Preserve the original
versus corrected Theorem 3 distinction and all positive loss terms.

`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending
in unchanged hashed source coverage. No completed-M06, original-algorithm
refinement or numerical-execution claim is made by this checkpoint.
