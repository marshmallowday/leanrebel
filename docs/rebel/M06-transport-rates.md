# M06 transport rates: restart and proof plan

## Exact restart

Branch: rebel/m06-transport-rates-20260924, based on
1c509f60f823505a36318e54735f61e00dd49aab (weighted-transport review).
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098 and is not a write target.
The predecessor proof source fd3770c4c4123cefec9cc5456f99b18f5b52c697,
its accepted targeted/full-library evidence and all earlier proofs are preserved.
The plugin comparison confirms only five documentation files differ between
that proof source and the restart commit. The plugin-downloaded source archive
10801103448 has ZIP SHA256
760abb4ae316ef668d541a30d1fe19833546893d615e425ca2b0c8d5854d8fa9 and source TAR
SHA256 fa1824c0f823e397bb734febe182ea8e457a4fd0a01ae32bc4af65bf97e7cdd5;
both were independently checked. No local Git or direct GitHub access was used.

At the initial read, independent predecessor ReBeL run35984130849,
job107582791762, was still in progress in compiler/lint/transitive-axiom checking.
Its success must be checked separately, not inferred from the target gate.

## Current proof obligation

Continue SEARCH-ERROR and SAFE-THEOREM3 (main section5.1 and Theorem3,
supplementG pp.21-22). The existing actual-prefix weighted charge is a useful
execution theorem, but an expectation is not itself a vanishing error rate.
Derive quantitative bounds from changes in finite source laws, explicitly
accounting for normalization, missing NEW queries and actual private seed/history
coupling. Investigate an OLD-query-mass weighted transport estimate by the
unnormalized atom differences, avoiding an inverse minimum-reach factor.
Connect proved estimates to the existing fresh-continuation security consumer;
keep numerical error, finite outer T and child loss visible.

All prospective Lean statements are UNVERIFIED at this checkpoint. No new proof
is claimed by this planning document. Commit implementation and adversarial
controls together with their build/lint/axiom consumers before acceptance.

## Boundaries

Do not assume a desired root safety inequality or CarriedResolveStepBounds.
Do not identify a model PBS with the actual unknown-opponent posterior, or
replace joint seed/history sampling by independent marginals. A conditional-law
stability premise must describe source probabilities, not restate the desired
security conclusion. Do not claim that arbitrary independently accurate scalar
Nash values imply small counterfactual vector drift.

Later carried-PBS independent re-solving, useful native first-exit rates and
the unrestricted original recursive-security theorem remain separate obligations.
The printed delta*C1+delta*C2/sqrt(T) and corrected finite-T form remain distinct.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
