# M06 weighted transport — compiler feedback and derived solver consumer

## Initial source failure (not accepted evidence)

Source72faa00ec9c41c4f69d153a7c3d016b9fc4c19fe FAILED targeted run35983186234/
job107579670569. Plugin-downloaded artifact10801690368 has SHA256
915cd97546e28c68947199bd230e3b59e9af0c74d7c2974f980e2ee8c99e18f7, verified locally.
All predecessor modules compiled; the supplemental audit was skipped and is
not accepted. The complete decoded compiler log identified three issues:

1. FinDist.support_map is an equality of sets, not an Iff with a .mpr field.
   Rewrite the support with that equality and give the membership witness.
2. The live Bool branch still contained a propositional true=true conditional,
   and the goal retained an opaque signed-value-change definition. Eliminate
   the conditional and unfold that definition before the linear arithmetic.
3. The generic root-security lemma inherited unused Fintype E.History.
   Move it before the finite-history section instead of disabling the linter.

The successor repairs these without changing statements, warning policy,
heartbeat limits, existing controls or axiom whitelist. Exact-SHA Lean acceptance
of the successor is still PENDING until its compiler, lint and axiom gates finish.

## Additional dependency-closed consumers in the same registered modules

cfrDWeightedTransportLoss_le_uniform derives that the actual weighted allowance
never exceeds the prior uniform value-drift/transport allowance. Actual prefix
support is derived from perfect recall and the existing unilateral density.
The finite-law rare-query improvement is therefore supported by a general
comparison theorem, not merely an example-specific arithmetic observation.

cfrDFreshChain_weighted_security constructs the noisy sampled-value parent and
the actual finite fresh-child chain, deriving both oracle accuracy and local
child quality internally. It consumes no caller-supplied final envelope, Nash
child certificate or security bound. Noise boundedness is an explicit ordinary
numerical assumption; it is not a claim about learned-network accuracy.

freshChainControl_biased_weighted_security uses the canonical hidden-type game,
actual parent prediction bias1/8, old-child loss1/4 and fresh losses1/4 then1/8.
It retains finite outer T and arbitrary fixed unknown behavioral opponents.
The weighted charge uses the actual private iteration/history joint law.

This remains a fixed-cut theorem. Later carried-PBS independent re-solving,
useful actual weighted drift/transport rates and CarriedResolveStepBounds remain
original M06 obligations. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 stay pending. Preserve the original printed/corrected distinction.
