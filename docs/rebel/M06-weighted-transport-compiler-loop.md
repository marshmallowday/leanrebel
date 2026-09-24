# M06 weighted transport — compiler loop and constructed consumer

## Initial source failure (not accepted evidence)

Source72faa00ec9c41c4f69d153a7c3d016b9fc4c19fe FAILED targeted run35983186234/
job107579670569. Plugin-downloaded artifact10801690368 has verified SHA256
915cd97546e28c68947199bd230e3b59e9af0c74d7c2974f980e2ee8c99e18f7.
All predecessor modules compiled; the supplemental audit was skipped and is
not accepted. The complete decoded compiler log identified three issues:

1. FinDist.support_map is a set equality, not an Iff with a .mpr field.
   Rewrite with that equality and supply the actual support witness.
2. The live branch retained a propositional true=true conditional and an
   unexpanded signed-value-change definition. Eliminate the conditional and
   unfold that definition before applying linear arithmetic.
3. The generic root-security theorem inherited unused Fintype E.History.
   Move it before the finite-history section instead of disabling the linter.

## Accepted repair

Sourcefd3770c4c4123cefec9cc5456f99b18f5b52c697 repaired all three issues without
weakening statements, warning policy, heartbeat limits, controls or allowed axioms.
Target35984130871/job107582693551 compiled all128 targets and passed the full
supplemental90-module/1396-declaration lint/transitive-axiom gate. Full library
CI35984130854/job107582847450 also succeeded. See the validation record for
exact completion times, verified log digest and the distinct pending independent
ReBeL run. Compilation-only checkpoint466f82c5 is superseded by this evidence.

## Additional dependency-closed consumers

cfrDWeightedTransportLoss_le_uniform derives that actual weighted error never
exceeds the prior uniform value-drift/transport allowance. Perfect recall and
unilateral density provide actual-prefix OLD support. The rare-query improvement
is therefore accompanied by a general theorem rather than isolated arithmetic.

cfrDFreshChain_weighted_security constructs the noisy sampled-value parent and
actual finite fresh-child chain, deriving oracle accuracy and local quality
internally. It consumes no final envelope, child Nash certificate or security
bound. Noise boundedness remains an explicit numerical premise, not a statement
about arbitrary learned-network accuracy.

freshChainControl_biased_weighted_security uses the canonical hidden-type game,
parent bias1/8, old-child tolerance1/4 and fresh tolerances1/4 then1/8. Finite T,
fixed arbitrary unknown opponents and the actual private seed/history coupling
are retained. The source family, not an unrelated solver trace, is evaluated.

This is still fixed-cut security. Later carried-PBS independent re-solving,
useful weighted drift/transport rates and CarriedResolveStepBounds remain.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
