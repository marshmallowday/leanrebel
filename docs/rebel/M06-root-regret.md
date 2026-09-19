# M06 constructed trunk/root-regret checkpoint

Continue on `rebel/m06-recovery`, not the stale `rebel/m06` branch. No main
integration or milestone completion is claimed at this checkpoint.

## Compiler-verified stages

- `719270f018f3fa454af4638d63ec3d932334b135`: terminal-exact conditional
  information-value backups; targeted run 35462531449 succeeded.
- `949f2dca2ef938e9702702ee47e559a9c5ff40f8`: actual stopped action scores,
  their canonical regret transfer, and the coupled value-response driver;
  targeted run 35463210260, job 105950659158 succeeded.
- `a7e65c1d0fea968267fc7f37e3705ab2d9365370`: the exact prefix/tail deviation
  decomposition; targeted run 35463407325, job 105951193764 succeeded.
- `1b1241e507e88aa40197fec2e7e48d73743b1918`: explicit finite-time regret
  of the actual searched trunk; targeted run 35463618885, job 105951760247
  succeeded. The proof supplies the learner's numerical bound from payoff
  size and oracle accuracy; it does not equate raw probe scores with canonical
  action utilities. Their common offset cancels before regret is compared.

These are exact-SHA targeted compiler results. Full lint, architecture,
coverage/inventory, examples and transitive-axiom acceptance must still be
confirmed for the final source; the last known all-gates baseline is 7eec0533.

## New local-continuation and full-game bridge

This checkpoint additionally contains `CFRDLeafContract`, `CFRDRootRegret` and
`CFRDNash`, pending their own compiler result at commit creation.

The value oracle returns only a legal continuation and information values.
Its numerical error is distinct from the conditional continuation optimality
loss. The latter bounds complete future behavioral deviations ONLY at live
cut information states of the unilateral dominating joint law. This explicit
counterfactual completion matters when factual own reach is zero. No final
root-regret/Nash certificate, hypothetical solver sequence, or off-trunk local
CFR learner is assumed. The actual root bound is obtained by combining the
proved trunk recurrence with a normalized conditional-density argument.

For a site with structural uniform own reach rho and action count A, the
searched cumulative allowance is

```
4 * sqrt(A) * ((U + delta) / rho) * sqrt(T) + 2 * T * delta / rho.
```

Only searched sites are summed. The mean root allowance is that sum divided
by T, plus the explicit continuation loss. Neither T=0 sampling nor exact Nash
at finite T is silently inferred. The exact reference value oracle is tied to
the continuation of the actual same-iteration driver. At zero remaining fuel,
continuation optimality is proved rather than required.

## Remaining milestone work

Finish the same-iteration posterior/counterfactual completion interface,
private random-iteration/carried-model execution and unknown-opponent safety,
explicit corrected Theorem 3 constants, and adversarial seed/averaging and
zero-error finite-T controls. Confirm all compiler results before promoting
coverage. Keep the printed R5 formula separate from the corrected finite-T
bound and do not substitute the M07 learning-convergence premise.
