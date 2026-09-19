# M06 full-game regret transfer checkpoint

Exact source `0403c132c31f21e50cd7bea71b70f9447307b9ad` passed the target
compiler in run `35454002335` (job `105925974439`). This validates Frontier,
ConditionalOracle and CFRDTrace, including the coupled numerical sequence and
its local finite-time estimates. It is not complete milestone acceptance.

CFRDRegret now transfers per-action score approximation into canonical
counterfactual regrets, discharges score size from canonical game payoff bounds,
and sums the constructed exhaustive schedule with the fixed deviator's own
reach coefficients. The resulting all-behavioral-deviation root bound is not
an oracle field or an assumed telescoping identity.

The remaining semantic adapters must derive these local score and tail
contracts from continuation-policy-consistent leaf vectors, including zero-own
reach fibers. Random-iteration safety, explicit source error constants and
adversarial controls must still be connected. No coverage item is promoted.
Compilation of this new regret slice is pending at commit creation.
