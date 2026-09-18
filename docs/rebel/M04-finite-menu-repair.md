# M04 finite-menu compiler repair

At 36bdf8d6ff4bf93e4e8cfbbff8af2987829344f7, ReBeL run 35308270211,
job 105484832270 passed static architecture and 37 regression tests. The new
explicit-fallback RegretMatching module compiled. CFRTrace then failed because
its canonical Choice carriers had no supplied Fintype. This checkpoint supplies
finite legal-menu enumeration as an operation-side typeclass parameter. This
is a structural finite-game assumption, not an assumed regret or solver result.
It does not require the ambient information-state carrier to be finite.

The payoff bounds are also aligned with the actual canonical BehavioralReach
API: joint actions carry their legality certificate in a subtype; opponent
factors multiply the chance factor in counterfactualStepProb. These repairs
change neither the canonical definitions nor the claimed probability bounds.
All new proof sources remain pending their own successful compiler/lint/axiom
results. No coverage item or M04 milestone is promoted at this checkpoint.

The constructed chronological root identity and its full two-stage examples
are retained. Next: validate coupled tables/payoff bounds, then the uniform
whole-policy regret bound, own-reach averages and independent private seeds,
canonical zero-sum Nash, rational solver/refinement and independent checks.
