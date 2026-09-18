# M04 canonical Nash source checkpoint

The actual ReBeL run 35311223422 / job 105493499979 on
840cb3a67a8fc6c1d642b536820d32701db7572f compiled OutcomeReach and
RootRegretBounds. It failed only while matching an implicit dependent observable
in IndependentRealization. This checkpoint supplies that observable explicitly;
no theorem statement or validation condition is relaxed.

AverageNash derives canonical IsNash with euPreferenceWithin from uniform
unilateral regret bounds, using the proved two-player deviation preservation.
Its intermediate regret premise is explicit. CFRNash then discharges that
premise with the actual constructed CFR trace and finite-game payoff bound.
The output uses rounds 0 through T-1 and each player's own reach, not a shared
random iteration or an arithmetic coordinate average. Every complete behavioral
deviation remains quantified. No new equilibrium definition is introduced.

The new Nash sources are not yet accepted compiler evidence. They remain in
the public analytic root and recursive lint/axiom consumers. The executable
rational reference solver, its real refinement, concrete full-game instances,
independent best-response checks, boundary/negative tests and final same-source
validation remain required before M04 acceptance and coverage promotion.
