# M04 full regret and own-reach average development

This is a source checkpoint, not M04 acceptance. The actual prior ReBeL run
35309241814, job 105487645043 on 1db2dda29bd993dfdb1c5617f4599c0635caa2ac
compiled the explicit-fallback matcher and reached two localized CFRTrace
errors: information-site eta equality and rewriting an unfolded dependent
recurrence. This checkpoint uses explicit reflexivity and a pointwise recurrence
lemma; neither the process nor its hypotheses are weakened.

RootRegretBounds connects the constructed root identity and actual coupled
tables to every behavioral deviation. The coefficient is the fixed target's
own reach, independent of round and opponents. The norm bound comes from the
game's payoff range and finite legal menus/history fibers. The stated bound
covers zero rounds cumulatively and positive rounds as an average.

WeightedAverage reuses ReachWeights and FinDist, with an explicit fallback at
zero total mass. Its mass-times-probability identity includes zero mass.
OwnReachAverage uses perfect recall to make own reach a function of information,
then constructs a behavioral law whose full own reach equals the mean own reach
of the input policies. No policy receives a hidden-state argument. The next
bridge must prove complete outcome-law equivalence to independent private
iteration seeds, and then the canonical two-player zero-sum Nash statement.

All new sources must pass their own actual Actions compiler/lint/axiom results.
The full rational reference solver/refinement and independent exhaustive
best-response examples remain required. Coverage and M03's qualified boundaries
are unchanged. The original all-document reread is recorded separately in
M04-document-review.md. All remote writes use the GitHub plugin; no worktree,
force push, changed pins, or main integration is used.
