# M06 joint completion and conditional leaf optimality

Source: `GameTheory/Analysis/ReBeL/CFRDCompletedLeaf.lean`.
This checkpoint is subject to exact-source compiler and full validation.

The selected-player continuation theorem now connects to arbitrary focal
deviations: completing opponents does not change any such conditional law
when their original own reach is nonzero on the root kernel. The focal
player's own reach may be zero. At a focal zero-own-reach root, completing
all players therefore executes the constructed focal response against the
original opponents. This is stronger than initial-history law preservation.

`TypeBeliefSlice.completed_value_eq_of_nash` splits supported and unsupported
types. Supported types inherit the existing PBSLeafOptimality theorem and
positive-root law preservation. Unsupported zero-own-reach types attain the
finite conditional maximum by actual remembered-type splicing. Completing
the opponents leaves every deviating focal continuation unchanged, giving
`completed_bestResponse_of_nash` for the completed JOINT profile.

`cfrDJointTypeCompletion` computes all players' completion policies, using
finite conditional maximization and the existing legal splice. Its theorem
`cfrDJointTypeCompletion_optimal` requires no supplied optimal completion or
value inequality. It permits different player-specific type carriers while
keeping the original joint-history kernels and information-local policies.

## Explicit premises and remaining connections

There must be a canonical Nash equilibrium at the slice's reconstructed PBS.
Each conditional kernel must have positive original own reach for opponents.
Supported own types must have nonzero original own reach; unsupported own
types must have zero original own reach throughout their kernel. These are
structural reach/support conditions, not assumed optimality conclusions.
They still have to be constructed from the actual CFR-D carried query and
its counterfactual reference law before closing SEARCH-CFRD/SEARCH-ERROR.

The constructor is noncomputable finite-game mathematics, not an executable
floating-point or neural solver. It does not yet construct recursive child
CFR-D tables or their finite-iteration quality bounds. The printed Theorem 3
and the corrected finite-T statement remain distinct, and M06 is not marked
accepted merely by this intermediate joint-completion proof.
