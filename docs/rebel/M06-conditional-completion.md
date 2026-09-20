# M06 conditional completion and supported-type Nash bridge

Restart source: `cd2e0f271dc8c55a3df66709ce5016a9c3c6a580` on
`rebel/m06-resume-20260920`. Its targeted run `35478943461`, job
`105993069826`, completed successfully. This includes the inherited compiler
repairs and conditional-root preservation. Do not replay the older failed
`e0242aa1` source or overwrite `rebel/m06-recovery`.

New source: `GameTheory/Analysis/ReBeL/CFRDConditionalCompletion.lean`.
The module is registered in the analytic umbrella and the M06 target list.
This implementation checkpoint requires its own exact-SHA compiler, lint,
architecture and transitive-axiom checks; it is not milestone acceptance.

The deviation-continuation theorem specializes selected-player preservation
to every opponent of a focal deviator. The deviator may have zero original
own reach and may use any complete legal behavioral replacement. Only the
opponents must have positive original own reach on the specified root.
The conditional-payoff theorem integrates this complete law equality over
a compatible conditional history kernel. The actual-payoff theorem requires
all players' own reaches to be positive on that kernel.

The supported-type Nash theorem now transports the existing canonical PBS
optimality result through simultaneous completion. It proves an inequality
against all behavioral deviations, not just preservation of the played mean.
No continuation-optimality conclusion is added as a structure field.

Remaining: combine this supported branch with the constructed zero-own-reach
best-response branch, justify kernel support/positivity for the actual
counterfactual queries, and connect recursively computed child continuation
bounds to the depth-limited solver and corrected Theorem 3. Arbitrary kernels,
ordinary Nash at zero-mass types, and independent equilibrium replacements
remain insufficient. M06 coverage is not promoted by this checkpoint.
