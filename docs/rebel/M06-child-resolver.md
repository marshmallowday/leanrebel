# M06 constructed child resolver

Continue on `rebel/m06-recovery`. The inherited source at `75e37c12` added
CFRDDelayedSampling but failed its target compiler. The repair at `b717496c`
renames the reserved `prefix` binder, removes unused section instances,
proves the policy equality explicitly, and repairs line width. No theorem
statement, trust allowance or acceptance gate is weakened.

CFRDChildResolve connects the child-table construction to the existing
PrivateIterationState, privateCarriedPrefix and carriedResolvedTail execution.
The new public resolver only uses the retained parent index and its legal
information-local child table. True terminals and exhausted fuel do not
invoke it. The proof derives equality of complete history laws against every
fixed unknown opponent; it does not assume CFRDResolverLocal or any stronger
fixed-opponent no-loss property of arbitrary equilibrium replacements.

This is a source/compiler checkpoint, not M06 acceptance. The actual coupled
CFR-D value-oracle adapter, explicit recursively computed child contracts and
full exact-SHA validation remain required. Existing document-review records
are preserved and are not mislabeled as a new complete rereading. No coverage
obligation is promoted by this intermediate commit.
