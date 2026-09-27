# ReBeL status — final observable-bound repair pending CI; M06 incomplete

Continue rebel/m06-kernel-value-repair-20260927, now a child of
1698e9ba212f4082cd7d601c13f3d0350e170bdf. Work started from the latest prior
checkpoint dac8bd902ba368357d4a53f0d0b6b90a6d3dddeb, not main. Earlier source
commits and failure/acceptance evidence remain preserved.

1698e9ba TARGET 36293359962 / job 108547527220 compiled the generic kernel-value
lemmas and actual noisy depth-parent integration. The only remaining compiler
failure was the observable-bound control: its split selected an unreduced outer
match, not the inner conditional. This repair splits the outer match directly,
then the inner conditional. The sharp-discrepancy control's earlier rewrite
error is gone. No theorem statement, premise, source definition or gate changes.

See M06-kernel-value-repair-1698e9ba-validation.md for the complete failed artifact,
exact source archive and 149 passing Python tests. The owner ledger is
M06-kernel-value-transport-coverage.json; its full predecessor is archived at
M06-kernel-value-transport-coverage-at-1698e9ba.json. All historical reviews remain.

Next inspect this new exact source's TARGET, GLOBAL and FULL CI separately.
Require all 154 declared build targets, 116 targeted / 259 global module audits,
complete transitive axiom records including the named controls, and normal/slow
lint. At 1698e9ba the unchanged global architecture, ledger and rational-runtime
gates passed, but TARGET lint/axioms were skipped after the control failed.
No complete changed-kernel slice acceptance is yet claimed.

The same opposing policies, horizon, actual correlated event-selected query,
finite-T residual and event denominator remain explicit. Compatible fresh
kernels are not yet identified as actual recursively re-solved posteriors;
their full L1 variation need not be small. Changed opponents, small primitive
kernel/leakage rates, late-value transport and constructed signed
CarriedResolveStepBounds remain open. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR
and SAFE-THEOREM3 remain pending. The accepted 51d5 depth-native evidence is
separate. M06 remains incomplete; learner convergence is not test-time safety.
