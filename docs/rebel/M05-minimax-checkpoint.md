# M05 canonical minimax checkpoint

M05 remains in progress; main is unchanged and no coverage item is promoted.
Work continues on `rebel/m05` through non-force GitHub-plugin writes.

At source `40f45ca1ad29908ecb0c60f159d8241ded20d7eb`, targeted run
`35396490581`, job `105766408193`, successfully compiled the complete
`Examples.ValueGeometry` module and preserved tracked-file cleanliness.
The actual canonical matrix-game values refute concavity and global centered
support of Appendix F's radial normalization, while the repaired extension
passes. Boundary zero-type values and the nondifferentiable hidden-coin game
with multiple optimal opponents are also Lean-checked.

Jobs `105766407758` and `105766408149` failed in independent public-clock
length lemmas: induction accidentally generalized PBS support or continuation
hypotheses. This source clears those irrelevant hypotheses only inside the
independent length proofs. No theorem statement or acceptance gate is weakened.

`PBSValue` adds canonical PBS equilibrium selection, value uniqueness for
either player, zero-sum security and the attained minimum of actual conditional
best-response branches. `PBSOptimalOpponent` characterizes the complete argmin
as exactly the opponent projection of the canonical equilibrium set. These
new connections await exact-source compiler validation.

The compact `M05` import root now collects the dependency-closed development
slice. The targeted workflow compiles that root; full CI, normal and slow lint,
architecture, inventory and transitive-axiom acceptance remain separate gates.
Remaining work includes canonical own-belief cone/simplex geometry, applicable
normalization calculus, source-semantic review, and justified coverage/STATUS
updates after all checks succeed.
