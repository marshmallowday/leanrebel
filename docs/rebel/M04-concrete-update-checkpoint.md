# M04 concrete local-update correspondence checkpoint

The remote continuation remains on `rebel/m04`; main and accepted M03 evidence
are untouched. The last completely successful ReBeL audit anchor remains
`89a816b1b0c178f77bd939e4d1c4364f65093c4a` until a newer run finishes every gate.

At `b0783fa419980b92a3c51a1f1a6767ecc9a25866`, the concrete primitive chance
rows compiled. Run `35359666285`, job `105647534776` exposed only semireducible
table projection mismatches in the concrete continuation proof. Those were
repaired at `b6c2be5585d63fe4db073c2e2abf732bf44c8acd`, which also adds the full
decision-site bijection and complete counterfactual-fiber summation proofs.
Its own build/lint/axiom results must still be checked, not inferred.

This checkpoint extends the proof chain to the actual runtime local commitment
and regret update, using an injective optional-action projection to avoid
transporting dependent menu values. The projection is only a finite sum and a
pushforward of canonical FinDist; it is not a replacement game or probability
semantics. A generic matcher theorem reindexes both regret coordinates and the
explicit fallback through a legal-menu bijection.

All new code remains under validation. This is not a completion claim for M04.
The concrete generated iteration and averaged output must still be connected
to the existing canonical solver, followed by exact-SHA build, normal/slow lint,
transitive axiom audit, full-library CI, semantic review and ledger updates.
The 3052 original obligations and accepted M03 qualification boundaries remain.
