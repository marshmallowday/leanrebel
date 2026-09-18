# M05 implementation checkpoints

M05 remains in progress. Read `M05-checkpoint.md` for the preserved source,
complete documentation review and remaining acceptance obligations.

## Finite type values — first compiler pass

`c1ed346d55e715581299c301dee91fa4867b8e37` added coordinatewise attaining
best responses, a simultaneous legal type-local plan, affine opponent branches,
finite minimax attainment and the characterization of optimal opponents.
These results concern the finite type-local normal form; they are not yet a
complete bridge from arbitrary canonical PBS continuation games.

Full CI `35392143520`, job `105752690158`, failed in `TypeValue.lean`:
the dependent finite-plan instance needed decidable type equality, and several
elementary lemmas included unnecessary finite/nonempty section assumptions.
The subsequent checkpoint makes these assumptions local instead of suppressing
lint. ReBeL run `35392143555` passed static architecture, line width, ledger,
inventory, fixtures and the independent rational solver checks before its
compiler/lint stage. Its final conclusion must be inspected separately.

## Geometry and PBS-relative private seeds — awaiting exact-source validation

`ValueGeometry.lean` adds cone/simplex concavity, centered simplex support,
an explicitly corrected concave extension, and convex averaging of supporting
vectors. It does not claim that Appendix F's radially normalized extension is
concave, or that the main existential extension statement is refuted.

`ContinuationConsistency.lean` and `ContinuationRealization.lean` address a
necessary semantic distinction: a fresh private strategy seed drawn at a PBS
must not be conditioned on actions before that PBS. The construction filters
the canonical own-action record by the public cut, proves compatibility under
legal steps, and realizes the full joint continuation history law. It keeps
correlations between the PBS's roots rather than multiplying their marginals.
These new files are compiler candidates until exact-SHA CI succeeds.

Still required: finite PBS equilibrium existence and its unilateral-deviation
bridge; legal typewise gluing and fixed compatible conditional-history kernels;
connection between the type-local matrix value and canonical PBS payoff;
real game-level normalization counterexamples and positive/boundary/nonsmooth
controls; all final compilation/lint/axiom/architecture gates; and justified
coverage/status updates. No M05 ledger item is promoted by this checkpoint.
