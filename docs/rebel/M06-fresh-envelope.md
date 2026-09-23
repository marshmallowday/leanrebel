# M06 fresh-continuation envelope checkpoint

## Source and current status

Source obligations: main Theorem 3 and supplemental G, printed pages 21-22;
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 in docs/rebel/coverage.json.
The original source rows remain pending. This checkpoint is not acceptance of
Theorem 3, its printed finite-T formula, or unrestricted recursive re-solving.

The predecessor is e630e689df13eddedafbe3c88c2bf12561b8d1a6. Its full CI,
ReBeL checks and source inventory succeeded. See STATUS.md for exact run/job IDs.
New-source compiler/lint/axiom acceptance is pending at checkpoint creation.

## Implemented dependency slice

Module GameTheory.Analysis.ReBeL.CFRDFreshValueDrift:

- cfrDFreshValueChange is new-minus-old continuation value, conditioned on the
  OLD unilateral reference law and the full own-information/live tag.
- cfrDFreshValueDrift is a finite maximum over supported live tags. It does not
  sum duplicated history representatives or evaluate unsupported posteriors.
- cfrDFreshValueChange_le_drift derives coverage of every supported query.
- cfrDFreshValueDrift_self and cfrDFreshValueDrift_zero_remaining retain zero
  change and stopping controls.
- cfrDFreshUniformDrift takes the finite maximum over the actual parent family.
- cfrDFreshCoherentResolver_envelope splits the resolved opponent payoff into
  the NEW child's unilateral gain and the old-to-new MODEL value change.
  The former uses local child optimality; the latter uses the computed maximum.
  Reference-prefix equality is still a strategic premise at this generic layer.

The maximum is an abstract real-valued finite specification, not a claimed
executable rational/float implementation. It contains no unknown opposing policy.
A finite-plan draw realizes the new behavioral profile even at off-model roots;
it must not be described as sampling the actual child CFR iteration.

## Next obligation

Construct the new family with cfrDInformationContinuation at a separately
chosen positive child tolerance, discharge reference-prefix equality and child
optimality by the existing finite information-set solver, and carry the resulting
loss plus computed drift into the parent security theorem. Then add concrete
live/off-model/nonzero-error controls. The remaining multi-level source theorem
still requires a justified vanishing bound on cross-solve drift, not an assumed
CarriedResolveStepBounds or a silently discarded error term.

## Coverage map (not source-row promotion)

| Original row | Contribution | Remaining |
| --- | --- | --- |
| SEARCH-FRONTIER | Existing stopped/live semantics preserved | Source acceptance review |
| SEARCH-CFRD | New-family conditional envelope bridge | Constructed fresh instantiation |
| SEARCH-ERROR | Explicit finite cross-family value drift | Source error-rate control |
| SAFE-THEOREM3 | Correct model comparator, not fixed-opponent exploitation | Recursive source guarantee |
