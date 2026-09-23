# M06 constructed fresh-continuation envelope

## Source and status

Source obligations: main Theorem 3 and supplemental G, printed pages 21-22;
SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 in docs/rebel/coverage.json.
The original rows remain pending. This contribution is a restricted additional
result, not acceptance of the printed formula or unrestricted recursive solving.
Base e630e689df13eddedafbe3c88c2bf12561b8d1a6 passed full CI, ReBeL and inventory.

## Implemented declarations

GameTheory.Analysis.ReBeL.CFRDFreshValueDrift defines cfrDFreshValueChange,
cfrDFreshValueDrift and cfrDFreshUniformDrift. These use the OLD unilateral
reference law conditioned on full own information and the live flag. The
finite maximum only includes supported live tags. Multiple histories with the
same tag do not multiply its weight. Unsupported posterior conventions never
become sampled queries. The change is NEW model continuation value minus OLD
model continuation value. No unknown opposing strategy occurs in the maximum.

cfrDFreshCoherentResolver_envelope splits the actual resolved opponent gain
into its unilateral gain against the NEW continuation and the conditional
old-to-new model-value change. Child local optimality bounds the first term;
the computed finite maximum bounds the second. Reference-prefix equality is
explicit at this generic layer, not assumed silently.

GameTheory.Analysis.ReBeL.CFRDFreshResolve discharges both strategic premises:

- cfrDFreshInformationProfiles recomputes cfrDInformationContinuation at each
  retained parent model with a separately chosen positive child tolerance.
  The finite information-set recurrence and zero-own-reach completion are real
  definitions, not caller-supplied equilibrium or quality certificates.
- cfrDFreshInformationResolver draws a fresh finite legal plan of that NEW
  averaged solution. Its full-history law, including off-model roots, follows
  from the existing finite-plan realization theorem. It is NOT a claim that
  the solver's individual CFR iterations are optimal or equivalent off support.
- cfrDFreshInformationResolver_envelope derives the local opponent envelope
  from the constructed child's reference-law preservation and leaf optimality.
- cfrDFreshInformation_security instantiates the actual noisy sampled-value
  parent and obtains a one-sided bound against every fixed seed-blind opponent.

Writing D for cfrDFreshInformationDrift and using the existing explicit game
constants, its total allowance is

    (C_error(who) + C_error(opponent)) * error
    + (C_finite(who) + C_finite(opponent)) / sqrt(T)
    + oldChildLoss + newChildLoss + D.

Finite T is positive. Both child losses are positive, prediction error is
nonnegative, payoffs are bounded, and the finite game is two-player zero-sum
with full AOH and total legal fallback. The reference Nash only names the
comparison game value. It is not a supplied child or output certificate.

## Controls and trust

Examples.CFRDFreshResolve contains eight theorem controls: a live legal state
with explicitly absent posterior, a genuine reference-supported/factually
absent query, a constructed envelope, zero same-policy drift, zero-fuel drift,
no-draw stopping, concrete security with old loss 1/4, new loss 1/8 and bias 1/8,
and the finite-law guard that mean zero does not imply every coordinate <= 0.
The absent-posterior record is an interface test, not an unsupported assertion
about which posterior the actual runner produces. The mean guard is not a
counterexample to the original game-level source theorem.

No new axioms, placeholders, trust escapes or expected-count changes are used.
The three modules are in the analytic root, M06 target list and supplemental
all-declaration/slow-lint audit. The offline pinned compiler passed all three
and a direct axiom audit checked 43 declarations against exactly propext,
Classical.choice and Quot.sound. Source-SHA Actions acceptance is still to be
checked after this checkpoint; see STATUS.md for diagnostic history.

## Remaining boundary, deliberately not claimed away

D is an abstract real-valued finite specification, not an executable numeric
backend or a guarantee that the drift vanishes with either child tolerance.
Independent child Nash alone is not being advertised as such a guarantee.
This resolver reconstructs a full child table from the retained parent model;
it does not consume each later carried PBS as a new independently solved root.
A multi-level source theorem must establish the appropriate conditional value
comparison along the actual carried-PBS sequence and the correct error rate.
It cannot assume CarriedResolveStepBounds, posterior equality, support
inclusion for unknown-opponent histories, or individual-iterate optimality.

## Supplemental coverage map, without source-row promotion

| Original row | Added contribution | Remaining |
| --- | --- | --- |
| SEARCH-FRONTIER | Existing stopped/live cases retained in fresh execution | Source acceptance review |
| SEARCH-CFRD | Constructed fresh finite information-set child envelope | Later carried-PBS recursion |
| SEARCH-ERROR | Explicit supported-fiber cross-family drift and positive losses | Source drift-rate theorem |
| SAFE-THEOREM3 | Derived one-cut unknown-opponent lower bound | Full recursive corrected source guarantee |
