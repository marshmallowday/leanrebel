# M06 — primitive policy stability and recursive replacement rates

Parent obligations: SEARCH-ERROR, SEARCH-CFRD and SAFE-THEOREM3; main section6
Theorem3 and supplemental G printed pp21-22. This is a restricted quantitative
bridge, not acceptance of either the printed formula or unrestricted safety.

## First checkpoint: finite laws

GameTheory.Math.Probability.FinDistMassDistance uses the canonical FinDist API.
The massDistance is sum |p(a)-q(a)| on the UNION of both finite supports. It has
normalization[0,2], not[0,1]. Neither a Fintype carrier nor a probability floor
is required. For |f|<=B the proved target is |Ep f-Eq f|<=B*massDistance(p,q).
The finite-product lemma changes one marginal and retains every other marginal,
which is the primitive needed for an arbitrary fixed unknown opponent.

Examples.MassDistance checks two overlapping laws with probabilities1/4 and3/4,
a sharp observable with bound1, distance2 for distinct point masses despite equal
Unit observations, and the ambient infinite carrier Nat. These finite-law
controls do not claim to be game-level counterexamples to source Theorem3.

## Intended downstream slice

Bound full canonical finite-horizon execution from the one-step marginal
estimate, including simultaneous moves, chance, terminal and zero-fuel cases.
Then bound the existing supported-fiber fresh model drift in terms of finite
policy distances, rather than assuming the desired conditional value change.
Use the same primitive estimate with carriedMemoryStep_selected_expect to
charge actual independently re-solved profiles along the retained-memory runner.
Any useful vanishing bound must state primitive policy-stability hypotheses;
Nash accuracy alone must not be substituted for them. The actual carried PBS
and its relation to unknown-opponent state laws are not identified by this work.

## Validation state

This first checkpoint is a compiler candidate. New core and controls are
registered in the analytic root, M06 targets and supplemental all-declaration
normal/slow-lint and transitive-axiom consumer. Existing registrations and all
checks are preserved. Exact-SHA compiler and audit output is still required.
All remote reads/writes/checkpoints use the GitHub plugin; main is untouched.
