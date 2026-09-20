# M06 finite-plan PBS reference solver

This is an implementation checkpoint, not milestone acceptance. All current
proofs and controls require their own exact-source build, normal/slow lint,
architecture gates and transitive axiom output. The allowed set remains only
propext, Classical.choice and Quot.sound.

## Construction and variant identity

The existing finite plan carrier is used without changing canonical protocol,
execution, information, probability, utility or Nash semantics. Every regret
update reads one shared previous-round profile. The correlated time-average
law is only a proof device: the returned profile plays independent marginal
averages. Its expected payoff matrix includes the original chance transitions.

For payoff magnitude B and plan counts a0,a1, the derived total error coefficient
is C = 4*B*(sqrt(a0)+sqrt(a1)). At N>0 the bound is C*sqrt(N)/N. For requested
epsilon>0, N = floor((C/epsilon)^2)+1 is a positive finite computed horizon and
the proof derives error <= epsilon. It does not choose a preexisting Nash witness.

For each actual finite-support joint posterior, m is its smallest positive atom.
Positivity and the inequality m <= p for every supported observed type mass p
are proved. Taking epsilon = m*loss for loss>0 supplies the earlier mass budget
without assuming a uniform floor across learned PBSs. One common horizon is
used for the full joint solve, not inconsistent independently solved type policies.

The resulting mixed finite plans are realized at the actual finiteBeliefForm
root. All behavioral deviations are included by the already proved realization
bridge. The conditional theorem excludes unsupported types, which require the
separate existing zero-own-reach completion when inserted into the public solver.

This is a noncomputable real-arithmetic complete-plan regret-matching reference,
NOT information-set CFR, a rational executable, or a floating-point refinement.
Plan enumeration and posterior-dependent horizons can be prohibitively large.
It is kept distinct from the paper algorithm and its fixed-T claims.

## Controls and remaining integration

Controls check the first computed regret table, a genuine changed next action,
a nonconstant generated trace, finite budget approximate Nash, a live canonical
HiddenTypes PBS and absence of any uniform positive floor for all finite laws.
These must be inspected after compilation; source presence is not validation.

This advances SEARCH-CFRD and SEARCH-ERROR. No parent source row is promoted.
Install the finite solves in the actual public-child table and prove its joint
splice/query compatibility and off-path completion. Fresh recursive carried
re-solving and its loss transfer remain separate. Preserve child and outer
iteration parameters, prediction error, and printed/corrected Theorem 3.
