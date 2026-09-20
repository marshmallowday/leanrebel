# M06 coherent private realization: semantics and coverage journal

## Constructed execution, not an assumed comparison

`cfrDPolicyDraw` independently predraws the finite legal action table of each
player from the actual computed behavioral profile. Finite sites, legal
fallbacks and canonical finite-plan realization are reused. The full sampled
profile is private: the actual unknown opponent is never drawn from the model.
The focal player's marginal suffices for the unilateral execution identity.

`cfrDPolicyDraw_run` proves equality of entire history distributions at every
legal root against every fixed unknown behavioral opponent, using perfect
recall. It does not require positive model reach or an existing model PBS.
`cfrDCoherentResolver_tail` preserves terminal/zero-fuel no-query behavior;
`cfrDCoherentResolver_resolve_eq` connects the actual carried resolver.
The opponent reference envelope is derived from the incumbent child contract,
not supplied as an arbitrary fixed-opponent no-loss certificate.

`cfrDFiniteCoherentResolver` instantiates the actual noisy CFR-D recurrence and
its constructed posterior-budgeted finite children, including zero-own-reach
completion. Both its envelope and security use that same computed family.
The general draw lemma permits a leaf contract, but the finite instance derives
it from the actual finite solver; its caller supplies no child Nash, positive
mass floor, probability budget, or local continuation-quality inequality.

## Repeated sampling with real private state

`cfrDCoherentStage` remembers the original private parent iteration, samples
fresh plans from that iteration's same behavioral family, and uses the existing
`carriedMemoryStep` and `executeCarriedResolves`. All previous private draws
and Bayesian MODEL updates stay in the canonical state; no alternative runner
or parallel notion of belief is introduced. The resolver does not assume the
stored model belief equals the unknown opponent's actual conditional law.

A finite schedule covers all remaining fuel; zero entries and terminal states
bypass the resolver. With final unscheduled fuel zero, induction proves the
entire execution equals the parent's behavioral continuation with the schedule's
sum. Any desired final block can be included as the last scheduled stage.
The result holds from arbitrary carried memory, history and model belief.
This is an aggregate distributional identity, not a claim that each drawn pure
policy has zero regret, and not a per-state no-loss assertion relative to an
arbitrary previously drawn pure policy.

The finite-solver specialization retains numerical error, positive child loss
and outer finite iteration error, in the bound
`A*predictionError + C/sqrt(T) + 2*childLoss`.
No switching-rate, stage-count or extra replacement penalty is introduced.
The stage schedule changes neither the sampled parent index nor its fixed
underlying behavioral family. Constants still depend on the original game
and total horizon; there is no claim of horizon-independent complexity.

## Controls and source correspondence

Eight new example theorems test an actually randomized source unequal to every
supported pure-profile draw, all-law equality at an off-model live history,
zero fuel, the actual finite-child noisy trace's law/envelope/security, and two
live strategic rounds separated by a zero-fuel stage. The multi-stage theorem
also applies to arbitrary existing private memory and absent model beliefs.
The inherited counterexamples for unsafe independent equilibrium replacement,
public/shared seeds, zero-joint versus zero-own reach and rare types remain.

This advances the execution side of SEARCH-CFRD and SEARCH-ERROR. It does NOT
close the original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR or SAFE-THEOREM3
parent rows. Their original statements, status and source identities are not
modified. The implementation is a realization/refinement of the existing
adaptive complete-plan real-arithmetic child reference, not information-set
CFR and not a rational/floating-point executable refinement.

The remaining original construction must associate actual recursive child
CFR iteration outputs and value tables with the parent continuation at each
new PBS. Independent selection of a different equilibrium is still invalid.
Predrawing the fixed behavioral result is not asserted identical to drawing a
uniform child-CFR iteration; that correspondence requires its own proof.
The inherited delayed-child-sampling APIs remain the relevant connection for
such a source-consistent family. Preserve the printed/corrected Theorem 3
statements and the numerical, child, outer and optional replacement boundaries.
