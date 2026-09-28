# Public-to-live discarded mass and actual stored-parent batch

## Branch and batch boundary

Continue rebel/m06-kernel-value-repair-20260927 at accepted
133dc247945486c48f055815b4262261f6fff5f2. It contains the unfinished M06 native
solver integration and its accepted dependencies. Default main was checked
separately at 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098; plugin identity is
marshmallowday with admin/push permission. Chat baseline is
9457c198126f3c8b7cb1045bbed2e0053788636f.

The previous repair loop is fully accepted by
M06-stored-child-133dc24-accepted.md. This batch follows the next explicit
unresolved branch of that proof: public termination need not be observable.
It combines conditioning analysis, actual native state identification, support,
future-value consumption, concrete consumers and adversarial controls in one
commit. Root-wrapper computational equivalence is a different obligation:
posterior error cannot supply equality of differently configured solver kernels.

## Implemented dependency chain

FinDistConditioningError proves the pasted conditional mean identity, a two-sided
bounded-expectation error from discarded event mass, and nested conditioning
with the explicit discarded numerator/public-reach denominator. No finite
carrier, minimum atom mass or independence premise is needed.

CFRDStoredChildDefect identifies the actual saved public posterior from the same
composed noisy round without the public-termination hypothesis. Its factual child
is the correlated public law restricted to live histories, with an exact support
iff. The expectation difference is bounded by
2 * payoffBound * stoppedPublicMass / publicReach. Publicly observable termination
recovers zero stopped mass using the earlier support theorem. Positivity of a
public observation still does not prove actual hidden-history support.

The bound is consumed by arbitrary fixed continuation kernels and paired with
the real cfrDComposedNextState belief identity. This can include one private draw
held across stage plus late fuel. Both sides use THE SAME continuation kernel:
the result does not claim stability of a policy recomputed on a different PBS.
The public-only PBS is not silently filtered before it is given to a solver.
The original algorithm and its observation interface remain unchanged.

Examples give a tight nonzero bound (quarter live, three quarters stopped,
opposite payoff extrema), constant-value cancellation, the actual hidden-type
noisy recursive parent's public state, and its full-future zero-error specialization.
The game-specific zero follows from the existing phase visibility proof.

Five Fraction controls cover 36 correlated/rare-query nested cases, the exact
signed residual identity and support restriction, tightness and the necessity of
dividing by public reach, nine retained-draw late kernels, resampling failure,
live/dead/absent/zero-fuel distinctions, and a counterexample to using this bound
when the solver's continuation kernel changes. They are independent finite
probability controls, not a simulation of the CFR learning trace.

## Precommit type and integration review

The actual source signatures of FinDist.condOn, support_condOn,
mem_support_condOn, condOn_condOn, probOf_condOn_eq_inter,
expect_condOn_eq_div_of_eq_zero_off, expect_congr, expect_sub and the event-error
consumer were read. Nested positivity uses an actual supported inner witness;
proof order is outerPossible, innerPossible, inclusion, innerConditional.
Division cancellation uses positive outer/event mass, not a fabricated bound.

Static review caught a missing DecidablePred binder for the proposition-valued
if in the pasted-mean theorem statement. It was added before commit; downstream
proofs provide classical decidability. Support proof calls name the full law
and both events explicitly, avoiding underconstrained dependent arguments.

Every publicTrace and PublicBelief index in the new solver-facing API uses
(fullInformation M).toInfoSignals. State history, saved belief, observed history
and next-state index were traced through resolvedNextState/carriedBeliefUpdate.
The initial-law premise is unchanged and does not permit resetting a later PBS.
Generic core retains independent us/ua/up/uq/uk universes. No protocol conversion
is hidden in the expectation comparisons: all laws use the same E.History.
Fintype/Choice/InfoState instances occur only after the actual composed-driver
section and match the existing accepted declarations.

Concrete consumers use model fullPrior for publicTrace, typed PBSChildSolve and
behavioral-profile aliases, the same fallback/payoff/noise/round, cut 2 and
remaining 1 as the accepted example. They retain recursive child [1] and nonzero
noise 1/8. Actual outer prefix and saved posterior use cut; continuation kernels
are not truncated or resampled by these proofs. Bound multiplication direction
and equality orientation were checked through all consumers, including the
zero discarded-mass specialization. Namespace names are checked against every
prior targeted/global axiom name; imports and target registration are checked.

These are source-level checks only. No local Lean, lake, lint or Python tests
were run. Compiler elaboration, all normal/slow lint and transitive axiom audit
must succeed on the new SHA before acceptance.

## Validation and remaining work

Expected surface: 175 build targets, 137 targeted / 278 global modules,
205 Python tests. New math/core/example modules are all explicitly targeted;
the global ReBeL inventory adds core and example, and the math source is fully
linted/audited by the targeted pass. Existing lists are not reduced.
Workflow triggers were re-read; branch/path conditions match all four workflows.
Workflow definitions and audit criteria are unchanged.

Still open: useful bounds when the actual solver kernel itself changes;
internal rooted child versus original-game fresh solver equivalence with
noise/fallback/budget/clock preserved; small native-chain support/signed
replacement costs; SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 acceptance.
The discarded-mass formula need not be small. It is model-posterior accounting,
not identification with an unknown opponent's actual posterior.
Keep finite-T and child tolerance terms, printed R5 versus corrected statements,
and all prior pinned acceptance journals. No source-level obligation is promoted.
