# Rooted query-weighted comparison batch

Parent and newly accepted checkpoint:300175a31f8d40d27e40d31b7b60fe6ce228a39f.
New code is pending exact-SHA Actions, lint, axiom and semantic acceptance.
This is a project dependency for M06; no paper obligation is promoted.

## Integrated result and boundary

FinDistConditionalMass proves that model-weighted conditional event shares
integrate exactly to original event mass, including a total absent-label
fallback whose model label weight is zero. No finite label carrier or positive
uniform lower bound on query reach is needed. For a different incoming law,
the upper bound retains its unhalved L1 atomVariation from the model law.

PBSRootQueryMass applies this to stopped histories in the actual rooted
parent prefix. A possible noninitial public query selects the factual live
child and the saved unfiltered public MODEL posterior. The internal recursive
request is exactly child.law.positiveMassFloor * parentLoss. The independently
recomputed fresh original solver keeps its own noise, partition, fallback and
tolerance. Existing recursive Nash/private-draw theorems discharge the two
query comparisons, rather than accepting Nash certificates from the caller.

The paired diagnostic is absolute selfplay scalar difference and signed
internal-selfplay minus fresh-private MODEL value. Integrating with the
incoming history law's own query weights gives respectively:

- parentLoss + freshError + 2*bound*(modelStoppedMass + actualModelL1);
- parentLoss + 2*freshError + 2*bound*(modelStoppedMass + actualModelL1).

Under model weights, actualModelL1=0. The native-checkpoint wrapper uses the
history marginal of a supplied joint PrivateIterationState law; it does not
replace the joint law or modify the native transition.

A label outside the eligible noninitial live queries contributes zero ONLY
to this restricted diagnostic. This is not an assertion that its native cost
is zero, nor a security theorem for actual factual execution. Fixed parent
trunk, cutoff and remaining horizon are shared across the diagnostic. The
native checkpoint theorem does not identify each state's saved PBS or
incumbent with that fixed parent. This is the mathematical boundary of this
batch, not a file-size split.

## Assumptions and source roles

The query comparison retains finite original history/action carriers, the
actual rooted history enumeration, uniform protocol universe, two players,
zero-sum payoff bounded by a nonnegative bound, positive parentLoss and
freshError, both recursive noise contracts, and both partition sums equal to
the same remaining horizon. The unknown opponent is fixed outside the fresh
private draw. No individual seed is assumed Nash.

The event-mass identity is finite-law disintegration, already represented by
FinDist.eq_bind_condOnFibre. The scalar/private premises come from the accepted
PBSRootStoredValue and actual recursive solver theorems. The actual selected
child request is defined by cfrDComposedChildTable and the accepted
pbsRootChildRecursive_selected connection, not a newly invented request.
This dependency does not alter the printed paper formula. Independent
prediction error, finite-T allowance and child loss remain as recorded in
M06-theorem3-interpretation.md; no term is absorbed into prediction error.

## Concrete consumers and controls

The actual hidden-type noisy rooted parent uses cut2 (administrative root
draw plus original chance), remaining1, numerical bias1/8, childloss1/4,
internal[1] and fresh[1]/tolerance1/4. Examples instantiate the model-weighted
pair, an arbitrary correlated native checkpoint and the excluded initial
query. The mass floor is taken from each actual child.

Five independent Fraction tests cover27 rare/asymmetric conditional shares,
81 incoming/model weights including absent labels,243 independent matrix
Nash pairs with private averaging,27 mass-scaled requests, and joint-versus-
product/history-clock/excluded-diagnostic controls. They are not actual CFR
execution, and have not been executed locally.

## Precommit type and static review

Read actual signatures of FinDist.expect_congr/map/bind/mono/smul/const,
probOf_condOn_eq_inter, eq_bind_condOnFibre, abs_expect_sub_le_atomVariation,
positiveMassFloor_pos/le and prob_le_one; also public child possibility,
pbsRootStored_fresh_value/security, rooted selected child, saved-state
projection and the existing concrete noisy parent.

Original fullInformation has all6 universes explicit. Rooted public signals
remain Option(List originalSignal); original and rooted History carriers are
not interchanged. Independent label and private-memory universes remain
independent. PublicBelief observations and child/state history indices remain
intact; no dependent casts or new conditioning operation are introduced.
The two recursive computations, mass-scaled request and remaining horizon
match all consumers. Private deficit is OLD-internal minus NEW-private with
an extra freshError. Returned local lets are reduced before stopped-fraction
rewrites; concrete consumers reduce only local aliases and zero variation
before ordinary exact type comparison. The native wrapper rewrites both
expect_map layers.

All15 new public names were compared against5642 accepted global axiom names
without collision. Three local instances have docstrings. New Lean widths
are at most100 characters; comment-stripped existing transport regex has no
match; no placeholders were introduced. These are static inspections, not
Lean compilation, phase2 execution or test execution.

Registration grows202→205 build targets,164→167 targeted audit modules,
304→306 global ReBeL modules and250→255 Python tests. The math module is
directly linted/audited by targeted checks and transitively imported from
ReBeL; the existing global prefix selection is unchanged. No old target is
removed. Workflow, audit criteria, heartbeat limits and solver definitions
are unchanged.

## Remaining dependency order

1. Validate all new modules and concrete consumers on this exact new SHA.
2. Connect each actual successive native query's saved MODEL input and
   conditional incumbent/history law, preserving private/PBS/history
   correlations and changing clocks. The fixed-parent diagnostic alone does
   not supply this connection.
3. Bound actual/model discrepancy and conditional incumbent/selfplay,
   support/stopped costs using the solver, then telescope on the unchanged
   native forward law to obtain useful small rates.
4. Review recursive safety against SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3
   original obligations and append acceptance only when all requirements hold.

No calibration, rare-query rate, target-value convergence, learner accuracy,
policy closeness or final-iterate convergence is assumed. Existing source
acceptances remain untouched; M06 and full Theorem3 remain incomplete.
