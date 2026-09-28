# Recomputed recursive value batch — pending exact-SHA Actions

Parent and accepted dependency: ce81eaecde20fb02de0a191ba1ceb64e32bafe16.
The previous stopped-mass repair loop is complete; see
M06-stopped-mass-ce81eae-accepted.md. Its success does not validate this batch.

## Dependency order and scope

This batch connects changed solver computations to actual native execution:
policy-value comparison, public/live posterior residual, actual recursive
private draws, live/missing/stopped state handling, signed local cost,
native forward schedule accounting, and initial-security inheritance.
The two new core modules, concrete consumers and rational controls are
committed together; no per-lemma workflow wait is intended.

PBSRecursivePosteriorValue defines recursivePolicyValueChange as the signed
difference of two canonical unilateral continuation values under the SAME
incoming law and SAME unknown opponent. executionKernelCharge bounds it when
an independent kernel estimate is available. cfrDFactualChild_changedPolicy_residual
shows that posterior filtering bounds only the residual after retaining this
signed change. pbsRecursiveDepthDraw_public_child_residual instantiates both
policies with actual recursive computations and both draws with their exact
averages. The saved-PBS tolerance and live-child positiveMassFloor * loss are
separate, even if the posterior laws happen to agree.

PBSRecursiveRecomputedValue records noise, cut list, tolerance and fuel for each
actual resolver stage in PBSRecursiveResolveConfig. pbsRecursiveRecomputedOutcome
is a proof-side value comparison at the actual state's saved PBS; no deployed
algorithm is changed. Off the existing pbsCarriedCFRException its value equals
the original private-draw outcome through stage + remaining fuel.
pbsRecursiveRecomputedLoss_eq_policyValueChange identifies the live local term
with old retained policy minus the recomputed policy. No incumbent equality
or small Nash-gap-to-policy-distance inference is used.

pbsRecursiveReplacement_expected_loss_le charges the exact native signed loss
by the computed value loss plus 2 * payoffBound * ACTUAL unsupported-state mass.
pbsRecursiveRecomputedBudget recursively adds these terms on the full state law
AFTER the native carriedMemoryStep. It never advances that law using the average
comparison, never pools saved posteriors, and never samples a new late draw.
carriedSignedSequenceLoss_le_recomputedBudget and
privateRecursiveResolve_inherits_recomputedBudget connect this computed budget
to the existing exact signed telescope and original initial security bound.

## Concrete and negative controls

The hidden-type noisy chain uses two actual recursive configurations:
[1,1,1] at tolerance 1/4 and [1] at tolerance 1/8, each with fuel 1, plus
final fuel 1. Its total fuel 3 is explicitly proved. A zero-stage consumer
retains a positive late tail. The actual noisy parent also consumes the
public/live residual theorem: public termination removes the posterior term
but does NOT erase the changed-budget policy term.

Five new Fraction tests cover 36 rare/correlated posterior cases with a signed
residual, changed computations even at identical posterior laws, tight actual
unsupported-mass penalties and gain signs, 27 native joint-forward schedules,
and retained stage/late randomness versus resampling, zero/missing/stopped
queries. These finite controls are not represented as running a Lean solver
or an actual CFR training trace.

## Precommit type and proof review

This is static review; compilation, Python execution, lint and axiom validation
remain pending Actions on the new SHA.

- Read the actual signatures of cfrDFactualChild_public_continuation_error,
  pbsRecursiveDepthDraw_value/from_support, recursive solver/stage definitions,
  carriedMemoryStep_selected_late_expect, replacement/signed-sequence definitions,
  executeCarriedResolves_loss_eq_signed, and privateRecursiveResolve_inherits_signedLoss.
- Read FinDist event-error, expectation and atom-variation consumers. The signed
  residual is first-minus-second; native loss is OLD-minus-recomputed. The
  execution charge follows its first profile. Arithmetic proof steps preserve
  this direction and add matching left/right bounds with add_le_add.
- Every new PublicBelief.condition explicitly supplies the full signal carrier.
  Generic E/M share the universe required by PBSRecursiveDepthNoise; this does
  not narrow any existing theorem. Example carriers are model fullPrior.
- Every state-dependent PBS index uses the same full-model publicTrace of that
  state's history. The live support argument is obtained only from the explicit
  complement of pbsCarriedCFRException. Missing beliefs and stopped stages use
  the old tail. No arbitrary actual history is declared supported.
- The concrete parent uses a typed PBSChildSolve and typed behavioral trunk
  before applying its dependent possible proof. Existing finite History, Choice
  and classical InfoState equality instances are supplied. Both solver calls
  preserve fallback, payoff, noise, cuts and the separate tolerance arguments.
- Configurations map to the unchanged pbsRecursiveDepthStage; the list induction
  uses remaining fuel from the tail stages plus finalFuel. The concrete totalFuel
  equality is stated under the exact local stage alias.
- Scope Fintype History only where atom variation or actual solver construction
  needs it, omitting it for the generic posterior residual. New public names were
  compared against all 2221 targeted/5357 global accepted declaration names;
  all 18 are distinct. New source lines are within 100 UTF-16 columns.
- Registered all three new modules in the umbrella, target list and targeted
  audit consumer without dropping old entries. No workflow, audit criterion,
  pinned source, solver definition or heartbeat limit was changed.

Expected surface: 178 build targets; 140 targeted and 281 global audit modules;
210 Python tests. No acceptance is inferred from these expected counts.

## Remaining mathematical boundary

The new budget is COMPUTED but is not proved small. Its unsupported probabilities
and changed-policy terms need solver-specific estimates. The public/live
residual evaluates model laws and does not identify them with an unknown
opponent's factual law; the native budget instead uses actual joint state laws.
Neither is a proof of equivalence between an internal chance-rooted child and
an original-game fresh solve with different root encoding, clock, fallback,
noise allocation or budget. Those correspondence obligations remain open.

This dependency batch does not promote SEARCH-CFRD, SEARCH-ERROR or
SAFE-THEOREM3. Keep printed R5 separate, retain finite-T and child-tolerance
terms, and do not assume final-iterate or network-learning convergence.
The already accepted target/average/frontier journal pins are unchanged.
