# Solver-derived Nash replacement batch — pending exact-SHA Actions

Parent and accepted dependency: 7f5526ca40282dd11a42301e5d12cad9ac3eb37e.
See M06-recomputed-value-7f5526c-accepted.md for its complete Actions evidence.
That acceptance is not validation of the new modules.

## Remaining work and chosen integration boundary

ROADMAP M06 requires a real depth-limited solver, finite-T/numerical error
propagation and unknown-opponent test-time safety. STATUS and the dedicated
owner ledger leave three connected groups:
1. Bound the changed value and support terms in actual fresh recursive chains.
2. Identify internal chance-rooted children with original-game fresh solvers,
   respecting posterior, clock, fallback, noise and allocated budgets.
3. Review remaining SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 source obligations.

This batch handles the first group's solver-derived comparison, from the
canonical Nash deviation through actual recursive solving, horizon checks,
native forward budgets, concrete examples and independent rational controls.
It is committed together. Group 2 has a substantive unresolved compatibility
condition: the supplied noise family may depend on the protocol representation,
and root-law equality alone does not identify two solver computations.
Group 3 cannot be promoted from these dependency results.

## Mathematical content and direction

nashReplacementTransport compares ACTUAL roots with the supplied model PBS and
the actual unknown opponent with the fresh solver's computed AVERAGE opponent.
It compares opposing policies while fixing the old own policy on one side and
the fresh own policy on the other. Both charges use actual prefixes. The
root-law L1 discrepancy appears twice.

behavioralNash_replacement_le applies the old own policy as a legal unilateral
deviation against the fresh Nash profile, then transports the old and fresh
payoffs separately. pbsRecursiveDepth_replacement_le discharges the Nash premise
using the actual structurally recursive solver's theorem, its numerical
contract and positive requested tolerance. There is no caller-supplied child
equilibrium or unexplained small changed-policy hypothesis.
nashReplacementTransport_le_rates exposes independent one-step opposing-kernel
rates and the incoming root-law discrepancy with the full finite fuel factor.

When the incoming law is the model law and the opponent is the computed fresh
opponent, pbsRecursiveDepth_model_replacement_le gives the requested tolerance
against ANY old own policy. It does not assert the own policies are close.
In general, the root and opponent terms cannot be dropped.

PBSRecursiveNashAligned checks the actual noise contracts, positive tolerances
and cuts.sum = stage fuel + all later stage fuel + final fuel. The fresh
solver's finite-horizon Nash theorem is used only at that horizon.
pbsRecursiveNashEnvelope evaluates the actual state's singleton history law
against its saved model PBS; no state is declared model-supported. Missing
beliefs and stopped stages retain the exact existing signed comparison.
pbsRecursiveNashBudget retains the actual unsupported-mass charge from private
sampling and advances only the native full-state memory law. The budget bounds
the previous recomputed budget, the exact signed sequence loss and the final
initial-security inheritance theorem.

The fresh average opponent used in the Nash comparison is not silently
identified with the selected private MODEL profile that generates a posterior.
The native solver, draw, posterior update and private memory are unchanged.

## Consumers and negative controls

The actual hidden-type three-level solver gives a 1/8 model-opponent bound for
arbitrary old policies. An actual two-stage noisy schedule uses [1,1,1] at
tolerance 1/4 and [1,1] at tolerance 1/8, with stage fuels 1,1 and final fuel 1.
It proves its alignment and consumes the full native Nash transport budget.
The older recomputed-cost schedule with second cuts [1] is proved NOT aligned
with final fuel 1: its earlier exact-cost theorem remains valid, but the stronger
Nash consumer cannot silently extend that solve from horizon 1 to horizon 2.

Five Fraction controls cover 729 model/actual/old/fresh/opponent combinations
with both-player Nash regret, a tight two-root-error coefficient, a genuine
exact-Nash matching-pennies failure when opponent transport is erased, a delayed
payoff counterexample to horizon extension, nine native forward-weight cases,
tight unsupported-mass penalties, and singleton-versus-mixture discrepancy.
These are independent finite controls, not an execution of Lean's CFR trace.

## Precommit type and semantic review

Read the actual signatures of pbsRecursiveDepth_isNash, canonical IsNash
consumers, behavioralBeliefForm/PublicBelief.continuationLaw,
runBehavioralFrom_atomVariation_le, abs_expect_sub_le_atomVariation,
executionKernelCharge_le_mul, the prior recomputed outcome/loss/budget and
private-security consumers, carriedResolveFuel, and the concrete hidden-type
solver examples. Checked the following through all new consumers:

- Generic E/M use the same uniform universe as the actual recursive noise family.
  Full-information signatures are explicit; new code does not create a
  PublicBelief.condition with an inferred signal carrier.
- The Nash deviation is the legal old own policy against the fresh average
  opponent. The two actual runs share the same unknown opponent. The two
  transport charges have the correct actual-to-model direction.
- The full dependent saved-belief index is unchanged. The live helper receives
  the exact state's stored proof and the same cuts/fuel/remaining equality.
  No partial stage unfolding is used to rewrite an if/Decidable pair.
- The recursive alignment proof is reverted before list induction so the
  induction hypothesis consumes the tail's alignment at the native next law.
  Scalar configuration fuel is definitionally matched to the actual mapped
  stage runner, avoiding inferred arithmetic fuel rewriting.
- Examples supply the finite History instance, retain the exact four-field
  configuration order, use existing protocol/action instances, and prove total
  fuel 3 explicitly. No rooted/original History or policy is coerced across models.
- New declarations were compared against all 2275 targeted/5411 global accepted
  axiom names. No collisions were found. New fields are not introduced without
  documentation; every public declaration and local instance is documented.
  New core lines are within 100 characters.
- Preserve all 178 build targets and 140 targeted/281 global modules, adding two
  cores and one example to targets, umbrella and targeted audit. Expected new
  surface is 181 targets, 143/284 modules and 215 Python tests.

This is static review, not Lean compilation or Python execution. All actual
build/lint/axiom/Python checks remain pending GitHub Actions on the new SHA.
No workflow, audit criterion, existing solver definition or frozen/pinned
acceptance source is modified.

## Limits retained

The native singleton-to-PBS discrepancy can be large even when aggregate laws
coincide. Averaging pointwise bounds does not cancel it; a sharper conditional
grouping argument is still needed for a general small native-chain rate.
The unknown opponent need not resemble the computed model opponent.
Actual unsupported mass is still separately charged, and support alone is
not equality of distributions. Thus this is not the full Theorem 3 small-rate
claim or a solution of internal-rooted/fresh-original equivalence.

Keep finite allocated iterations, numerical and child tolerances, native
correlations and late fuel. No learner, final-iterate, Nash-value target or
profile convergence is assumed. Printed R5 and corrected/limited claims remain
separate. M06 remains incomplete.
