# M06 carried posterior, primitive rates and signed late-value batch

## Branch and batch boundary

Continue the re-read existing M06 work branch
rebel/m06-kernel-value-repair-20260927 from
fa95a3d06b2061b18fa678518c2adf0531650377. The previous repair is accepted from
all four same-SHA Actions runs, documented in
M06-opponent-value-transport-fa95a3d-accepted.md. No competing branch update was
observed. Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.

The user's batch instruction supersedes earlier thin-slice workflow guidance.
ROADMAP M06, STATUS and the owner ledger identify linked gaps in recursive
posterior identification, source rates, late-value transport and signed
CarriedResolveStepBounds. Implement these related mechanisms in dependency
order, together with actual solver consumers and independent controls, then
perform one commit and one parallel workflow round.

This batch ends at a real semantic boundary: a primitive execution-rate
hypothesis is not supplied by a finite-iteration Nash guarantee. Different
optimal strategies can have different transition laws. General small solver
rates need additional analysis, potentially a tighter signed value envelope
rather than requiring all policy distances to vanish. No specification or
acceptance condition is weakened to treat these costs as small.

## Definitions, assumptions and consumers

1. In PBSOpponentModelTransport, executionKernelCharge is nonnegative, splits
   exactly across a horizon at the first profile's checkpoint law, and is at
   most fuel*rate under an explicit primitive one-step L1 rate. Incoming law
   variation and opponent/model execution costs remain separate. Their mean
   public conditional defect is bounded under the actual public law, including
   missing model queries and without a reach-probability floor.

2. carriedBeliefUpdate_eq_atObservation and
   resolvedNextState_belief_eq_atObservation identify the stored posterior with
   certified conditioning of the chosen model's continuation of the incoming
   joint belief. This certifies the posterior actually stored by recursion.
   It DOES NOT identify the model posterior with the factual unknown-opponent
   posterior, nor identify every caller-supplied TypeBeliefSlice with it.

3. TypeBeliefSlice.conditionalGap_abs_sub_le_executionRate consumes primitive
   kernel rates for the two optimal responses and the retained response through
   the existing measured-cost proof. The extra bound is
   2*B*rootVariation + 2*B*fuel*rate. Its primitive hypothesis quantifies over
   legal own responses and histories; it is not inferred from scalar Nash.

4. New PBSCarriedValue proves carriedMemoryStep_selected_expect. In a live
   stage, the same private profile draw executes stage.fuel and the remaining
   late horizon. At a stopped stage the prior selected profile is preserved.
   The proof uses canonical runBehavioralFrom_add and existing memory updates.

5. carriedReplacementExecutionCharge compares the old selected own policy
   with each native sampled own policy against the SAME arbitrary unknown
   opponent, from the actual input history, over stage.fuel+remaining. Within
   that comparison its prefix weights follow the OLD comparator profile.
   This differs from an opponent/model posterior charge. Across stages, the
   incoming state distributions follow actual native resolver execution.

6. carriedMemoryStep_selected_loss_le derives the SIGNED old-minus-new
   selected continuation loss from B times this computed charge. It includes
   the late horizon, retains random private draws, and needs only bounded
   payoff and finite histories. No local payoff-loss certificate is assumed.
   Stopped stages cost zero even with positive remaining fuel.

7. carriedSequenceExecutionCharge sums expected stage costs under the native
   full-state forward laws. executeCarriedResolves_loss_le_executionCharge
   telescopes signed comparisons over the complete finite schedule.
   privateRecursiveResolve_inherits_executionCharge and
   cfrDDepth_recursive_security_executionCharge connect this to the existing
   initial depth-limited solver guarantee, preserving oracle error, child
   loss and the finite-T residual. The latter retains the existing explicit
   initial oracle contracts; it does not assert learner convergence.

8. carriedResolveStepBounds_of_executionRate constructs the existing signed
   certificate from primitive transition rates and a remaining-horizon cap,
   rather than accepting stage payoff comparisons as premises.
   pbsCarriedDepthSequence_value_loss_le consumes the computed bound for the
   actual configured noisy-depth solver schedule. Small rates for unrestricted
   constructed solvers remain open.

## Controls and validation

New Examples.PBSCarriedValue consumes two actual noisy depth stages with
iteration counts 2 and 3, prediction bias 1/8 and child tolerance 1/4. It also
checks zero stage fuel with positive late fuel and certified selected-iterate
posterior storage on supported model observations.

Seven new independent Fraction tests cover 9 late-tail fixtures, 5 private-draw
mixtures and 27 forward telescoping schedules, plus rare actual versus model
weights, stopped no-query behavior, negative signed gain cancellation and
stored-prior/selected-policy conditioning versus reset or pooled models.

This batch is pending its own Actions. No Lean or Python validation was run
locally or inside the plugin. Sources were reviewed for signatures, dependency
orientation, scope, line widths and absence of proof placeholders; those are
not compiler results. The two new modules are added to the analysis umbrella,
explicit targeted build list and complete targeted axiom/lint consumer.
Targets increase 154→156, targeted modules 116→118, global modules 259→261.
Expected Python test count increases 153→160. No previous target is removed.
All workflow definitions, trust gates, toolchain and dependency pins are retained.

Current triggers were re-read: CI all pushes; ReBeL checks main or rebel/**;
targeted rebel/m06* with the matching Lean/target/auditor paths. Check distinct
same-SHA runs after the ref update, then schedule one thread follow-up in JST
approximately 50 minutes after that update.

## Remaining M06 acceptance

- Identify the specific conditional type kernels needed by every recursive
  solver value comparison, beyond the exact stored model-posterior identity.
- Derive useful solver-specific small root, execution and support leakage rates
  or stronger signed value bounds; primitive hypotheses and measured costs
  alone do not establish the claimed Theorem 3 constants.
- Complete the paper-to-implementation acceptance review of SEARCH-FRONTIER,
  SEARCH-CFRD and SEARCH-ERROR and the corrected/restricted SAFE-THEOREM3;
  keep the printed R5 mismatch separate.
- Verify this entire batch at its exact source SHA, including full transitive
  axioms, normal/slow lint, build, architecture and all Python controls.

M06 is incomplete. The next work should again combine related remaining items
and aggregate all CI fixes, rather than commit after each short lemma.
