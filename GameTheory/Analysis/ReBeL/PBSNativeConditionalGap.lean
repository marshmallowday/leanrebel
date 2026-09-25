/-
# Conditional error of actual private CFR iteration draws

The opponent is the SAME computed average throughout this comparison. Only
one player's native iteration is drawn, privately and uniformly, and retained
throughout the continuation. Every draw has a nonnegative current-opponent
best-response gap. Therefore the expectation of its ABSOLUTE gap, not merely
the absolute expectation, equals the averaged policy's gap on supported types.
No analogous conclusion for changed opponents or absent roots is asserted.
-/

import GameTheory.Analysis.ReBeL.PBSConditionalValueStability
import GameTheory.Analysis.ReBeL.PBSSupportedSampling

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}

/-- The genuine native sampler preserves conditional continuation payoff at
any supported root type, against arbitrary FIXED opposing policies. The
training horizon and execution horizon may differ. No hidden-root policy is used. -/
theorem pbsInformationCFR_conditional_sampling_value
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) (value : E.History → ℝ) (type : T) (supported : type ∈ own.support) :
    (cfrIterationLaw t).expect (fun n => slice.conditionalPayoff opponents steps value
        (pbsInformationCFRIterate M (slice.mixture own) fallback payoff fuel n.val who) type) =
      slice.conditionalPayoff opponents steps value
        (pbsInformationCFR M (slice.mixture own) fallback payoff fuel t who) type := by
  unfold TypeBeliefSlice.conditionalPayoff PublicBelief.continuationLaw
  simp only [FinDist.expect_bind]
  rw [FinDist.expect_comm]
  apply FinDist.expect_congr
  intro history reached
  have inRoot : history ∈ (slice.mixture own).law.support := by
    rw [TypeBeliefSlice.mixture, FinDist.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨type, supported, reached⟩
  have same := congrArg (fun law : FinDist E.History => law.expect value)
    (pbsInformationCFR_sampling_from_support M (slice.mixture own) fallback payoff fuel t
      opponents who steps history inRoot)
  simpa only [pbsInformationCFRSampleFrom, FinDist.expect_bind] using same

/-- Native own-iteration gap against the computed AVERAGE opponent's Eq. (1)
value. This is not a self-play gap against the same-index opposing iterate.
The iteration index is chosen before play, not disclosed to the opponent. -/
def pbsInformationCFRConditionalDrawGap
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (type : T) (round : Fin t) : ℝ :=
  let average := pbsInformationCFR M (slice.mixture own) fallback payoff fuel t
  slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel
      (payoff who) average type -
    slice.conditionalPayoff average fuel (payoff who)
      (pbsInformationCFRIterate M (slice.mixture own) fallback payoff fuel round.val who) type

/-- Every individual draw is bounded by the same conditional best response.
This sign, not an invalid exchange of absolute value and expectation, is used below. -/
theorem pbsInformationCFRConditionalDrawGap_nonneg
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (type : T) (round : Fin t) :
    0 ≤ pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t type round :=
  sub_nonneg.mpr (slice.conditionalPayoff_le_infoValue
    (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (fallback player)) fuel (payoff who)
    (pbsInformationCFR M (slice.mixture own) fallback payoff fuel t) type
    (pbsInformationCFRIterate M (slice.mixture own) fallback payoff fuel round.val who))

/-- The mean ABSOLUTE native gap equals the averaged gap at a supported type.
No per-iterate Nash claim is made. An absent root cannot be cancelled from the
model mixture, and is deliberately not covered by this equality. -/
theorem pbsInformationCFRConditionalDrawGap_mean_abs
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (type : T) (supported : type ∈ own.support) :
    let average := pbsInformationCFR M (slice.mixture own) fallback payoff fuel t
    (cfrIterationLaw t).expect (fun n =>
        |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t type n|) =
      |slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel
          (payoff who) average type -
        slice.conditionalPayoff average fuel (payoff who) (average who) type| := by
  let average := pbsInformationCFR M (slice.mixture own) fallback payoff fuel t
  calc
    _ = (cfrIterationLaw t).expect
        (pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t type) := by
      apply FinDist.expect_congr
      intro n _
      exact abs_of_nonneg
        (pbsInformationCFRConditionalDrawGap_nonneg M slice own fallback payoff fuel t type n)
    _ = slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel
          (payoff who) average type -
        slice.conditionalPayoff average fuel (payoff who) (average who) type := by
      unfold pbsInformationCFRConditionalDrawGap
      rw [FinDist.expect_sub, FinDist.expect_const,
        pbsInformationCFR_conditional_sampling_value M slice own fallback payoff fuel t
          average fuel (payoff who) type supported]
    _ = _ := (abs_of_nonneg (sub_nonneg.mpr (slice.conditionalPayoff_le_infoValue
      (fullSignals_perfectRecall M.toInfoSignals)
      (fun player => liftPolicy M player (fallback player)) fuel (payoff who)
      average type (average who)))).symm

/-- A dominated type-query law consumes the ACTUAL private iteration law.
Its density cap is explicit; no such cap for an independently carried PBS is
inferred. The finite-time residual is the existing information-set CFR bound. -/
theorem pbsInformationCFR_native_query_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel t : Nat) [NeZero t]
    (query : FinDist T) (ratio : T → ℝ) (factor : ℝ) (factorNonneg : 0 ≤ factor)
    (density : ∀ type, query.prob type = own.prob type * ratio type)
    (ratioBound : ∀ type ∈ own.support, ratio type ≤ factor) :
    query.expect (fun type => (cfrIterationLaw t).expect (fun n =>
      |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t type n|)) ≤
        factor * pbsRootCFRBound M (slice.mixture own).law bound fuel t := by
  let average := pbsInformationCFR M (slice.mixture own) fallback payoff fuel t
  calc
    _ = query.expect (fun type =>
        |slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel
            (payoff who) average type -
          slice.conditionalPayoff average fuel (payoff who) (average who) type|) := by
      apply FinDist.expect_congr
      intro type sampled
      exact pbsInformationCFRConditionalDrawGap_mean_abs M slice own fallback payoff fuel t type
        (informationReweight_support own query (fun kind => kind) ratio density sampled)
    _ ≤ _ := pbsInformationCFR_reweighted_infoGap_abs_le M slice own fallback payoff
      zeroSum bound nonneg bounded fuel t query ratio factor factorNonneg density ratioBound

/-- Under the model's own type law the density factor is one and no positive
mass floor is needed. This is a native-draw MEAN bound, not a uniform bound
on every type, every iterate, or a paired self-play iterate. -/
theorem pbsInformationCFR_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel t : Nat) [NeZero t] :
    own.expect (fun type => (cfrIterationLaw t).expect (fun n =>
      |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t type n|)) ≤
        pbsRootCFRBound M (slice.mixture own).law bound fuel t := by
  simpa only [one_mul] using pbsInformationCFR_native_query_mean_abs_le M slice own fallback
    payoff zeroSum bound nonneg bounded fuel t own (fun _ => 1) 1 (by norm_num)
    (fun _ => (mul_one _).symm) (fun _ _ => le_rfl)

/-- The same computed positive budget selects the number of ACTUAL native
iterations. No equilibrium witness, conditional-rate certificate, or learner
convergence premise is supplied by the caller. -/
theorem pbsInformationBudget_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h player, |utility h player| ≤ bound)
    (error : ℝ) (positive : 0 < error) :
    let t := pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error
    own.expect (fun type => (cfrIterationLaw t).expect (fun n =>
      |pbsInformationCFRConditionalDrawGap M slice own fallback (fun player h => utility h player)
        fuel t type n|)) ≤ error := by
  exact (pbsInformationCFR_native_mean_abs_le M slice own fallback
    (fun player h => utility h player) zeroSum (fun _ => bound) (fun _ => nonneg)
    (fun player h => bounded h player) fuel
    (pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error)).trans
      (pbsInformationBudgetRounds_error M (slice.mixture own).law (fun _ => bound)
        fuel error positive)

end GameTheory.ReBeL
