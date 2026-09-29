/-
# Scalar values of recursive solves on different public beliefs

Cross deviations compare self-play values after transporting a fixed profile
between root laws. Different algorithms' outputs need not be equal. Every
recursive solver below supplies its own finite-budget Nash guarantee.
-/

import GameTheory.Analysis.ReBeL.PBSRecursivePotential

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)

/-- Different root laws cost one uniform fixed-profile expectation error.
The first opposing-player deviation and second own deviation keep both
Nash allowances explicit, for either focal player. -/
theorem behavioralNash_crossRoot_value_sub_le
    {firstObs secondObs : List M.PublicSignal}
    (firstBelief : PublicBelief M.toInfoSignals firstObs)
    (secondBelief : PublicBelief M.toInfoSignals secondObs)
    (first second : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h p => payoff p h))
    (firstError secondError rootError : ℝ)
    (firstNash : IsNash (behavioralBeliefForm M firstBelief fuel)
      (euPreferenceWithin firstError (fun h p => payoff p h)) first)
    (secondNash : IsNash (behavioralBeliefForm M secondBelief fuel)
      (euPreferenceWithin secondError (fun h p => payoff p h)) second)
    (roots : ∀ profile : Profile M.behavioralSignature,
      |(firstBelief.law.bind (M.runBehavioralFrom profile fuel)).expect (payoff who) -
        (secondBelief.law.bind (M.runBehavioralFrom profile fuel)).expect (payoff who)| ≤
        rootError) :
    (firstBelief.law.bind (M.runBehavioralFrom first fuel)).expect (payoff who) -
      (secondBelief.law.bind (M.runBehavioralFrom second fuel)).expect (payoff who) ≤
      firstError + secondError + rootError := by
  have lower := behavioralNash_model_security M firstBelief first second who fuel
    payoff firstError zeroSum firstNash
  have upper := (isNash_iff (F := behavioralBeliefForm M secondBelief fuel)
    (weaklyPrefers := euPreferenceWithin secondError (fun h p => payoff p h))
    second).mp secondNash who (first who)
  rw [euPreferenceWithin_apply] at upper
  simp only [expectedUtility, behavioralBeliefForm, PublicBelief.continuationLaw] at upper
  have cross := (abs_le.mp (roots (Profile.update second who (first who)))).2
  linarith only [lower, upper, cross]

/-- The same uniform root comparison controls both directions without
requiring opponent agreement, a unique equilibrium or an exact equilibrium. -/
theorem behavioralNash_crossRoot_value_abs_le
    {firstObs secondObs : List M.PublicSignal}
    (firstBelief : PublicBelief M.toInfoSignals firstObs)
    (secondBelief : PublicBelief M.toInfoSignals secondObs)
    (first second : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h p => payoff p h))
    (firstError secondError rootError : ℝ)
    (firstNash : IsNash (behavioralBeliefForm M firstBelief fuel)
      (euPreferenceWithin firstError (fun h p => payoff p h)) first)
    (secondNash : IsNash (behavioralBeliefForm M secondBelief fuel)
      (euPreferenceWithin secondError (fun h p => payoff p h)) second)
    (roots : ∀ profile : Profile M.behavioralSignature,
      |(firstBelief.law.bind (M.runBehavioralFrom profile fuel)).expect (payoff who) -
        (secondBelief.law.bind (M.runBehavioralFrom profile fuel)).expect (payoff who)| ≤
        rootError) :
    |(firstBelief.law.bind (M.runBehavioralFrom first fuel)).expect (payoff who) -
      (secondBelief.law.bind (M.runBehavioralFrom second fuel)).expect (payoff who)| ≤
      firstError + secondError + rootError := by
  have upper := behavioralNash_crossRoot_value_sub_le M firstBelief secondBelief first second
    who fuel payoff zeroSum firstError secondError rootError firstNash secondNash roots
  have lower := behavioralNash_crossRoot_value_sub_le M secondBelief firstBelief second first
    who fuel payoff zeroSum secondError firstError rootError secondNash firstNash
    (fun profile => by simpa only [abs_sub_comm] using roots profile)
  exact abs_le.mpr ⟨by linarith only [lower], upper⟩

variable [Fintype E.History]

/-- Root variation bounds every common continuation profile. Only the
fixed kernel is transported; its equilibrium need not survive a root change. -/
theorem behavioralRoot_profile_error
    {firstObs secondObs : List M.PublicSignal}
    (firstBelief : PublicBelief M.toInfoSignals firstObs)
    (secondBelief : PublicBelief M.toInfoSignals secondObs)
    (profile : Profile M.behavioralSignature) (fuel : Nat)
    (value : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |value h| ≤ bound) :
    |(firstBelief.law.bind (M.runBehavioralFrom profile fuel)).expect value -
      (secondBelief.law.bind (M.runBehavioralFrom profile fuel)).expect value| ≤
      bound * FinDist.atomVariation firstBelief.law secondBelief.law := by
  have transport := runBehavioralFrom_atomVariation_le M profile profile fuel
    firstBelief.law secondBelief.law
  rw [executionKernelCharge_self, add_zero] at transport
  exact (FinDist.abs_expect_sub_le_atomVariation _ _ value bound bounded).trans
    (mul_le_mul_of_nonneg_left transport nonneg)

variable [∀ who, Fintype (E.Action who)]

/-- Independently configured recursive solves discharge both Nash premises.
Only total horizon must agree; noise, cut partition, fallback and tolerance
can differ. The uniform root error concerns common fixed profiles only. -/
theorem pbsRecursiveDepth_crossQuery_value_error
    (firstNoise secondNoise : PBSRecursiveDepthNoise.{u})
    (firstNoiseBound : PBSRecursiveDepthNoiseBound firstNoise)
    (secondNoiseBound : PBSRecursiveDepthNoiseBound secondNoise)
    (firstCuts secondCuts : List Nat) (horizon : firstCuts.sum = secondCuts.sum)
    (firstFallback secondFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h p => payoff p h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    {firstObs secondObs : List M.PublicSignal}
    (firstBelief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals firstObs)
    (secondBelief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals secondObs)
    (firstError secondError : ℝ) (firstPositive : 0 < firstError)
    (secondPositive : 0 < secondError) (who : Fin 2) (rootError : ℝ)
    (roots : ∀ profile : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature,
      |(firstBelief.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
            profile firstCuts.sum)).expect (payoff who) -
        (secondBelief.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
            profile firstCuts.sum)).expect (payoff who)| ≤ rootError) :
    let first := pbsRecursiveDepth firstNoise firstCuts E M firstFallback payoff bound
      firstBelief firstError
    let second := pbsRecursiveDepth secondNoise secondCuts E M secondFallback payoff bound
      secondBelief secondError
    |(firstBelief.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom first firstCuts.sum)).expect
        (payoff who) -
      (secondBelief.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom second secondCuts.sum)).expect
        (payoff who)| ≤ firstError + secondError + rootError := by
  intro first second
  have firstNash := @pbsRecursiveDepth_isNash.{u} firstNoise firstNoiseBound firstCuts E M
    inferInstance inferInstance firstFallback payoff zeroSum bound nonneg bounded
    firstObs firstBelief firstError firstPositive
  have secondNash := @pbsRecursiveDepth_isNash.{u} secondNoise secondNoiseBound secondCuts E M
    inferInstance inferInstance secondFallback payoff zeroSum bound nonneg bounded
    secondObs secondBelief secondError secondPositive
  rw [← horizon] at secondNash
  have estimate := @behavioralNash_crossRoot_value_abs_le.{u} E
    (fullInformation.{0, u, u, u, u, u} M) firstObs secondObs firstBelief secondBelief
    first second who firstCuts.sum payoff zeroSum firstError secondError rootError
    firstNash secondNash roots
  simpa only [horizon] using estimate

/-- The actual root-law L1 discrepancy supplies the previous theorem's
uniform error, without a value-stability certificate from the caller. -/
theorem pbsRecursiveDepth_crossQuery_value_variation
    (firstNoise secondNoise : PBSRecursiveDepthNoise.{u})
    (firstNoiseBound : PBSRecursiveDepthNoiseBound firstNoise)
    (secondNoiseBound : PBSRecursiveDepthNoiseBound secondNoise)
    (firstCuts secondCuts : List Nat) (horizon : firstCuts.sum = secondCuts.sum)
    (firstFallback secondFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h p => payoff p h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    {firstObs secondObs : List M.PublicSignal}
    (firstBelief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals firstObs)
    (secondBelief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals secondObs)
    (firstError secondError : ℝ) (firstPositive : 0 < firstError)
    (secondPositive : 0 < secondError) (who : Fin 2) :
    let first := pbsRecursiveDepth firstNoise firstCuts E M firstFallback payoff bound
      firstBelief firstError
    let second := pbsRecursiveDepth secondNoise secondCuts E M secondFallback payoff bound
      secondBelief secondError
    |(firstBelief.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom first firstCuts.sum)).expect
        (payoff who) -
      (secondBelief.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom second secondCuts.sum)).expect
        (payoff who)| ≤ firstError + secondError +
      bound * FinDist.atomVariation firstBelief.law secondBelief.law := by
  exact pbsRecursiveDepth_crossQuery_value_error M firstNoise secondNoise firstNoiseBound
    secondNoiseBound firstCuts secondCuts horizon firstFallback secondFallback payoff zeroSum
    bound nonneg bounded firstBelief secondBelief firstError secondError firstPositive
    secondPositive who _ (fun profile =>
      @behavioralRoot_profile_error.{u} E (fullInformation.{0, u, u, u, u, u} M)
        inferInstance firstObs secondObs firstBelief secondBelief profile firstCuts.sum
        (payoff who) bound nonneg (bounded who))

/-- A fresh private solve secures the earlier computation's model value
after both root error and finite solve tolerances. This is a scalar model-root
comparison, not an equality of native posteriors or a full recursive rate. -/
theorem pbsRecursiveDepth_crossQuery_private_security
    (firstNoise secondNoise : PBSRecursiveDepthNoise.{u})
    (firstNoiseBound : PBSRecursiveDepthNoiseBound firstNoise)
    (secondNoiseBound : PBSRecursiveDepthNoiseBound secondNoise)
    (firstCuts secondCuts : List Nat) (horizon : firstCuts.sum = secondCuts.sum)
    (firstFallback secondFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h p => payoff p h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    {firstObs secondObs : List M.PublicSignal}
    (firstBelief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals firstObs)
    (secondBelief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals secondObs)
    (firstError secondError : ℝ) (firstPositive : 0 < firstError)
    (secondPositive : 0 < secondError) (who : Fin 2)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) :
    let first := pbsRecursiveDepth firstNoise firstCuts E M firstFallback payoff bound
      firstBelief firstError
    (firstBelief.law.bind
      ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom first firstCuts.sum)).expect
        (payoff who) -
      (firstError + 2 * secondError +
        bound * FinDist.atomVariation firstBelief.law secondBelief.law) ≤
    (pbsRecursiveDepthDraw secondNoise secondCuts M secondFallback payoff bound
      secondBelief secondError).expect (fun chosen =>
        (secondBelief.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) secondCuts.sum)).expect (payoff who)) := by
  intro first
  have comparison := pbsRecursiveDepth_crossQuery_value_variation M firstNoise secondNoise
    firstNoiseBound secondNoiseBound firstCuts secondCuts horizon firstFallback secondFallback
    payoff zeroSum bound nonneg bounded firstBelief secondBelief firstError secondError
    firstPositive secondPositive who
  have security := pbsRecursiveDepth_private_model_security M secondNoise secondNoiseBound
    secondCuts secondFallback payoff zeroSum bound nonneg bounded secondBelief secondError
    secondPositive unknown who
  dsimp only at comparison security
  have upper := (abs_le.mp comparison).2
  linarith only [upper, security]

end GameTheory.ReBeL
