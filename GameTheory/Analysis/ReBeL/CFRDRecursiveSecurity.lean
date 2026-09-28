/-
# Finite parent error through the native fresh recursive chain

Source: ReBeL pp.21-22 retains a CFR term independent of value error; the
printed Theorem 3 instead multiplies that term by delta. We formalize the
separated interpretation, with child loss and native replacement costs visible.
This is a restricted finite-time security theorem, not full Theorem 3 acceptance.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationSampledDriver
import GameTheory.Analysis.ReBeL.CFRDAverageLimit
import GameTheory.Analysis.ReBeL.PBSRecursiveNashBudget

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation.{0, u, u, u, u, u} M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation.{0, u, u, u, u, u} M).InfoState who)]

/-- The initial bound comes from the actual noisy finite-child parent, not a
supplied security premise. Every later stage uses native private memory and
saved PBSs. Numerical error, finite outer iterations, child loss and signed
recomputation/support costs remain separate, including at zero prediction error. -/
theorem cfrDRecursiveRecomputed_security
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (cut finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ player h, |payoff player h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk player info, |noise n trunk player info| ≤ error)
    (reference : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation.{0, u, u, u, u, u} M).toBehavioralGameForm
      (cut + pbsRecursiveConfigFuel finalFuel configs))
      (euPreference (fun h player => payoff player h)) reference)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) (t : Nat) [NeZero t] :
    let remaining := pbsRecursiveConfigFuel finalFuel configs
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation.{0, u, u, u, u, u} M)
      (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
        bound loss noise) n.val
    ((fullInformation.{0, u, u, u, u, u} M).runBehavioral reference
      (cut + remaining)).expect (payoff who) -
      (cfrDDepthAverageErrorFloor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining error loss +
        cfrDDepthAverageFiniteFactor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining bound / Real.sqrt t +
        pbsRecursiveRecomputedBudget M fallback payoff bound plays unknown who finalFuel
          (payoff who) bound configs
          ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
            (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M)))) ≤
      (privateRecursiveResolve (fullInformation.{0, u, u, u, u, u} M)
        (cfrIterationLaw t) plays unknown who cut finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays))).expect
          (payoff who) := by
  intro remaining plays
  have initial := cfrDConstructedSampledInformationOracle_carried_security M fallback payoff
    zeroSum cut remaining bound error loss hb he hl bounded noise noiseBound
    reference equilibrium unknown who t
  have inherited := privateRecursiveResolve_inherits_recomputedBudget M fallback payoff bound
    (cfrIterationLaw t) plays unknown who cut finalFuel configs (payoff who) bound (bounded who)
    (((fullInformation.{0, u, u, u, u, u} M).runBehavioral reference
      (cut + remaining)).expect (payoff who) -
      (cfrDDepthAverageErrorFloor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining error loss +
        cfrDDepthAverageFiniteFactor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining bound / Real.sqrt t))
    (by
      rw [carriedResolveFuel_config_eq M fallback payoff bound plays finalFuel configs]
      dsimp only [cfrDDepthAverageErrorFloor, cfrDDepthAverageFiniteFactor]
      linarith only [initial])
  simpa only [sub_add_eq_sub_sub] using inherited

/-- Horizon-aligned actual recursive solvers replace the signed recomputation
term by their solver-derived Nash envelope. Actual root/opponent discrepancies
and unsupported-state mass remain charged; no general small-rate claim follows. -/
theorem cfrDRecursiveNash_security
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (cut finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ player h, |payoff player h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk player info, |noise n trunk player info| ≤ error)
    (reference : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation.{0, u, u, u, u, u} M).toBehavioralGameForm
      (cut + pbsRecursiveConfigFuel finalFuel configs))
      (euPreference (fun h player => payoff player h)) reference)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) (t : Nat) [NeZero t]
    (aligned : PBSRecursiveNashAligned finalFuel configs) :
    let remaining := pbsRecursiveConfigFuel finalFuel configs
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation.{0, u, u, u, u, u} M)
      (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
        bound loss noise) n.val
    ((fullInformation.{0, u, u, u, u, u} M).runBehavioral reference
      (cut + remaining)).expect (payoff who) -
      (cfrDDepthAverageErrorFloor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining error loss +
        cfrDDepthAverageFiniteFactor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining bound / Real.sqrt t +
        pbsRecursiveNashBudget M fallback payoff bound plays unknown who finalFuel configs
          ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
            (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M)))) ≤
      (privateRecursiveResolve (fullInformation.{0, u, u, u, u, u} M)
        (cfrIterationLaw t) plays unknown who cut finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays))).expect
          (payoff who) := by
  intro remaining plays
  have security := cfrDRecursiveRecomputed_security M fallback payoff zeroSum cut finalFuel
    configs bound error loss hb he hl bounded noise noiseBound reference equilibrium unknown who t
  have budget := pbsRecursiveRecomputedBudget_le_nashBudget M fallback payoff zeroSum
    bound hb bounded plays unknown who finalFuel configs aligned
    ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
      (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M)))
  dsimp only at security
  linarith only [security, budget]

omit [∀ who, Fintype (E.Action who)]
    [∀ who, DecidableEq ((fullInformation.{0, u, u, u, u, u} M).InfoState who)] in
/-- Exact numerical predictions leave finite parent regret AND child loss.
This is an identity of allowances, not a claim that actual error attains them. -/
theorem cfrDRecursive_zero_prediction_allowance
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (bound loss : ℝ) (t : Nat) :
    cfrDDepthAverageErrorFloor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) cut remaining 0 loss +
      cfrDDepthAverageFiniteFactor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) cut remaining bound / Real.sqrt t =
    cfrDDepthAverageFiniteFactor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) cut remaining bound / Real.sqrt t + 2 * loss := by
  simp only [cfrDDepthAverageErrorFloor, mul_zero, zero_add, add_comm]

end GameTheory.ReBeL
