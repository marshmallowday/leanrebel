/-
# Finite-parent security with actual fresh-query payoff diameter

Initial security is derived from the finite noisy sampled parent. The second
cap charges actual native query visits, including unsupported queries. It
does not need a model/factual posterior identity or small opponent transport.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveQueryCost

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

/-- The actual sampled parent supplies initial security; no initial-value or
child Nash certificate is assumed. The added cost is payoff diameter times
the expected count of actual queries, independent of solver alignment. -/
theorem cfrDRecursiveQuery_security
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
    (lower upper : ℝ) (lowerBound : ∀ h, lower ≤ payoff who h)
    (upperBound : ∀ h, payoff who h ≤ upper) :
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
        (upper - lower) * pbsRecursiveQueryVisits M fallback payoff bound plays unknown who
          configs
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
  have inherited := privateRecursiveResolve_inherits_queryVisits M fallback payoff bound
    (cfrIterationLaw t) plays unknown who cut finalFuel configs (payoff who) lower upper
    lowerBound upperBound
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


/-- Both derived guarantees concern the same actual execution. Select the
smaller complete-chain charge; support terms remain inside the grouped cap,
while the diameter cap covers all actual queries without a support premise. -/
theorem cfrDRecursiveQuery_capped_security
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
    (aligned : PBSRecursiveNashAligned finalFuel configs)
    (lower upper : ℝ) (lowerBound : ∀ h, lower ≤ payoff who h)
    (upperBound : ∀ h, payoff who h ≤ upper) :
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
        min (pbsRecursiveGroupedBudget M fallback payoff bound plays unknown who finalFuel configs
          ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
            (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M))))
          ((upper - lower) * pbsRecursiveQueryVisits M fallback payoff bound plays unknown who
          configs ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
            (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M))))) ≤
      (privateRecursiveResolve (fullInformation.{0, u, u, u, u, u} M)
        (cfrIterationLaw t) plays unknown who cut finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays))).expect
          (payoff who) := by
  intro remaining plays
  have grouped := cfrDRecursiveGrouped_security M fallback payoff zeroSum cut finalFuel
    configs bound error loss hb he hl bounded noise noiseBound reference equilibrium unknown
    who t aligned
  have queried := cfrDRecursiveQuery_security M fallback payoff zeroSum cut finalFuel
    configs bound error loss hb he hl bounded noise noiseBound reference equilibrium unknown
    who t lower upper lowerBound upperBound
  dsimp only at grouped queried
  rcases le_total
      (pbsRecursiveGroupedBudget M fallback payoff bound plays unknown who finalFuel configs
          ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
            (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M))))
      ((upper - lower) * pbsRecursiveQueryVisits M fallback payoff bound plays unknown who
          configs ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
            (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M)))) with smaller | smaller
  · rw [min_eq_left smaller]
    exact grouped
  · rw [min_eq_right smaller]
    exact queried

end GameTheory.ReBeL
