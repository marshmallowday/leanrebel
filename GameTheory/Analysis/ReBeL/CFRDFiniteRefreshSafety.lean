/-
# Constructed finite-child CFR-D followed by fresh bounded public re-solving

The initial security bound is supplied by the actual noisy outer recurrence
with finite-budget children. Every later candidate is computed from its
carried PBS. No local replacement comparison or recursive-value certificate
is assumed. A separate explicit refresh penalty is paid for the finite chain.
-/

import GameTheory.Analysis.ReBeL.CFRDFiniteRefresh
import GameTheory.Analysis.ReBeL.CFRDFiniteDriver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The finite noisy driver and freshly refreshed execution have numerical,
child, outer finite-time and refresh terms explicitly separated. The only
Nash premise names the original-game value, not any child or replacement. -/
theorem cfrDConstructedFiniteOracle_refreshed_security
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h))
    (cut finalFuel : Nat) (fuels : List Nat) (bound error loss rate : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (hr : 0 ≤ rate) (hr1 : rate ≤ 1) (bounded : ∀ who h, |payoff who h| ≤ bound)
    (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash
      ((fullInformation M).toBehavioralGameForm (cut + (fuels.sum + finalFuel)))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    let remaining := fuels.sum + finalFuel
    let oracle := cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      fallback payoff cut remaining oracle n.val
    ((fullInformation M).runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining 0 +
          cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining 1) * error +
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 1) / Real.sqrt t + 2 * loss) -
      (fuels.length : ℝ) * (2 * bound * rate) ≤
      (privateRecursiveResolve (fullInformation M) (cfrIterationLaw t) plays unknown who
        cut finalFuel (finiteRefreshStages (fullInformation M) plays (fullObservationClock M)
          fallback (fun h player => payoff player h) bound loss rate hr hr1 finalFuel fuels)).expect
        (payoff who) := by
  dsimp only
  apply finiteRefresh_inherits_bound (fullInformation M) (cfrIterationLaw t) _
    (fullObservationClock M) fallback (fun h player => payoff player h) bound loss rate hr hr1
    unknown who cut finalFuel fuels hb (bounded who)
  exact cfrDConstructedFiniteOracle_carried_security M fallback payoff zeroSum cut
    (fuels.sum + finalFuel) bound error loss hb he hl bounded noise noiseBound
    reference equilibrium unknown who t

end GameTheory.ReBeL
