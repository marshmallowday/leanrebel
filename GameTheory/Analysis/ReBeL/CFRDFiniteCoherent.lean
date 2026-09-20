/-
# Deferred private realization of the actual finite-child CFR-D trace

The resolver recomputes the SAME finite construction indexed by its retained
parent iteration, then draws legal pure plans. It does not choose a new Nash
equilibrium. Numerical error, positive finite-child loss and outer finite
regret remain distinct; no switching penalty or local envelope is assumed.
This is an execution refinement, not independent recursive re-solving.
-/

import GameTheory.Analysis.ReBeL.CFRDCoherentDraw
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

/-- The sampled family is computed from this very perturbed outer recurrence,
including the posterior-budgeted finite children and off-path completion. -/
def cfrDFiniteCoherentResolver (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) (t : Nat) : CarriedPublicResolver (fullInformation M) (Fin t) :=
  cfrDCoherentResolver (fullInformation M) fallback (fun n : Fin t =>
    cfrDDepthPlay (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
      (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) n.val)

/-- Freshly drawn plans have the full retained-parent history law against any
unknown opponent, with no payoff, Nash, reference-support or accuracy premise. -/
theorem cfrDFiniteCoherentResolver_law
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) (unknown : Profile (fullInformation M).behavioralSignature)
    (who : Fin 2) (t : Nat) [NeZero t] :
    privateCarriedResolve (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          fallback payoff cut remaining
          (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) n.val)
        (cfrDFiniteCoherentResolver M fallback payoff cut remaining bound loss noise t)
        unknown who cut remaining =
      privateCarriedContinue (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          fallback payoff cut remaining
          (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) n.val)
        unknown who cut remaining :=
  cfrDCoherentResolver_resolve_eq (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback _ _ unknown who cut remaining

/-- The counterfactual opponent envelope is now derived for a nontrivial
sampled resolver of the constructed finite solver, not assumed as a certificate. -/
theorem cfrDFiniteCoherentResolver_envelope
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (unknown : Profile (fullInformation M).behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (t : Nat) :
    CFRDResolverEnvelope (fullInformation M)
      (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
        fallback payoff cut remaining
        (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) n.val)
      (cfrDFiniteCoherentResolver M fallback payoff cut remaining bound loss noise t)
      fallback unknown who opponent cut remaining (payoff opponent) loss := by
  apply cfrDCoherentResolver_envelope (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback _ unknown who opponent different
  intro n
  exact cfrDConstructedFiniteOracle_leafOptimal M fallback payoff zeroSum cut remaining
    bound loss nonneg positive bounded noise n.val opponent

/-- The real private-plan execution inherits the finite-child driver's bound
without a switch probability or any additional replacement penalty. Only the
comparison equilibrium naming the original game value is supplied. -/
theorem cfrDFiniteCoherentResolver_security
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    ((fullInformation M).runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining 0 +
          cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining 1) * error +
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 1) / Real.sqrt t + 2 * loss) ≤
      (privateCarriedResolve (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          fallback payoff cut remaining
          (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) n.val)
        (cfrDFiniteCoherentResolver M fallback payoff cut remaining bound loss noise t)
        unknown who cut remaining).expect (payoff who) := by
  rw [cfrDFiniteCoherentResolver_law]
  exact cfrDConstructedFiniteOracle_carried_security M fallback payoff zeroSum cut remaining
    bound error loss hb he hl bounded noise noiseBound reference equilibrium unknown who t

end GameTheory.ReBeL
