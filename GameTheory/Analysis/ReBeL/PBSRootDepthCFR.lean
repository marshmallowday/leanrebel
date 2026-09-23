/-
# Constructed noisy depth-limited CFR-D at a joint-PBS root

The canonical chance-root adapter runs the actual coupled parent recurrence
with computed information-set children and counterfactual zero-reach completion.
The administrative root costs one transition; cut and remaining count original
transitions. No child equilibrium or local optimality certificate is an input.
The deepest child backend here is still full-root CFR, not arbitrary-depth recursion.
-/

import GameTheory.Analysis.ReBeL.PBSInformationSampling
import GameTheory.Analysis.ReBeL.CFRDInformationSampledDriver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- A legal fallback for the reduced rooted model, before its full-AOH adapter. -/
def pbsRootDepthFallback (roots : FinDist E.History)
    (fallback : Profile M.strategicSignature) :
    Profile (pbsRootInformation (fullInformation M) roots).strategicSignature :=
  fun who => pbsRootPolicy (fullInformation M) roots who (liftPolicy M who (fallback who))

/-- Prediction perturbations may read the modeled rooted query, never the
actual hidden input history or the unknown opponent used during execution. -/
abbrev PBSRootDepthNoise (roots : FinDist E.History) :=
  CFRDPredictionNoise (pbsRootInformation (fullInformation M) roots)

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (roots : FinDist E.History)

/-- Rooted histories are finite by the previously proved strict-rank construction. -/
local instance rootDepthHistoryFintype : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

/-- Classical equality is confined to the real-valued reference solver. -/
local instance rootDepthInfoDecidableEq (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

/-- Local action carriers inherit the original finite action options. -/
local instance rootDepthChoiceFintype (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- Completed child sampling expectations, with the supplied numerical noise,
are fed to the current rooted parent's actual regret update at every round. -/
def pbsRootDepthOracle (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) : CFRDValueOracle (pbsRootFullInformation M roots) :=
  cfrDConstructedSampledInformationOracle (pbsRootInformation (fullInformation M) roots)
    (pbsRootDepthFallback M roots fallback) (pbsRootPayoff roots payoff)
    (cut + 1) remaining bound loss noise

/-- One actual coupled depth-limited iteration, including its computed
continuation. It is not an independently supplied strategy sequence. -/
def pbsRootDepthIterate (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (round : Nat) :
    Profile (pbsRootFullInformation M roots).behavioralSignature :=
  cfrDDepthPlay (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
    (pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise) round

/-- Independent own-reach averages of the same finite coupled iteration family. -/
def pbsRootDepthAverage (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (t : Nat) [NeZero t] :
    Profile (pbsRootFullInformation M roots).behavioralSignature :=
  cfrDDepthAveragedProfile (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
    (pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise) t

/-- Numerical error, positive child tolerance and finite outer iterations
remain separate in the original depth-limited regret budgets. -/
def pbsRootDepthBudget (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) (bound error loss : ℝ) (t : Nat) : ℝ :=
  cfrDDepthMeanBudget (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining bound error loss 0 t +
  cfrDDepthMeanBudget (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining bound error loss 1 t

/-- The root's sampled-value oracle agrees for every queried trunk, not just
along a previously selected unperturbed learning trace. -/
theorem pbsRootDepthOracle_eq (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) :
    pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise =
      cfrDConstructedInformationOracle (pbsRootInformation (fullInformation M) roots)
        (pbsRootDepthFallback M roots fallback) (pbsRootPayoff roots payoff)
        (cut + 1) remaining bound loss noise :=
  cfrDConstructedSampledInformationOracle_eq _ _ _ _ _ _ _ _

/-- All rooted behavioral deviations are bounded by the constructed noisy
parent and its computed children. Positive leaf loss is retained explicitly. -/
theorem pbsRootDepthAverage_isNash (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history who => payoff who history)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (noise : PBSRootDepthNoise M roots)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] :
    IsNash ((pbsRootFullInformation M roots).toBehavioralGameForm (cut + 1 + remaining))
      (euPreferenceWithin (pbsRootDepthBudget M roots fallback cut remaining bound error loss t)
        (fun history who => pbsRootPayoff roots payoff who history))
      (pbsRootDepthAverage M roots fallback payoff cut remaining bound loss noise t) := by
  unfold pbsRootDepthAverage
  rw [pbsRootDepthOracle_eq]
  exact cfrDConstructedInformationOracle_isNash
    (pbsRootInformation (fullInformation M) roots) (pbsRootDepthFallback M roots fallback)
    (pbsRootPayoff roots payoff) (pbsRootPayoff_zeroSum roots payoff zeroSum)
    (cut + 1) remaining bound error loss hb he hl
    (fun who => pbsRootPayoff_abs_le roots payoff who bound hb (bounded who)) noise noiseBound t

/-- Uniformly drawing an actual depth-limited iteration realizes its own-reach
average against each fixed seed-blind opponent. Execution and training fuel
need not coincide. No per-iterate Nash or prediction-accuracy premise is used. -/
theorem pbsRootDepthAverage_uniform_law (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (t : Nat) [NeZero t]
    (unknown : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (who : Fin 2) (steps : Nat) :
    (pbsRootFullInformation M roots).runBehavioral
      (Profile.update unknown who
        (pbsRootDepthAverage M roots fallback payoff cut remaining bound loss noise t who))
      (steps + 1) =
      (cfrIterationLaw t).bind (fun n => (pbsRootFullInformation M roots).runBehavioral
        (Profile.update unknown who
          (pbsRootDepthIterate M roots fallback payoff cut remaining bound loss noise n.val who))
        (steps + 1)) := by
  exact run_unilateral_average (pbsRootFullInformation M roots)
    (fullSignals_perfectRecall (pbsRootInformation (fullInformation M) roots).toInfoSignals)
    (fun _ => cfrIterationLaw t)
    (fun n : Fin t => pbsRootDepthIterate M roots fallback payoff cut remaining bound loss
      noise n.val) (pbsRootFallback M roots fallback) unknown who (steps + 1)

end GameTheory.ReBeL
