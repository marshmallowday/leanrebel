/-
# A budgeted CFR-D parent for a smaller computational child

The child is selected by the current parent's factual joint PBS. Its accuracy
is a separate induction premise, transferred through the existing public splice
and zero-own-reach completion. This parent allocates a finite positive number
of rounds and decodes all behavioral deviations back to the original PBS.
-/

import GameTheory.Analysis.ReBeL.CFRDComposedChild
import GameTheory.Analysis.ReBeL.CFRDInformationDriver
import GameTheory.Analysis.ReBeL.PBSInformationDepthBudget

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

section Parent

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- Recompute the child from this iteration's trunk, then perturb its own values. -/
def cfrDComposedOracle (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (noise : CFRDPredictionNoise M) :
    CFRDValueOracle (fullInformation M) := fun n trunk =>
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut remaining
    (fun _ strategy => cfrDComposedChildContinuation M strategy fallback cut remaining loss
      solve (fun h who => payoff who h)) n trunk
  { continuation := response.continuation
    prediction := fun who info => response.prediction who info + noise n trunk who info }

/-- Accuracy is evaluated along the actual perturbed parent recurrence. -/
theorem cfrDComposedOracle_accurate (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (noise : CFRDPredictionNoise M) (error : ℝ)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error) :
    CFRDDepthAccurate (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDComposedOracle M fallback payoff cut remaining loss solve noise) error := by
  intro n who info _sampled
  let oracle := cfrDComposedOracle M fallback payoff cut remaining loss solve noise
  let trunk := cfrProfile (fullInformation M) (cfrDInformationFallback M fallback)
    (cfrDState (fullInformation M)
      (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
      (cfrDInformationFallback M fallback)
      (cfrDDepthOracle (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining oracle) n)
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut remaining
    (fun _ strategy => cfrDComposedChildContinuation M strategy fallback cut remaining loss
      solve (fun h player => payoff player h)) n trunk
  have residual : |response.prediction who info + noise n trunk who info -
      response.prediction who info| ≤ error := by
    simpa only [add_sub_cancel_left] using noiseBound n trunk who info
  exact residual

/-- The induction premise supplies all live queries, including zero-own-reach types. -/
theorem cfrDComposedOracle_leafOptimal (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (loss : ℝ)
    (positive : 0 < loss) (solve : PBSChildSolve M)
    (smaller : PBSChildSolveAccurate M solve (fun h who => payoff who h) remaining)
    (noise : CFRDPredictionNoise M) :
    CFRDDepthLeafOptimal (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDComposedOracle M fallback payoff cut remaining loss solve noise) loss := by
  intro n who
  rw [cfrDDepthPlay_eq]
  apply cfrDDepthProfile_leafOptimal
  · exact cfrDComposedChildContinuation_referenceLaw M _ fallback cut remaining loss
      solve (fun h player => payoff player h) who
  · exact cfrDComposedChildContinuation_leafOptimal M _ fallback cut remaining loss positive
      solve (fun h player => payoff player h) smaller who

/-- A genuine coupled parent inherits finite-time Nash from a smaller computation. -/
theorem cfrDComposedOracle_isNash (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (solve : PBSChildSolve M)
    (smaller : PBSChildSolveAccurate M solve (fun h who => payoff who h) remaining)
    (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] :
    IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreferenceWithin
        (cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound error loss 0 t +
          cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound error loss 1 t)
        (fun h who => payoff who h))
      (cfrDDepthAveragedProfile (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining
        (cfrDComposedOracle M fallback payoff cut remaining loss solve noise) t) :=
  cfrDDepthAveragedProfile_isNash (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) (cfrDInformationFallback M fallback)
    payoff zeroSum cut remaining (cfrDComposedOracle M fallback payoff cut remaining loss
      solve noise) bound error loss hb he hl.le bounded
    (cfrDComposedOracle_accurate M fallback payoff cut remaining loss solve noise error noiseBound)
    (cfrDComposedOracle_leafOptimal M fallback payoff cut remaining loss hl solve smaller noise) t

end Parent

section Rooted

variable (roots : FinDist E.History)

/-- Retain the canonical finite enumeration of rooted histories. -/
local instance composedHistoryFintype : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

/-- Equality is used only in this real-valued reference construction. -/
local instance composedInfoDecidableEq (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

/-- Rooted local menus inherit the original finite action carriers. -/
local instance composedChoiceFintype (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- The same private own-reach average, now with the compositional child. -/
def pbsComposedDepthAverage (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve (pbsRootInformation (fullInformation M) roots))
    (noise : PBSRootDepthNoise M roots) (t : Nat) [NeZero t] :
    Profile (pbsRootFullInformation M roots).behavioralSignature :=
  cfrDDepthAveragedProfile (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
    (cfrDComposedOracle (pbsRootInformation (fullInformation M) roots)
      (pbsRootDepthFallback M roots fallback) (pbsRootPayoff roots payoff)
      (cut + 1) remaining loss solve noise) t

/-- One root chance step is administrative, not an original cut transition. -/
theorem pbsComposedDepthAverage_isNash (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (solve : PBSChildSolve (pbsRootInformation (fullInformation M) roots))
    (smaller : PBSChildSolveAccurate (pbsRootInformation (fullInformation M) roots) solve
      (fun h who => pbsRootPayoff roots payoff who h) remaining)
    (noise : PBSRootDepthNoise M roots)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] :
    IsNash ((pbsRootFullInformation M roots).toBehavioralGameForm (cut + 1 + remaining))
      (euPreferenceWithin (pbsRootDepthBudget M roots fallback cut remaining bound error loss t)
        (fun h who => pbsRootPayoff roots payoff who h))
      (pbsComposedDepthAverage M roots fallback payoff cut remaining loss solve noise t) :=
  cfrDComposedOracle_isNash (pbsRootInformation (fullInformation M) roots)
    (pbsRootDepthFallback M roots fallback) (pbsRootPayoff roots payoff)
    (pbsRootPayoff_zeroSum roots payoff zeroSum) (cut + 1) remaining bound error loss hb he hl
    (fun who => pbsRootPayoff_abs_le roots payoff who bound hb (bounded who))
    solve smaller noise noiseBound t

variable {observations : List M.PublicSignal}

/-- A finite budget is computed before decoding the resulting original local policy. -/
def pbsComposedDepthProfile
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound error loss tolerance : ℝ)
    (solve : PBSChildSolve (pbsRootInformation (fullInformation M) belief.law))
    (noise : PBSRootDepthNoise M belief.law) :
    Profile (fullInformation M).behavioralSignature :=
  pbsRootDecodeProfile M belief.law (observations.length - 1)
    (pbsComposedDepthAverage M belief.law fallback payoff cut remaining loss solve noise
      (pbsRootDepthBudgetRounds M belief.law fallback cut remaining bound error loss tolerance))

/-- The requested accuracy follows from the finite allocation and the smaller
solver theorem, not from an accuracy certificate stored in the implementation. -/
theorem pbsComposedDepthProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss tolerance : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (feasible : pbsRootDepthErrorFactor M belief.law fallback cut remaining * error +
      2 * loss < tolerance)
    (solve : PBSChildSolve (pbsRootInformation (fullInformation M) belief.law))
    (smaller : PBSChildSolveAccurate (pbsRootInformation (fullInformation M) belief.law) solve
      (fun h who => pbsRootPayoff belief.law payoff who h) remaining)
    (noise : PBSRootDepthNoise M belief.law)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error) :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin tolerance (fun h who => payoff who h))
      (pbsComposedDepthProfile M belief fallback payoff cut remaining bound error loss tolerance
        solve noise) := by
  let t := pbsRootDepthBudgetRounds M belief.law fallback cut remaining bound error loss tolerance
  have precise : IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin (pbsRootDepthBudget M belief.law fallback cut remaining
        bound error loss t) (fun h who => payoff who h))
      (pbsComposedDepthProfile M belief fallback payoff cut remaining bound error loss tolerance
        solve noise) := by
    apply pbsRootDecodeProfile_isNash
    have horizon : cut + 1 + remaining = cut + remaining + 1 := by omega
    rw [← horizon]
    exact pbsComposedDepthAverage_isNash M belief.law fallback payoff zeroSum cut remaining
      bound error loss hb he hl bounded solve smaller noise noiseBound t
  rw [isNash_iff] at precise ⊢
  intro who replacement
  have gain := precise who replacement
  rw [euPreferenceWithin_apply] at gain ⊢
  exact gain.trans (add_le_add (le_refl _)
    (pbsRootDepthBudgetRounds_error M belief.law fallback cut remaining bound error loss
      tolerance he feasible))

end Rooted

end GameTheory.ReBeL
