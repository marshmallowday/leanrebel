/-
# Root training vectors for a composed CFR-D parent

The backup and original-game comparator use the very same composed oracle.
The child computation need not be Nash for numerical target propagation.
Accuracy of the returned policy remains a separate finite-budget theorem.
-/

import GameTheory.Analysis.ReBeL.CFRDValueTargetMemory
import GameTheory.Analysis.ReBeL.PBSComposedDepth

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}
variable (belief : PublicBelief (fullInformation M).toInfoSignals observations)

/-- Use the canonical rooted history carrier of the composed solver. -/
local instance composedTargetHistory : Fintype (pbsRootProtocol belief.law).History :=
  pbsRootHistoryFintype belief.law

/-- Reference computations use classical equality of local information states. -/
local instance composedTargetInfo (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M belief.law).InfoState who) := Classical.decEq _

/-- Local legal choices inherit the original finite action carriers. -/
local instance composedTargetChoice (who : Fin 2)
    (info : (pbsRootFullInformation M belief.law).InfoState who) :
    Fintype ((pbsRootFullInformation M belief.law).Choice who info) := by
  classical
  infer_instance

variable (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
variable (cut remaining : Nat) (loss : ℝ)
variable (solve : PBSChildSolve (pbsRootInformation (fullInformation M) belief.law))
variable (noise : PBSRootDepthNoise M belief.law)

/-- A backed-up vector from the actual composed round, not a second learning trace. -/
def pbsComposedValueTarget (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ :=
  cfrDDepthValueTarget (pbsRootFullInformation M belief.law)
    (fullObservationClock (pbsRootInformation (fullInformation M) belief.law))
    (pbsRootFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
    (cut + 1) remaining
    (cfrDComposedOracle (pbsRootInformation (fullInformation M) belief.law)
      (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
      (cut + 1) remaining loss solve noise) round who
    (pbsRootValueReadout M belief.law who) (some type)

/-- Proof-side value from the original correlated PBS and the decoded same
round. This full rollout is not part of the computed backed-up target. -/
def pbsComposedOriginalTarget (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ :=
  conditionalOracleValue belief.law (fun h => (fullInformation M).infoOf who h.trace)
    (fun h => ((fullInformation M).runBehavioralFrom
      (pbsRootDecodeProfile M belief.law (observations.length - 1)
        (pbsComposedDepthIterate M belief.law fallback payoff cut remaining
          loss solve noise round))
      (cut + remaining) h).expect (payoff who)) type

/-- The cut-conditional comparator is exactly the original-game continuation.
The administrative draw and all remaining transitions are retained. -/
theorem pbsComposedOriginalTarget_eq (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) :
    pbsComposedOriginalTarget M belief fallback payoff cut remaining loss solve noise
        round who type =
      cfrDDepthExactTarget (pbsRootFullInformation M belief.law)
        (fullObservationClock (pbsRootInformation (fullInformation M) belief.law))
        (pbsRootFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
        (cut + 1) remaining
        (cfrDComposedOracle (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
          (cut + 1) remaining loss solve noise) round who
        (pbsRootValueReadout M belief.law who) (some type) := by
  let profile := pbsComposedDepthIterate M belief.law fallback payoff
    cut remaining loss solve noise round
  have original := pbsRootValueReadout_original M belief.law (observations.length - 1)
    (pbsRoot_publicBelief_depth M belief) profile (cut + remaining) who type (payoff who)
  have payoffRead : pbsRootPayoff belief.law payoff who =
      (fun h : (pbsRootProtocol belief.law).History => h.state.elim 0 (payoff who)) := by
    funext h
    dsimp only [pbsRootPayoff]
    cases h.state <;> rfl
  have fullOriginal :
      conditionalOracleValue
          ((pbsRootFullInformation M belief.law).runBehavioral profile (cut + 1 + remaining))
          (fun h => pbsRootValueReadout M belief.law who
            ((pbsRootFullInformation M belief.law).infoOf who h.trace))
          (pbsRootPayoff belief.law payoff who) (some type) =
        pbsComposedOriginalTarget M belief fallback payoff cut remaining loss solve noise
          round who type := by
    rw [show cut + 1 + remaining = (cut + remaining) + 1 by omega, payoffRead]
    exact original
  exact fullOriginal.symm.trans
    (pbsRootValueReadout_tower M belief.law profile cut remaining who
      (some type) (pbsRootPayoff belief.law payoff who))

/-- Each own root coordinate consumes only the actual parent prediction error.
No child equilibrium, minimum reach or unknown-opponent law is assumed. -/
theorem pbsComposedValueTarget_error (error : ℝ) (nonneg : 0 ≤ error)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (round : Nat) (who : Fin 2) (type : (fullInformation M).InfoState who) :
    |pbsComposedValueTarget M belief fallback payoff cut remaining loss solve noise
        round who type -
      pbsComposedOriginalTarget M belief fallback payoff cut remaining loss solve noise
        round who type| ≤ error := by
  rw [pbsComposedOriginalTarget_eq]
  apply cfrDDepthValueTarget_error
  · exact fullSignals_perfectRecall
      (pbsRootInformation (fullInformation M) belief.law).toInfoSignals
  · exact nonneg
  · exact cfrDComposedOracle_accurate
      (pbsRootInformation (fullInformation M) belief.law)
      (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
      (cut + 1) remaining loss solve noise error noiseBound

/-- The training mask is the incoming own-type support, for every composed
round, even when the child changes its strategy or the run stops early. -/
theorem pbsComposedValueTarget_support (round : Nat) (who : Fin 2) :
    cfrDDepthValueTargetSupport (pbsRootFullInformation M belief.law)
        (fullObservationClock (pbsRootInformation (fullInformation M) belief.law))
        (pbsRootFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
        (cut + 1) remaining
        (cfrDComposedOracle (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
          (cut + 1) remaining loss solve noise) round who
        (pbsRootValueReadout M belief.law who) =
      (belief.law.map (fun h => some ((fullInformation M).infoOf who h.trace))).support :=
  congrArg FinDist.support
    (pbsRootValueReadout_law M belief.law (observations.length - 1)
      (pbsRoot_publicBelief_depth M belief)
      (pbsComposedDepthIterate M belief.law fallback payoff cut remaining loss solve noise round)
      cut who)

/-- Uniform averaging retains the same-round original-game meaning. Its
numerical bound is independent of the number of parent rounds. -/
theorem pbsComposedValueTargetMean_error (error : ℝ) (nonneg : 0 ≤ error)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] (who : Fin 2) (type : (fullInformation M).InfoState who) :
    |cfrDValueTargetMean
        (fun n => pbsComposedValueTarget M belief fallback payoff
          cut remaining loss solve noise n who) t type -
      cfrDValueTargetMean
        (fun n => pbsComposedOriginalTarget M belief fallback payoff
          cut remaining loss solve noise n who) t type| ≤ error := by
  apply cfrDValueTargetMean_error
  intro n _
  exact pbsComposedValueTarget_error M belief fallback payoff cut remaining
    loss solve noise error nonneg noiseBound n who type

end GameTheory.ReBeL
