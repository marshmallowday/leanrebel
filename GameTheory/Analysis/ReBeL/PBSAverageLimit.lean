/-
# Later-average guarantees in the original public-belief game

The fixed noisy or recursively composed parent is decoded at every later
iteration count. Administrative root fuel, prediction error and child tolerance
stay explicit. This changes the averaging horizon, not the trained oracle.
-/

import GameTheory.Analysis.ReBeL.CFRDAverageLimit
import GameTheory.Analysis.ReBeL.PBSRecursiveDepth

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

section Rooted

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (roots : FinDist E.History)

/-- The same rooted history enumeration is used by all later parent averages. -/
local instance averageLimitHistory : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

/-- Equality is confined to the real-valued reference implementation. -/
local instance averageLimitInfo (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

/-- Finite legal menus are inherited from the original action carriers. -/
local instance averageLimitChoice (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- More parent iterations bound the finite term while retaining both sources
of nonzero error. This is an all-later-count statement. -/
theorem pbsRootDepthBudget_after (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) (bound error loss epsilon : ℝ)
    (he : 0 ≤ error) (positive : 0 < epsilon) (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (pbsRootDepthFiniteFactor M roots fallback cut remaining bound) epsilon ≤ t) :
    pbsRootDepthBudget M roots fallback cut remaining bound error loss t ≤
      pbsRootDepthErrorFactor M roots fallback cut remaining * error + 2 * loss + epsilon := by
  have finite := pbsRootDepthBudget_le_factors M roots fallback cut remaining
    bound error loss he t
  have rate := cfrDAverageRate_after
    (pbsRootDepthFiniteFactor M roots fallback cut remaining bound) epsilon positive t large
  linarith only [finite, rate]

variable {observations : List M.PublicSignal}

/-- The constructed finite-child noisy solver covers all original-game
behavioral deviations at every count beyond the explicit threshold. -/
theorem pbsInformationDepthAverage_after
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss epsilon : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hl : 0 < loss) (positive : 0 < epsilon)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (noise : PBSRootDepthNoise M belief.law)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (pbsRootDepthFiniteFactor M belief.law fallback cut remaining bound) epsilon ≤ t) :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin
        (pbsRootDepthErrorFactor M belief.law fallback cut remaining * error +
          2 * loss + epsilon) (fun h who => payoff who h))
      (pbsInformationDepthCFR M belief fallback payoff cut remaining bound loss noise t) := by
  have finite := pbsInformationDepthCFR_isNash M belief fallback payoff zeroSum
    cut remaining bound error loss hb he hl bounded noise noiseBound t
  have budget := pbsRootDepthBudget_after M belief.law fallback cut remaining
    bound error loss epsilon he positive t large
  rw [isNash_iff] at finite ⊢
  intro who replacement
  have gain := finite who replacement
  rw [euPreferenceWithin_apply] at gain ⊢
  exact gain.trans (add_le_add_left budget _)

/-- A fixed composed child computation also admits the all-later-count bound.
Its accuracy is a local smaller-solver premise, not the conclusion being proved. -/
theorem pbsComposedDepthAverage_after
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss epsilon : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hl : 0 < loss) (positive : 0 < epsilon)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (solve : PBSChildSolve (pbsRootInformation (fullInformation M) belief.law))
    (smaller : PBSChildSolveAccurate (pbsRootInformation (fullInformation M) belief.law) solve
      (fun h who => pbsRootPayoff belief.law payoff who h) remaining)
    (noise : PBSRootDepthNoise M belief.law)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (pbsRootDepthFiniteFactor M belief.law fallback cut remaining bound) epsilon ≤ t) :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin
        (pbsRootDepthErrorFactor M belief.law fallback cut remaining * error +
          2 * loss + epsilon) (fun h who => payoff who h))
      (pbsRootDecodeProfile M belief.law (observations.length - 1)
        (pbsComposedDepthAverage M belief.law fallback payoff
          cut remaining loss solve noise t)) := by
  have finite : IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin (pbsRootDepthBudget M belief.law fallback
        cut remaining bound error loss t) (fun h who => payoff who h))
      (pbsRootDecodeProfile M belief.law (observations.length - 1)
        (pbsComposedDepthAverage M belief.law fallback payoff
          cut remaining loss solve noise t)) := by
    apply pbsRootDecodeProfile_isNash
    rw [show cut + remaining + 1 = cut + 1 + remaining by omega]
    exact pbsComposedDepthAverage_isNash M belief.law fallback payoff zeroSum
      cut remaining bound error loss hb he hl bounded solve smaller noise noiseBound t
  have budget := pbsRootDepthBudget_after M belief.law fallback cut remaining
    bound error loss epsilon he positive t large
  rw [isNash_iff] at finite ⊢
  intro who replacement
  have gain := finite who replacement
  rw [euPreferenceWithin_apply] at gain ⊢
  exact gain.trans (add_le_add_left budget _)

end Rooted

section Recursive

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
variable (bound : ℝ) {observations : List M.PublicSignal}
variable (belief : PublicBelief (fullInformation M).toInfoSignals observations)

/-- Vary only the outer averaging count of the existing recursive parent.
The recursive tail, its positive budgets and the noisy infinite trace are fixed. -/
def pbsRecursiveParentAverage (noise : PBSRecursiveDepthNoise.{u})
    (cut : Nat) (tail : List Nat) (tolerance : ℝ) (t : Nat) [NeZero t] :
    Profile (fullInformation M).behavioralSignature := by
  letI : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
  let error := pbsDepthAllocationError
    (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance
  exact pbsRootDecodeProfile M belief.law (observations.length - 1)
    (pbsComposedDepthAverage M belief.law fallback payoff cut tail.sum (tolerance / 8)
      (pbsRecursiveDepth noise tail (pbsRootProtocol belief.law)
        (pbsRootInformation (fullInformation M) belief.law)
        (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff) bound)
      (noise E M belief.law error) t)

/-- At the existing allocated count this is definitionally the original solver. -/
theorem pbsRecursiveParentAverage_allocated (noise : PBSRecursiveDepthNoise.{u})
    (cut : Nat) (tail : List Nat) (tolerance : ℝ) :
    pbsRecursiveParentAverage M fallback payoff bound belief noise cut tail tolerance
        (pbsRootDepthBudgetRounds M belief.law fallback cut tail.sum bound
          (pbsDepthAllocationError
            (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance)
          (tolerance / 8) tolerance) =
      pbsRecursiveDepth noise (cut :: tail) E M fallback payoff bound belief tolerance := rfl

/-- All smaller-solver premises are discharged by the existing structural
induction. The residual floor still contains fixed noise and child tolerance;
only the outer finite-time remainder vanishes as t grows. -/
theorem pbsRecursiveParentAverage_after (noise : PBSRecursiveDepthNoise.{u})
    (noiseBound : PBSRecursiveDepthNoiseBound noise) (cut : Nat) (tail : List Nat)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (hb : 0 ≤ bound)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (tolerance epsilon : ℝ) (htol : 0 < tolerance) (positive : 0 < epsilon)
    (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (pbsRootDepthFiniteFactor M belief.law fallback cut tail.sum bound) epsilon ≤ t) :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + tail.sum))
      (euPreferenceWithin
        (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum *
            pbsDepthAllocationError
              (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance +
          2 * (tolerance / 8) + epsilon) (fun h who => payoff who h))
      (pbsRecursiveParentAverage M fallback payoff bound belief noise cut tail tolerance t) := by
  let _ : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
  apply pbsComposedDepthAverage_after M belief fallback payoff zeroSum cut tail.sum
    bound _ _ epsilon hb (pbsDepthAllocationError_pos _ tolerance htol).le
    (div_pos htol (by norm_num)) positive bounded
  · intro childObs child target childPositive
    exact pbsRecursiveDepth_isNash noise noiseBound tail
      (pbsRootInformation (fullInformation M) belief.law)
      (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
      (pbsRootPayoff_zeroSum belief.law payoff zeroSum) bound hb
      (fun who => pbsRootPayoff_abs_le belief.law payoff who bound hb (bounded who))
      child target childPositive
  · exact noiseBound M belief.law _ (pbsDepthAllocationError_pos _ tolerance htol).le
  · exact large

end Recursive

end GameTheory.ReBeL
