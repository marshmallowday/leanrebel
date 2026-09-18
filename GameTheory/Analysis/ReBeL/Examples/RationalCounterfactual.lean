/-
# The executed counterfactual evaluator sums the canonical information fiber

The complete history codec, exact primitive chance evaluation and reach
factorization supply this result. The summation includes every legal off-path
history and does not assume a counterfactual payoff or regret identity.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalReach
import GameTheory.Analysis.ReBeL.Examples.RationalSites
import GameTheory.Analysis.ReBeL.Examples.CFRNash

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- The finite carrier is the original game's full legal history enumeration. -/
local instance counterfactualHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Equality is proof-level on the canonical full observation carrier. -/
local instance counterfactualInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Each information fiber is a finite subtype of all legal histories. -/
local instance counterfactualFiberFintype (who : Player)
    (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).InformationHistory who info) := by
  classical
  infer_instance

private theorem cast_map_sum {α : Type*} (xs : List α) (f : α → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map fun x => (f x : ℝ)).sum := by
  induction xs with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]

/-- Reindexing the raw list neither duplicates nor omits any canonical history. -/
theorem row_sum_eq (f : (protocol fullPrior).History → ℝ) :
    (rows.map fun row => f (decode row)).sum = ∑ history, f history := by
  classical
  have hset : (rows.map decode).toFinset = Finset.univ := by
    ext history
    simp [decoded_rows_complete history]
  have h := List.sum_toFinset f decoded_rows_nodup
  rw [hset] at h
  simpa only [List.map_map, Function.comp_def] using h.symm

/-- Exact agreement of the actual numeric information-fiber summation with the
canonical unnormalized counterfactual reach-weighted continuation expectation. -/
theorem counterfactualValue_eq_fiber
    (reachNumeric continueNumeric : NumericProfile)
    (reachSemantic continueSemantic : Profile (model fullPrior).behavioralSignature)
    (hreach : RowRealizes reachNumeric reachSemantic)
    (hcontinue : RowRealizes continueNumeric continueSemantic)
    (who : Player) (key : ActiveKey) (horizon : ℕ) :
    (table.counterfactualValue reachNumeric continueNumeric who key.1 horizon : ℝ) =
      ∑ history : (model fullPrior).InformationHistory who (decodeInfo key.1),
        (model fullPrior).counterfactualReachProbability reachSemantic who history.1.trace *
          ((model fullPrior).runBehavioralFrom continueSemantic
            (horizon - table.depth who key.1) history.1).expect (cfrPayoff who) := by
  classical
  let f : (protocol fullPrior).History → ℝ := fun history =>
    (model fullPrior).counterfactualReachProbability reachSemantic who history.trace *
      ((model fullPrior).runBehavioralFrom continueSemantic
        (horizon - table.depth who key.1) history).expect (cfrPayoff who)
  calc
    _ = (rows.map fun row =>
        if (model fullPrior).infoOf who (decode row).trace = decodeInfo key.1 then
          f (decode row) else 0).sum := by
      unfold HistoryTable.counterfactualValue
      rw [show table.histories = rows from rfl, cast_map_sum]
      apply congrArg List.sum
      apply List.map_congr_left
      intro row _
      rw [show table.info who row = information who row from rfl]
      by_cases h : information who row = key.1
      · have hc := (information_matches who row key).mpr h
        rw [if_pos h, if_pos hc, Rat.cast_mul]
        exact congrArg₂ (fun x y : ℝ => x * y)
          (counterfactualReach_correct reachNumeric reachSemantic hreach who row)
          (value_correct continueNumeric continueSemantic hcontinue
            (horizon - table.depth who key.1) row who)
      · have hc : (model fullPrior).infoOf who (decode row).trace ≠ decodeInfo key.1 :=
          fun hc => h ((information_matches who row key).mp hc)
        simp only [if_neg h, if_neg hc, Rat.cast_zero]
    _ = ∑ history, if (model fullPrior).infoOf who history.trace = decodeInfo key.1 then
        f history else 0 := row_sum_eq (fun history =>
          if (model fullPrior).infoOf who history.trace = decodeInfo key.1 then f history else 0)
    _ = ∑' history : (protocol fullPrior).History,
        {history | (model fullPrior).infoOf who history.trace = decodeInfo key.1}.indicator
          f history := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro history _
      by_cases h : (model fullPrior).infoOf who history.trace = decodeInfo key.1 <;> simp [h]
    _ = ∑' history : (model fullPrior).InformationHistory who (decodeInfo key.1),
        f history.1 :=
      (tsum_subtype
        {history | (model fullPrior).infoOf who history.trace = decodeInfo key.1} f).symm
    _ = ∑ history : (model fullPrior).InformationHistory who (decodeInfo key.1),
        f history.1 := tsum_fintype _

/-- Installing any represented continuation keeps the original reach profile.
The absolute local clock is the same one used by the general real CFR solver. -/
theorem counterfactualValue_correct
    (reachNumeric continueNumeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (who : Player) (key : ActiveKey)
    (alternative : (model fullPrior).BehavioralPolicy who)
    (hreach : RowRealizes reachNumeric semantic)
    (hcontinue : RowRealizes continueNumeric (Profile.update semantic who alternative))
    (horizon : ℕ) :
    (table.counterfactualValue reachNumeric continueNumeric who key.1 horizon : ℝ) =
      (model fullPrior).counterfactualContinuationValue semantic who (canonicalSite who key)
        alternative (cfrPayoff who)
        (horizon - decisionClock.depth who (canonicalSite who key).1) := by
  rw [counterfactualValue_eq_fiber reachNumeric continueNumeric semantic
    (Profile.update semantic who alternative) hreach hcontinue who key horizon,
    canonicalSite_depth]
  rfl

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
