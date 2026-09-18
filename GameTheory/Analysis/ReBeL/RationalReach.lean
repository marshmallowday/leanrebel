/-
# Exact rational reach factors on canonical histories

A runtime path is a serialization of the canonical legal choices, not a new
notion of reach. The cast proofs include zero-probability policies and keep
chance separate from every player's strategic contribution.
-/

import GameTheory.Analysis.ReBeL.RationalEvaluation
import GameTheory.ReBeL.ReachFactorization

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

universe ui us ua up uq uk
variable {ι : Type ui} {E : ExecutionProtocol.{ui, us, ua} ι}
variable (M : InformationModel.{ui, us, ua, up, uq, uk} E)

/-- Serialize the existing information-local choices along a legal trace.
No opponent's hidden information is an input to the focal policy. -/
def choicePath (who : ι) : {state : E.State} → E.Trace state → List (Sigma (M.Choice who))
  | _, .start => []
  | _, .extend prior joint legal _ =>
      ⟨M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩ :: choicePath who prior

/-- Multiplication over the serialization is the one canonical own reach. -/
theorem choicePath_product (semantic : Profile M.behavioralSignature)
    (who : ι) {state : E.State} (trace : E.Trace state) :
    ((choicePath M who trace).map fun entry => (semantic who entry.1).prob entry.2).prod =
      M.playerReachProbability semantic who trace := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [choicePath, List.map_cons, List.prod_cons, ih,
        InformationModel.playerReachProbability, InformationModel.playerStepProb]
      ring

private theorem cast_map_prod {α : Type*} (xs : List α) (f : α → ℚ) :
    ((xs.map f).prod : ℝ) = (xs.map fun x => (f x : ℝ)).prod := by
  induction xs with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.prod_cons, Rat.cast_mul, ih]

/-- A table whose choice path encodes the legal trace has exact own reach. -/
theorem ownReach_eq_playerReach
    (G : HistoryTable E.History M.InfoState M.Choice)
    (hpath : ∀ who history, G.ownPath who history = choicePath M who history.trace)
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic)
    (who : ι) (history : E.History) :
    (G.ownReach numeric who history : ℝ) =
      M.playerReachProbability semantic who history.trace := by
  unfold HistoryTable.ownReach
  rw [hpath, cast_map_prod]
  simp_rw [hreal]
  exact choicePath_product M semantic who history.trace

variable [Fintype ι] [DecidableEq ι]

/-- Counterfactual reach is chance times the product of opponents' own reaches,
including chance correlations and histories the focal policy never reaches. -/
theorem counterfactualReach_eq_chance_prod (semantic : Profile M.behavioralSignature)
    (who : ι) {state : E.State} (trace : E.Trace state) :
    M.counterfactualReachProbability semantic who trace =
      chanceReach trace * ∏ other ∈ Finset.univ.erase who,
        M.playerReachProbability semantic other trace := by
  induction trace with
  | start => simp [InformationModel.counterfactualReachProbability,
      chanceReach, InformationModel.playerReachProbability]
  | extend prior joint legal realized ih =>
      rw [InformationModel.counterfactualReachProbability, ih]
      simp only [chanceReach, InformationModel.counterfactualStepProb,
        InformationModel.opponentsStepProb, InformationModel.playerReachProbability,
        InformationModel.playerStepProb, Finset.prod_mul_distrib]
      ring

/-- Exact conversion of the runtime counterfactual coefficient. The supplied
chance certificate is policy-independent; no regret or value bound is assumed. -/
theorem counterfactualReach_eq
    (G : HistoryTable E.History M.InfoState M.Choice)
    (hpath : ∀ who history, G.ownPath who history = choicePath M who history.trace)
    (hchance : ∀ history, ((G.chanceFactors history).prod : ℝ) = chanceReach history.trace)
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic)
    (who : ι) (history : E.History) :
    (G.counterfactualReach numeric who history : ℝ) =
      M.counterfactualReachProbability semantic who history.trace := by
  unfold HistoryTable.counterfactualReach
  push_cast
  rw [hchance, counterfactualReach_eq_chance_prod]
  congr 1
  exact Finset.prod_congr rfl fun other _ =>
    ownReach_eq_playerReach M G hpath numeric semantic hreal other history

end GameTheory.ReBeL.Rational
