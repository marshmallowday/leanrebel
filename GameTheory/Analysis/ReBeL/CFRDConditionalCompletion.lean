/-
# Conditional payoffs and values under joint zero-own-reach completion

Every focal deviation law is preserved when the opponents' original own
reaches are nonzero on the conditional kernel. Thus the attained infostate
value is unchanged too, even if the focal player's own reach is zero.
The canonical deviation theorem is shared with CFRDCompletedLeaf.
-/

import GameTheory.Analysis.ReBeL.CFRDCompletedLeaf
import GameTheory.Analysis.ReBeL.CFRDQuerySupport

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable {M : InformationModel.{uι, us, ua, up, uq, uk} E}
variable [Fintype ι] [DecidableEq ι]
variable {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- The conditional expected payoff of each behavioral deviation is unchanged
when all other players have positive original own reach on the kernel. -/
theorem completeZeroReach_conditionalPayoff (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (fuel : Nat)
    (payoff : E.History → ℝ) (target : M.BehavioralPolicy who) (type : T)
    (positive : ∀ history ∈ (slice.kernel type).law.support,
      ∀ player, player ≠ who → M.playerReachProbability base player history.trace ≠ 0) :
    slice.conditionalPayoff (cfrDCompleteZeroReach M base completion) fuel payoff target type =
      slice.conditionalPayoff base fuel payoff target type := by
  unfold conditionalPayoff
  apply congrArg (fun law : FinDist E.History => law.expect payoff)
  apply FinDist.bind_congr
  intro history supported
  exact cfrDCompleteZeroReach_deviation_continuation M hrecall base completion who target
    fuel history (positive history supported)

/-- With positive original own reach for every player, the actual completed
conditional payoff is unchanged, including all future off-path decisions. -/
theorem completeZeroReach_actualPayoff (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (fuel : Nat)
    (payoff : E.History → ℝ) (type : T)
    (positive : ∀ history ∈ (slice.kernel type).law.support,
      ∀ player, M.playerReachProbability base player history.trace ≠ 0) :
    slice.conditionalPayoff (cfrDCompleteZeroReach M base completion) fuel payoff
        (cfrDCompleteZeroReach M base completion who) type =
      slice.conditionalPayoff base fuel payoff (base who) type := by
  unfold conditionalPayoff
  rw [Profile.update_eq_self, Profile.update_eq_self]
  apply congrArg (fun law : FinDist E.History => law.expect payoff)
  apply FinDist.bind_congr
  intro history supported
  exact cfrDCompleteZeroReach_positive_continuation M hrecall base completion fuel history
    (positive history supported)

variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- The attained maximum over ALL behavioral deviations is also preserved.
No positive own reach for the focal player and no Nash assumption are needed. -/
theorem completeZeroReach_infoValue (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (base completion : Profile M.behavioralSignature) (type : T)
    (positive : ∀ history ∈ (slice.kernel type).law.support,
      ∀ player, player ≠ who → M.playerReachProbability base player history.trace ≠ 0) :
    slice.infoValue fallback fuel payoff (cfrDCompleteZeroReach M base completion) type =
      slice.infoValue fallback fuel payoff base type := by
  let completed := cfrDCompleteZeroReach M base completion
  let first := (slice.simultaneousResponse fallback fuel payoff completed).toBehavioral
  let second := (slice.simultaneousResponse fallback fuel payoff base).toBehavioral
  apply le_antisymm
  · calc
      _ = slice.conditionalPayoff completed fuel payoff first type :=
        (slice.simultaneousResponse_attains fallback fuel payoff completed type).symm
      _ = slice.conditionalPayoff base fuel payoff first type :=
        slice.completeZeroReach_conditionalPayoff hrecall base completion fuel payoff
          first type positive
      _ ≤ _ := slice.conditionalPayoff_le_infoValue hrecall fallback fuel payoff base type first
  · calc
      _ = slice.conditionalPayoff base fuel payoff second type :=
        (slice.simultaneousResponse_attains fallback fuel payoff base type).symm
      _ = slice.conditionalPayoff completed fuel payoff second type :=
        (slice.completeZeroReach_conditionalPayoff hrecall base completion fuel payoff
          second type positive).symm
      _ ≤ _ := slice.conditionalPayoff_le_infoValue hrecall fallback fuel payoff
        completed type second

end GameTheory.ReBeL.TypeBeliefSlice
