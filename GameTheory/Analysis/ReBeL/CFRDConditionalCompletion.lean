/-
# Conditional deviation laws under joint zero-own-reach completion

Completing opponents cannot alter a conditional deviation law when their
original own reaches are nonzero on the root kernel. The deviator's own reach
may be zero. Completing every player also preserves the actual conditional
law on all-positive kernels. These facts connect supported-type Nash
optimality to the completed profile without confusing it with root-law equality.
-/

import GameTheory.Analysis.ReBeL.CFRDZeroReachContinuation
import GameTheory.Analysis.ReBeL.PBSLeafOptimality

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Every complete unilateral deviation has the same conditional law against
jointly completed opponents. Only opponents' original own reaches must be
positive; no joint-reach or focal-own-reach assumption is imposed. -/
theorem cfrDCompleteZeroReach_deviation_continuation (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (who : ι)
    (target : M.BehavioralPolicy who) (fuel : Nat) (history : E.History)
    (positive : ∀ player, player ≠ who →
      M.playerReachProbability base player history.trace ≠ 0) :
    M.runBehavioralFrom
        (Profile.update (cfrDCompleteZeroReach M base completion) who target) fuel history =
      M.runBehavioralFrom (Profile.update base who target) fuel history := by
  classical
  have identify (first second : Profile M.behavioralSignature) :
      (fun player => if player ∈ Finset.univ.erase who then first player
        else (Profile.update second who target) player) =
      Profile.update first who target := by
    funext player
    by_cases same : player = who
    · subst player
      simp [Profile.update_same]
    · rw [if_pos (Finset.mem_erase.mpr ⟨same, Finset.mem_univ player⟩),
        Profile.update_of_ne _ _ same]
  have preserved := cfrDCompleteZeroReach_selected_continuation M hrecall base completion
    (Profile.update base who target) (Finset.univ.erase who) fuel history
    (fun player member => positive player (Finset.mem_erase.mp member).1)
  simpa only [identify] using preserved

namespace TypeBeliefSlice

variable {M} {observations : List M.PublicSignal} {who : ι} {T : Type ut}
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
conditional payoff is unchanged as well, including all future off-path decisions. -/
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

/-- Supported-type Nash optimality survives simultaneous zero-reach completion
on positive root kernels. Optimality is derived from the canonical Nash
predicate, not added as a continuation-value certificate. -/
theorem completeZeroReach_bestResponse_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (base completion : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) base) (type : T) (supported : type ∈ own.support)
    (positive : ∀ history ∈ (slice.kernel type).law.support,
      ∀ player, M.playerReachProbability base player history.trace ≠ 0)
    (target : M.BehavioralPolicy who) :
    slice.conditionalPayoff (cfrDCompleteZeroReach M base completion) fuel
        (fun history => utility history who) target type ≤
      slice.conditionalPayoff (cfrDCompleteZeroReach M base completion) fuel
        (fun history => utility history who) (cfrDCompleteZeroReach M base completion who)
        type := by
  rw [slice.completeZeroReach_conditionalPayoff hrecall base completion fuel
      (fun history => utility history who) target type
      (fun history member player _ => positive history member player),
    slice.completeZeroReach_actualPayoff hrecall base completion fuel
      (fun history => utility history who) type positive]
  exact slice.conditional_bestResponse_of_nash hrecall fallback fuel utility own base
    equilibrium type supported target

end TypeBeliefSlice
end GameTheory.ReBeL
