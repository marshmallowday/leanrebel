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

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut uv
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ i, Fintype (E.Action i)] [∀ i info, Fintype (M.Choice i info)]
variable {observations : List M.PublicSignal} {T : ι → Type ut} {Tag : Type uv}

/-- An actual sampled reference query supplies all own-reach hypotheses of
joint completed leaf optimality. The remaining hypotheses identify the typed
kernel, its factual support, and the canonical PBS Nash game; none supplies a
payoff inequality or an assumed optimal completion policy. -/
theorem cfrDJointTypeCompletion_referenceQuery_optimal (hrecall : M.PerfectRecall)
    (slices : ∀ who, TypeBeliefSlice M observations who (T who))
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (base : Profile M.behavioralSignature)
    (who : ι) (own : FinDist (T who))
    (equilibrium : IsNash (behavioralBeliefForm M ((slices who).mixture own) fuel)
      (euPreference utility) base) (type : T who)
    (cut : Nat) (observe : E.History → Tag) (readInfo : Tag → M.InfoState who)
    (information : ∀ history, M.infoOf who history.trace = readInfo (observe history))
    (tag : Tag)
    (sampled : tag ∈ ((unilateralReferenceLaw M base fallback who cut).map observe).support)
    (kernel : ((slices who).kernel type).law =
      (unilateralReferenceLaw M base fallback who cut).condOnFibre observe tag)
    (factual : type ∈ own.support ↔ tag ∈ ((M.runBehavioral base cut).map observe).support)
    (target : M.BehavioralPolicy who) :
    (slices who).conditionalPayoff (cfrDJointTypeCompletion M slices fallback fuel utility base)
        fuel (fun history => utility history who) target type ≤
      (PublicBelief.continuationLaw M (cfrDJointTypeCompletion M slices fallback fuel utility base)
        fuel ((slices who).kernel type)).expect (fun history => utility history who) := by
  apply cfrDJointTypeCompletion_optimal M hrecall slices fallback fuel utility base who own
    equilibrium type
  · intro history reached other different
    exact cfrDReference_conditional_opponents M base fallback who cut observe tag sampled
      history (by simpa only [kernel] using reached) other different
  · intro onPath history reached
    exact (cfrDReference_factual_support_iff M hrecall base fallback who cut observe readInfo
      information tag sampled history (by simpa only [kernel] using reached)).mp
      (factual.mp onPath)
  · intro offPath history reached
    exact cfrDReference_factual_absent_own_zero M hrecall base fallback who cut observe readInfo
      information tag sampled (fun present => offPath (factual.mpr present)) history
      (by simpa only [kernel] using reached)

/-- The same constructed completion satisfies the numerical conditional-oracle
inequality at the actual reference query, against every behavioral deviation.
This is a sampled-query result; arbitrary off-support fallback queries are not
silently upgraded to Bayesian or counterfactual guarantees. -/
theorem cfrDJointTypeCompletion_referenceOracle_optimal (hrecall : M.PerfectRecall)
    (slices : ∀ who, TypeBeliefSlice M observations who (T who))
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (base : Profile M.behavioralSignature)
    (who : ι) (own : FinDist (T who))
    (equilibrium : IsNash (behavioralBeliefForm M ((slices who).mixture own) fuel)
      (euPreference utility) base) (type : T who)
    (cut : Nat) (observe : E.History → Tag) (readInfo : Tag → M.InfoState who)
    (information : ∀ history, M.infoOf who history.trace = readInfo (observe history))
    (tag : Tag)
    (sampled : tag ∈ ((unilateralReferenceLaw M base fallback who cut).map observe).support)
    (kernel : ((slices who).kernel type).law =
      (unilateralReferenceLaw M base fallback who cut).condOnFibre observe tag)
    (factual : type ∈ own.support ↔ tag ∈ ((M.runBehavioral base cut).map observe).support)
    (target : M.BehavioralPolicy who) :
    conditionalOracleValue (unilateralReferenceLaw M base fallback who cut) observe
        (fun history => (M.runBehavioralFrom
          (Profile.update (cfrDJointTypeCompletion M slices fallback fuel utility base) who target)
          fuel history).expect (fun outcome => utility outcome who)) tag ≤
      conditionalOracleValue (unilateralReferenceLaw M base fallback who cut) observe
        (fun history => (M.runBehavioralFrom
          (cfrDJointTypeCompletion M slices fallback fuel utility base) fuel history).expect
          (fun outcome => utility outcome who)) tag := by
  have optimal := cfrDJointTypeCompletion_referenceQuery_optimal M hrecall slices fallback
    fuel utility base who own equilibrium type cut observe readInfo information tag sampled
    kernel factual target
  simpa only [TypeBeliefSlice.conditionalPayoff, PublicBelief.continuationLaw,
    FinDist.expect_bind, conditionalOracleValue, kernel] using optimal

end GameTheory.ReBeL
