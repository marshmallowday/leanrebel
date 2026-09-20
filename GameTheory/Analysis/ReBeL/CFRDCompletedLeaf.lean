/-
# Joint zero-reach completion and conditional leaf optimality

Supported types inherit Nash optimality. Unsupported zero-own-reach types
use a constructed conditional best response. Completing opponents does not
invalidate either result: their positive own reach on the conditional kernel
preserves every focal deviation law. Reach compatibility is explicit and is
not inferred from ordinary Nash or from equality of the initial outcome law.
-/

import GameTheory.Analysis.ReBeL.CFRDZeroReachContinuation
import GameTheory.Analysis.ReBeL.CFRDZeroReachOptimality
import GameTheory.Analysis.ReBeL.PBSLeafOptimality

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Completing the opponents preserves every focal continuation deviation
from a root where those opponents have nonzero original own reach. -/
theorem cfrDCompleteZeroReach_deviation_continuation (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (who : ι)
    (target : M.BehavioralPolicy who) (fuel : Nat) (history : E.History)
    (positive : ∀ other, other ≠ who →
      M.playerReachProbability base other history.trace ≠ 0) :
    M.runBehavioralFrom
        (Profile.update (cfrDCompleteZeroReach M base completion) who target) fuel history =
      M.runBehavioralFrom (Profile.update base who target) fuel history := by
  classical
  let selected : Finset ι := Finset.univ.erase who
  let unknown := Profile.update base who target
  have absent : who ∉ selected := by simp [selected]
  have first : (fun player => if player ∈ selected then
        cfrDCompleteZeroReach M base completion player else unknown player) =
      Profile.update (cfrDCompleteZeroReach M base completion) who target := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [if_neg absent, unknown, Profile.update_same]
    · have member : player ∈ selected :=
        Finset.mem_erase.mpr ⟨same, Finset.mem_univ player⟩
      rw [if_pos member, Profile.update_of_ne _ _ same]
  have second : (fun player => if player ∈ selected then base player else unknown player) =
      Profile.update base who target := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [if_neg absent, unknown, Profile.update_same]
    · have member : player ∈ selected :=
        Finset.mem_erase.mpr ⟨same, Finset.mem_univ player⟩
      rw [if_pos member, Profile.update_of_ne _ _ same]
  have law := cfrDCompleteZeroReach_selected_continuation M hrecall base completion unknown
    selected fuel history (fun player member => positive player (Finset.ne_of_mem_erase member))
  simpa only [first, second] using law

/-- At a focal zero-own-reach root, joint completion executes the supplied
focal response against the original opponents, provided their own reach is
positive. This statement concerns the entire conditional outcome law. -/
theorem cfrDCompleteZeroReach_counterfactual_continuation (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (who : ι)
    (fuel : Nat) (history : E.History)
    (zero : M.playerReachProbability base who history.trace = 0)
    (positive : ∀ other, other ≠ who →
      M.playerReachProbability base other history.trace ≠ 0) :
    M.runBehavioralFrom (cfrDCompleteZeroReach M base completion) fuel history =
      M.runBehavioralFrom (Profile.update base who (completion who)) fuel history := by
  calc
    _ = M.runBehavioralFrom
        (Profile.update base who (cfrDCompleteZeroReach M base completion who))
        fuel history := by
      simpa only [Profile.update_eq_self] using
        cfrDCompleteZeroReach_deviation_continuation M hrecall base completion who
          (cfrDCompleteZeroReach M base completion who) fuel history positive
    _ = _ := cfrDCompleteZeroReach_continuation M hrecall base completion who fuel history zero

namespace TypeBeliefSlice

variable {M} {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- Joint completion attains a type's full behavioral best-response value.
Positive types use Nash; zero-own-reach types use finite constructed responses.
The support/own-reach alignment and opponents' kernel support are explicit. -/
theorem completed_value_eq_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (base completion : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) base)
    (computed : completion who =
      (slice.simultaneousResponse fallback fuel (fun history => utility history who)
        base).toBehavioral) (type : T)
    (opponents : ∀ history ∈ (slice.kernel type).law.support, ∀ other, other ≠ who →
      M.playerReachProbability base other history.trace ≠ 0)
    (supported : type ∈ own.support → ∀ history ∈ (slice.kernel type).law.support,
      M.playerReachProbability base who history.trace ≠ 0)
    (unsupported : type ∉ own.support → ∀ history ∈ (slice.kernel type).law.support,
      M.playerReachProbability base who history.trace = 0) :
    (PublicBelief.continuationLaw M (cfrDCompleteZeroReach M base completion) fuel
        (slice.kernel type)).expect (fun history => utility history who) =
      slice.infoValue fallback fuel (fun history => utility history who) base type := by
  classical
  by_cases onPath : type ∈ own.support
  · calc
      _ = (PublicBelief.continuationLaw M base fuel (slice.kernel type)).expect
          (fun history => utility history who) := by
        apply congrArg (fun law : FinDist E.History =>
          law.expect (fun history => utility history who))
        apply FinDist.bind_congr
        intro history member
        apply cfrDCompleteZeroReach_positive_continuation M hrecall
        intro other
        by_cases same : other = who
        · subst other
          exact supported onPath history member
        · exact opponents history member other same
      _ = _ := by
        simpa only [conditionalPayoff, Profile.update_eq_self] using
          slice.conditional_value_eq_of_nash hrecall fallback fuel utility own base
            equilibrium type onPath
  · calc
      _ = slice.conditionalPayoff base fuel (fun history => utility history who)
          (completion who) type := by
        unfold conditionalPayoff
        apply congrArg (fun law : FinDist E.History =>
          law.expect (fun history => utility history who))
        apply FinDist.bind_congr
        intro history member
        exact cfrDCompleteZeroReach_counterfactual_continuation M hrecall base completion who
          fuel history (unsupported onPath history member) (opponents history member)
      _ = _ := by
        rw [computed]
        exact slice.simultaneousResponse_attains fallback fuel
          (fun history => utility history who) base type

/-- The completed joint profile, not merely its original opponents, is
conditionally optimal against every complete behavioral focal deviation. -/
theorem completed_bestResponse_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (base completion : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) base)
    (computed : completion who =
      (slice.simultaneousResponse fallback fuel (fun history => utility history who)
        base).toBehavioral) (type : T)
    (opponents : ∀ history ∈ (slice.kernel type).law.support, ∀ other, other ≠ who →
      M.playerReachProbability base other history.trace ≠ 0)
    (supported : type ∈ own.support → ∀ history ∈ (slice.kernel type).law.support,
      M.playerReachProbability base who history.trace ≠ 0)
    (unsupported : type ∉ own.support → ∀ history ∈ (slice.kernel type).law.support,
      M.playerReachProbability base who history.trace = 0)
    (target : M.BehavioralPolicy who) :
    slice.conditionalPayoff (cfrDCompleteZeroReach M base completion) fuel
        (fun history => utility history who) target type ≤
      (PublicBelief.continuationLaw M (cfrDCompleteZeroReach M base completion) fuel
        (slice.kernel type)).expect (fun history => utility history who) := by
  calc
    _ = slice.conditionalPayoff base fuel (fun history => utility history who) target type := by
      unfold conditionalPayoff
      apply congrArg (fun law : FinDist E.History =>
        law.expect (fun history => utility history who))
      apply FinDist.bind_congr
      intro history member
      exact cfrDCompleteZeroReach_deviation_continuation M hrecall base completion who target
        fuel history (opponents history member)
    _ ≤ slice.infoValue fallback fuel (fun history => utility history who) base type :=
      slice.conditionalPayoff_le_infoValue hrecall fallback fuel
        (fun history => utility history who) base type target
    _ = _ := (slice.completed_value_eq_of_nash hrecall fallback fuel utility own base completion
      equilibrium computed type opponents supported unsupported).symm

end TypeBeliefSlice

variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {T : ι → Type ut}

/-- One simultaneous joint completion is computed by finite conditional
maximization and legal remembered-type splicing for every player. -/
def cfrDJointTypeCompletion
    (slices : ∀ who, TypeBeliefSlice M observations who (T who))
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (base : Profile M.behavioralSignature) :
    Profile M.behavioralSignature :=
  cfrDCompleteZeroReach M base (fun who =>
    ((slices who).simultaneousResponse fallback fuel
      (fun history => utility history who) base).toBehavioral)

/-- The actual constructed joint completion satisfies the conditional
optimality theorem without an assumed completion policy or value inequality. -/
theorem cfrDJointTypeCompletion_optimal (hrecall : M.PerfectRecall)
    (slices : ∀ who, TypeBeliefSlice M observations who (T who))
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (base : Profile M.behavioralSignature)
    (who : ι) (own : FinDist (T who))
    (equilibrium : IsNash (behavioralBeliefForm M ((slices who).mixture own) fuel)
      (euPreference utility) base) (type : T who)
    (opponents : ∀ history ∈ ((slices who).kernel type).law.support,
      ∀ other, other ≠ who → M.playerReachProbability base other history.trace ≠ 0)
    (supported : type ∈ own.support → ∀ history ∈ ((slices who).kernel type).law.support,
      M.playerReachProbability base who history.trace ≠ 0)
    (unsupported : type ∉ own.support → ∀ history ∈ ((slices who).kernel type).law.support,
      M.playerReachProbability base who history.trace = 0)
    (target : M.BehavioralPolicy who) :
    (slices who).conditionalPayoff (cfrDJointTypeCompletion M slices fallback fuel utility base)
        fuel (fun history => utility history who) target type ≤
      (PublicBelief.continuationLaw M (cfrDJointTypeCompletion M slices fallback fuel utility base)
        fuel ((slices who).kernel type)).expect (fun history => utility history who) := by
  exact (slices who).completed_bestResponse_of_nash hrecall fallback fuel utility own base
    (fun player => ((slices player).simultaneousResponse fallback fuel
      (fun history => utility history player) base).toBehavioral)
    equilibrium rfl type opponents supported unsupported target

end GameTheory.ReBeL
