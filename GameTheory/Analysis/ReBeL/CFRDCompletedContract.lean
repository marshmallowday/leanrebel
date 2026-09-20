/-
# From compatible computed query responses to the CFR-D leaf contract

Joint zero-own-reach completion preserves the factual and unilateral reference
query packets. A computed response need agree only on the legal continuation
of its own conditional kernel, not at unrelated public states. Canonical PBS
Nash, compatible query kernels, and this local policy agreement derive the
actual solver's all-deviation leaf contract. No value bound is assumed in the
query data. Constructing those query games from recursive solves remains separate.
-/

import GameTheory.Analysis.ReBeL.CFRDConditionalCompletion
import GameTheory.Analysis.ReBeL.CFRDPBSOracle
import GameTheory.Analysis.ReBeL.CFRDLeafContract

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

section ReferenceQueries

variable [∀ who info, Fintype (M.Choice who info)]

/-- Completing opponents does not change the actual unilateral reference law.
The reference player's uniform legal policy is the same before and after. -/
theorem cfrDCompleteZeroReach_referenceLaw (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (cut : Nat) :
    unilateralReferenceLaw M (cfrDCompleteZeroReach M base completion) fallback who cut =
      unilateralReferenceLaw M base fallback who cut :=
  cfrDCompleteZeroReach_deviation_run M hrecall base completion who
    (uniformLegalPolicy M who (fallback who)) cut

/-- Both factual and counterfactual PBS query packets are unchanged, not just
one expected value or the observation marginals. -/
theorem cfrDCompleteZeroReach_currentPBS (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (cut : Nat) :
    cfrDCurrentPBS M fallback (cfrDCompleteZeroReach M base completion) cut =
      cfrDCurrentPBS M fallback base cut := by
  unfold cfrDCurrentPBS
  rw [cfrDCompleteZeroReach_run M hrecall]
  congr 1
  funext who
  rw [cfrDCompleteZeroReach_referenceLaw M hrecall]

/-- At a sampled query, every behavioral deviation has the same conditional
value against completed opponents, even when the focal own reach is zero.
The conditional on the left uses the COMPLETED profile's actual reference law. -/
theorem cfrDCompleteZeroReach_referenceDeviationValue {Tag : Type*}
    (hrecall : M.PerfectRecall) (base completion : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (cut remaining : Nat)
    (observe : E.History → Tag) (tag : Tag)
    (sampled : tag ∈ ((unilateralReferenceLaw M base fallback who cut).map observe).support)
    (target : M.BehavioralPolicy who) (payoff : E.History → ℝ) :
    conditionalOracleValue
        (unilateralReferenceLaw M (cfrDCompleteZeroReach M base completion) fallback who cut)
        observe (fun history => (M.runBehavioralFrom
          (Profile.update (cfrDCompleteZeroReach M base completion) who target)
          remaining history).expect payoff) tag =
      conditionalOracleValue (unilateralReferenceLaw M base fallback who cut) observe
        (fun history => (M.runBehavioralFrom (Profile.update base who target)
          remaining history).expect payoff) tag := by
  rw [cfrDCompleteZeroReach_referenceLaw M hrecall]
  unfold conditionalOracleValue
  apply FinDist.expect_congr
  intro history reached
  apply congrArg (fun law : FinDist E.History => law.expect payoff)
  exact cfrDCompleteZeroReach_deviation_continuation M hrecall base completion who target
    remaining history
    (cfrDReference_conditional_opponents M base fallback who cut observe tag sampled
      history reached)

end ReferenceQueries

namespace TypeBeliefSlice

variable {M} {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- Only legal nonterminal continuation decisions on this kernel must agree.
A public-state splice need not match its constituent response everywhere. -/
theorem conditionalPayoff_eq_of_reachable_agreement
    (base : Profile M.behavioralSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (first second : M.BehavioralPolicy who) (type : T)
    (agree : ∀ history ∈ (slice.kernel type).law.support,
      ∀ later, E.ReachesWithin fuel history later → ¬ E.terminal later.state →
        first (M.infoOf who later.trace) = second (M.infoOf who later.trace)) :
    slice.conditionalPayoff base fuel payoff first type =
      slice.conditionalPayoff base fuel payoff second type := by
  unfold conditionalPayoff
  apply congrArg (fun law : FinDist E.History => law.expect payoff)
  apply FinDist.bind_congr
  intro history supported
  apply M.runBehavioralFrom_congr
  intro later reaches live player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact agree history supported later reaches live
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- Joint completion attains the conditional value when its focal decisions
locally implement the computed finite best response. The supported branch
uses Nash; the zero-own-reach branch uses that computed response. -/
theorem completed_value_eq_of_local_response (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (base completion : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) base) (type : T)
    (localResponse : ∀ history ∈ (slice.kernel type).law.support,
      ∀ later, E.ReachesWithin fuel history later → ¬ E.terminal later.state →
        completion who (M.infoOf who later.trace) =
          (slice.simultaneousResponse fallback fuel (fun h => utility h who) base).toBehavioral
            (M.infoOf who later.trace))
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
      _ = slice.conditionalPayoff base fuel (fun history => utility history who)
          (slice.simultaneousResponse fallback fuel (fun h => utility h who) base).toBehavioral
          type := slice.conditionalPayoff_eq_of_reachable_agreement base fuel
            (fun history => utility history who) _ _ type localResponse
      _ = _ := slice.simultaneousResponse_attains fallback fuel
        (fun history => utility history who) base type

end TypeBeliefSlice

variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable [∀ who info, Fintype (M.Choice who info)]

/-- Canonical query equilibria and locally implemented computed responses
supply the ACTUAL all-deviation leaf contract consumed by the depth solver.
The type and public state may vary by query. The data contains no assumed
payoff inequality, and no claim is made at an unsampled fallback conditional. -/
theorem cfrDCompleteZeroReach_leafOptimal_of_queryGames (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (who : ι) (utility : E.History → ι → ℝ) (cut remaining : Nat)
    (queries : ∀ info : M.InfoState who,
      (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
        (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support →
      ∃ (observations : List M.PublicSignal) (T : Type ut)
        (slice : TypeBeliefSlice M observations who T) (own : FinDist T) (type : T),
        IsNash (behavioralBeliefForm M (slice.mixture own) remaining)
          (euPreference utility) base ∧
        (∀ history ∈ (slice.kernel type).law.support,
          ∀ later, E.ReachesWithin remaining history later → ¬ E.terminal later.state →
            completion who (M.infoOf who later.trace) =
              (slice.simultaneousResponse fallback remaining (fun h => utility h who)
                base).toBehavioral (M.infoOf who later.trace)) ∧
        (slice.kernel type).law =
          (unilateralReferenceLaw M base fallback who cut).condOnFibre
            (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) (info, true) ∧
        (type ∈ own.support ↔ (info, true) ∈ ((M.runBehavioral base cut).map
          (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support)) :
    CFRDLeafOptimal M (cfrDCompleteZeroReach M base completion) fallback who
      (fun history => utility history who) cut remaining 0 := by
  intro target info sampled
  rw [cfrDCompleteZeroReach_referenceLaw M hrecall] at sampled ⊢
  obtain ⟨observations, T, slice, own, type, equilibrium, localResponse, kernel, factual⟩ :=
    queries info sampled
  have opponents : ∀ history ∈ (slice.kernel type).law.support, ∀ other, other ≠ who →
      M.playerReachProbability base other history.trace ≠ 0 := by
    intro history reached other different
    exact cfrDReference_conditional_opponents M base fallback who cut
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) (info, true) sampled
      history (by simpa only [kernel] using reached) other different
  have supported : type ∈ own.support → ∀ history ∈ (slice.kernel type).law.support,
      M.playerReachProbability base who history.trace ≠ 0 := by
    intro onPath history reached
    exact (cfrDReference_factual_support_iff M hrecall base fallback who cut
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) Prod.fst (fun _ => rfl)
      (info, true) sampled history (by simpa only [kernel] using reached)).mp (factual.mp onPath)
  have unsupported : type ∉ own.support → ∀ history ∈ (slice.kernel type).law.support,
      M.playerReachProbability base who history.trace = 0 := by
    intro offPath history reached
    exact cfrDReference_factual_absent_own_zero M hrecall base fallback who cut
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) Prod.fst (fun _ => rfl)
      (info, true) sampled (fun present => offPath (factual.mpr present)) history
      (by simpa only [kernel] using reached)
  have actual := slice.completed_value_eq_of_local_response hrecall fallback remaining
    utility own base completion equilibrium type localResponse opponents supported unsupported
  have better : slice.conditionalPayoff (cfrDCompleteZeroReach M base completion) remaining
        (fun history => utility history who) target type ≤
      (PublicBelief.continuationLaw M (cfrDCompleteZeroReach M base completion) remaining
        (slice.kernel type)).expect (fun history => utility history who) := by
    calc
      _ = slice.conditionalPayoff base remaining (fun h => utility h who) target type :=
        slice.completeZeroReach_conditionalPayoff hrecall base completion remaining
          (fun h => utility h who) target type opponents
      _ ≤ slice.infoValue fallback remaining (fun h => utility h who) base type :=
        slice.conditionalPayoff_le_infoValue hrecall fallback remaining
          (fun h => utility h who) base type target
      _ = _ := actual.symm
  unfold conditionalOracleValue cfrDLeafGain
  rw [FinDist.expect_sub]
  apply sub_nonpos.mpr
  simpa only [TypeBeliefSlice.conditionalPayoff, PublicBelief.continuationLaw,
    FinDist.expect_bind, kernel] using better

end GameTheory.ReBeL
