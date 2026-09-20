/-
# Restoring a searched prefix without losing a continuation contract

The depth driver always restores its current trunk. A zero-own-reach
completion may have changed irrelevant decisions before the cut, so its
profile need not be definitionally equal to the driver's profile. These
lemmas transport the full conditional deviation contract through that clamp.
-/

import GameTheory.Analysis.ReBeL.CFRDLeafContract
import GameTheory.Analysis.ReBeL.CFRDPBSOracle
import GameTheory.Analysis.ReBeL.CFRDQuerySupport

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι]

/-- At and after a cut root the restored trunk is never consulted. -/
theorem cfrDDepthProfile_continuation_atCut (clock : ObservationClock M)
    (trunk continuation : Profile M.behavioralSignature) (cut fuel : Nat)
    (history : E.History) (atCut : history.trace.length = cut) :
    M.runBehavioralFrom (cfrDDepthProfile M clock cut trunk continuation) fuel history =
      M.runBehavioralFrom continuation fuel history := by
  apply M.runBehavioralFrom_congr
  intro later reaches _ who
  have after : ¬ clock.depth who (M.infoOf who later.trace) < cut := by
    rw [clock.correct]
    have monotone := reaches.trace_length_le
    omega
  simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_neg after]

variable [DecidableEq ι]

/-- The same equality holds for every complete unilateral behavioral deviation. -/
theorem cfrDDepthProfile_deviation_atCut (clock : ObservationClock M)
    (trunk continuation : Profile M.behavioralSignature) (cut fuel : Nat)
    (history : E.History) (atCut : history.trace.length = cut)
    (who : ι) (target : M.BehavioralPolicy who) :
    M.runBehavioralFrom
        (Profile.update (cfrDDepthProfile M clock cut trunk continuation) who target)
        fuel history =
      M.runBehavioralFrom (Profile.update continuation who target) fuel history := by
  apply M.runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
    have after : ¬ clock.depth player (M.infoOf player later.trace) < cut := by
      rw [clock.correct]
      have monotone := reaches.trace_length_le
      omega
    simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_neg after]

variable [∀ who info, Fintype (M.Choice who info)]

/-- Every unilateral prefix reference is computed from the trunk alone. -/
theorem cfrDDepthProfile_referenceLaw (clock : ObservationClock M)
    (trunk continuation : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι) (cut : Nat) :
    unilateralReferenceLaw M (cfrDDepthProfile M clock cut trunk continuation)
        fallback who cut = unilateralReferenceLaw M trunk fallback who cut := by
  unfold unilateralReferenceLaw
  apply runBehavioral_eq_of_before_depth M clock
  intro player info before
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
    simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_pos before]

/-- Restoring the trunk preserves the exact same local loss allowance if the
continuation has the same unilateral prefix reference. Only supported live
fibers matter; early terminal histories cannot masquerade as live cut roots. -/
theorem cfrDDepthProfile_leafOptimal (clock : ObservationClock M)
    (trunk continuation : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι) (payoff : E.History → ℝ)
    (cut remaining : Nat) (loss : ℝ)
    (prefix : unilateralReferenceLaw M continuation fallback who cut =
      unilateralReferenceLaw M trunk fallback who cut)
    (optimal : CFRDLeafOptimal M continuation fallback who payoff cut remaining loss) :
    CFRDLeafOptimal M (cfrDDepthProfile M clock cut trunk continuation)
      fallback who payoff cut remaining loss := by
  intro target info sampled
  have reference : unilateralReferenceLaw M (cfrDDepthProfile M clock cut trunk continuation)
      fallback who cut = unilateralReferenceLaw M continuation fallback who cut :=
    (cfrDDepthProfile_referenceLaw M clock trunk continuation fallback who cut).trans prefix.symm
  rw [reference] at sampled ⊢
  have equal : conditionalOracleValue (unilateralReferenceLaw M continuation fallback who cut)
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))
      (cfrDLeafGain M (cfrDDepthProfile M clock cut trunk continuation) who target payoff remaining)
      (info, true) =
      conditionalOracleValue (unilateralReferenceLaw M continuation fallback who cut)
        (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))
        (cfrDLeafGain M continuation who target payoff remaining) (info, true) := by
    unfold conditionalOracleValue
    apply FinDist.expect_congr
    intro history reached
    have original := cfrD_conditional_support_source _ _ _ sampled history reached
    have live : cfrDCutLive remaining history = true := congrArg Prod.snd
      (conditionalOracle_support _ _ _ sampled history reached)
    have nonterminal : ¬ E.terminal history.state :=
      (show remaining ≠ 0 ∧ ¬ E.terminal history.state from by
        simpa only [cfrDCutLive, decide_eq_true_eq] using live).2
    have atCut : history.trace.length = cut := by
      rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
          (Profile.update continuation who (uniformLegalPolicy M who (fallback who)))
          cut E.initHistory history original with stopped | depth
      · exact (nonterminal stopped).elim
      · simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
          Nat.zero_add] using depth
    unfold cfrDLeafGain
    rw [cfrDDepthProfile_deviation_atCut M clock trunk continuation cut remaining history atCut,
      cfrDDepthProfile_continuation_atCut M clock trunk continuation cut remaining history atCut]
  exact equal.le.trans (optimal target info sampled)

end GameTheory.ReBeL
