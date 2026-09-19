/-
# Local continuation contracts and their actual root contribution

Numerical value accuracy and continuation optimality are different premises.
The latter is imposed only on conditional continuation games at live cut
information states. It is not a root-regret certificate. Counterfactual
completion is explicit at zero factual own reach. A normalized density then
transfers this local contract to every legal unilateral prefix deviation.
-/

import GameTheory.Analysis.ReBeL.CFRDPrefix

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- A conditional upper bound transfers under any normalized information-local
density. No worst-case inverse factual reach factor is needed. -/
theorem conditionalOracle_reweight_le {Leaf Info : Type*}
    (reference alternative : FinDist Leaf) (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (value : Leaf → ℝ) (bound : ℝ)
    (bounded : ∀ info ∈ (reference.map observe).support,
      conditionalOracleValue reference observe value info ≤ bound) :
    alternative.expect value ≤ bound := by
  rw [← conditionalOracle_reweight_exact reference alternative observe weight density value]
  apply FinDist.expect_le_of_forall
  intro info reached
  apply bounded
  rw [FinDist.support_map] at reached ⊢
  obtain ⟨leaf, sampled, same⟩ := reached
  exact ⟨leaf, informationReweight_support reference alternative observe weight density sampled,
    same⟩

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Gain from changing only the future legal behavioral policy at a cut leaf. -/
def cfrDLeafGain (base : Profile M.behavioralSignature) (who : ι)
    (target : M.BehavioralPolicy who) (payoff : E.History → ℝ) (remaining : Nat)
    (history : E.History) : ℝ :=
  (M.runBehavioralFrom (Profile.update base who target) remaining history).expect payoff -
    (M.runBehavioralFrom base remaining history).expect payoff

/-- A stopped leaf admits no continuation deviation gain, independently of
what either the oracle or an arbitrary alternative policy would have done. -/
theorem cfrDLeafGain_stopped (base : Profile M.behavioralSignature) (who : ι)
    (target : M.BehavioralPolicy who) (payoff : E.History → ℝ) (remaining : Nat)
    (history : E.History) (stopped : cfrDCutLive remaining history ≠ true) :
    cfrDLeafGain M base who target payoff remaining history = 0 := by
  unfold cfrDLeafGain
  rw [cfrDCutValue_stopped M _ payoff remaining history stopped,
    cfrDCutValue_stopped M base payoff remaining history stopped, sub_self]

/-- Conditioning on a stopped leaf cannot introduce a continuation gain. -/
theorem cfrDLeafGain_conditional_stopped (law : FinDist E.History)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (remaining : Nat) (info : M.InfoState who)
    (sampled : (info, false) ∈ (law.map
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))).support) :
    conditionalOracleValue law
        (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
        (cfrDLeafGain M base who target payoff remaining) (info, false) = 0 := by
  unfold conditionalOracleValue
  calc
    _ = (law.condOnFibre
        (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
        (info, false)).expect (fun _ => (0 : ℝ)) := by
      apply FinDist.expect_congr
      intro history reached
      have same := congrArg Prod.snd (conditionalOracle_support law
        (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))
        (info, false) sampled history reached)
      apply cfrDLeafGain_stopped
      rw [show cfrDCutLive remaining history = false from same]
      decide
    _ = 0 := FinDist.expect_const _ _

variable [∀ who info, Fintype (M.Choice who info)]

/-- A local approximate best-response contract for the supplied continuation.
It quantifies over complete information-local future policies, not hidden-state
choices. A positive reference fiber can matter even at zero factual own reach.
The loss here is separate from prediction error and is never silently dropped. -/
def CFRDLeafOptimal (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (payoff : E.History → ℝ)
    (cut remaining : Nat) (loss : ℝ) : Prop :=
  ∀ (target : M.BehavioralPolicy who) (info : M.InfoState who),
    (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))).support →
    conditionalOracleValue (unilateralReferenceLaw M base fallback who cut)
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
      (cfrDLeafGain M base who target payoff remaining) (info, true) ≤ loss

/-- Local continuation optimality controls the remaining root difference
under every unilateral prefix. The actual cut law is not replaced by a guessed
posterior, and no positive factual own-reach premise is imposed. -/
theorem cfrDLeafOptimal_tail_gain_le (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (target : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (cut remaining : Nat) (loss : ℝ) (nonneg : 0 ≤ loss)
    (optimal : CFRDLeafOptimal M base fallback who payoff cut remaining loss) :
    (M.runBehavioral (Profile.update base who target) (cut + remaining)).expect payoff -
        (M.runBehavioral (Profile.update base who
          (cfrDPrefixPolicy M clock base who target cut)) (cut + remaining)).expect payoff ≤
      loss := by
  rw [cfrDPrefix_tail_gain M clock base who target payoff cut remaining]
  apply conditionalOracle_reweight_le (unilateralReferenceLaw M base fallback who cut)
    (M.runBehavioral (Profile.update base who target) cut)
    (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
    (fun tag : M.InfoState who × Bool => unilateralDensity M base fallback who target tag.1)
    (unilateralReference_density M hrecall base fallback who target cut)
    (cfrDLeafGain M base who target payoff remaining) loss
  rintro ⟨info, flag⟩ sampled
  cases flag
  · rw [cfrDLeafGain_conditional_stopped M _ base who target payoff remaining info sampled]
    exact nonneg
  · exact optimal target info sampled

/-- At zero remaining fuel the local optimality contract is derived, rather
than supplied. This is the exact-oracle/full-search boundary used in controls. -/
theorem cfrDLeafOptimal_zero_remaining (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (payoff : E.History → ℝ) (cut : Nat) :
    CFRDLeafOptimal M base fallback who payoff cut 0 0 := by
  intro target info _sampled
  have zero : cfrDLeafGain M base who target payoff 0 = fun _ => (0 : ℝ) := by
    funext history
    apply cfrDLeafGain_stopped
    rw [cfrDCutLive_zero]
    decide
  unfold conditionalOracleValue
  rw [zero, FinDist.expect_const]

variable [∀ who, DecidableEq (M.InfoState who)]

/-- The local continuation contract at each round of this very solver. -/
def CFRDDepthLeafOptimal (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (loss : ℝ) : Prop :=
  ∀ n who, CFRDLeafOptimal M (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
    fallback who (payoff who) cut remaining loss

/-- An ideal reference value oracle computed from a supplied legal continuation.
It is a specification/reference oracle, not a claim of cheap continuation
solving. The numerical trunk driver still performs only stopped execution. -/
def cfrDExactValueOracle (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ) (cut remaining : Nat)
    (continuation : Nat → Profile M.behavioralSignature → Profile M.behavioralSignature) :
    CFRDValueOracle M := fun n strategy =>
  let next := continuation n strategy
  let base := cfrDDepthProfile M clock cut strategy next
  { continuation := next
    prediction := fun who info =>
      conditionalOracleValue (unilateralReferenceLaw M base fallback who cut)
        (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
        (fun history => (M.runBehavioralFrom base remaining history).expect (payoff who))
        (info, true) }

/-- The reference value oracle satisfies its numerical contract exactly for
the actual coupled recurrence, not for an independently supplied play trace. -/
theorem cfrDExactValueOracle_accurate (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ) (cut remaining : Nat)
    (continuation : Nat → Profile M.behavioralSignature → Profile M.behavioralSignature) :
    CFRDDepthAccurate M clock fallback payoff cut remaining
      (cfrDExactValueOracle M clock fallback payoff cut remaining continuation) 0 := by
  intro n who info _sampled
  let base := cfrDDepthPlay M clock fallback payoff cut remaining
    (cfrDExactValueOracle M clock fallback payoff cut remaining continuation) n
  let value := conditionalOracleValue (unilateralReferenceLaw M base fallback who cut)
    (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
    (fun history => (M.runBehavioralFrom base remaining history).expect (payoff who)) (info, true)
  change |value - value| ≤ 0
  simp only [sub_self, abs_zero, le_refl]

end GameTheory.ReBeL
