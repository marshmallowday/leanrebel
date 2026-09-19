/-
# Constructed public re-solving at a genuinely live cut

In the two-stage hidden-type game the first round is searched and the second
round is still live. A public resolver recomputes the fair continuation.
Its replacement contract is derived from the canonical continuation law for
EVERY opposing behavioral policy, not assumed as a root-security certificate.
-/

import GameTheory.Analysis.ReBeL.CFRDResolveSafety
import GameTheory.Analysis.ReBeL.Examples.CFRDLiveControl

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Finite legal histories for the public re-solving control. -/
local instance liveResolveHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior
/-- Decidable equality for the proof-only information-state interface. -/
local instance liveResolveInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _
/-- Explicitly finite canonical legal menus for the re-solving control. -/
local instance liveResolveChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

variable {K : Type*}

/-- The selected sequence is the actual coupled live-cut CFR-D solver. -/
def liveResolvePlays (index : K → Nat) : K → Profile (model fullPrior).behavioralSignature :=
  fun iteration => cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff
    2 1 liveControlOracle (index iteration)

/-- This game has the same solved fair continuation at every public cut.
The resolver's interface has no access to the unknown opposing policy. -/
def livePublicResolver (K : Type*) : CarriedPublicResolver (model fullPrior) K :=
  fun _ _ _ => FinDist.pure liveFairContinuation

/-- Re-solving does not alter the actual second-round law against any
opponent. Only the focal policy is replaced; the opponent is never reset. -/
theorem liveResolve_second_run (n : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (x y a b : Bool) :
    (model fullPrior).runBehavioralFrom
        (Profile.update unknown who
          (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff
            2 1 liveControlOracle n who)) 1 (decode (.second x y a b)) =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (liveFairContinuation who))
        1 (decode (.second x y a b)) := by
  have laws : liveSecondLaw
      (Profile.update unknown who
        (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff
          2 1 liveControlOracle n who)) x y a b =
      liveSecondLaw (Profile.update unknown who (liveFairContinuation who)) x y a b := by
    funext player
    unfold liveSecondLaw
    by_cases same : player = who
    · subst player
      rw [Profile.update_same, Profile.update_same, liveControl_second_policy]
    · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
  rw [liveSecond_run, liveSecond_run, laws]

/-- At each genuine live history the actual public resolver incurs zero
loss, independently of hidden types, earlier actions, and the unknown policy. -/
theorem liveResolve_second_loss (index : K → Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (iteration : K) (x y a b : Bool) :
    privateResolvedLoss (model fullPrior) (liveResolvePlays index) (livePublicResolver K)
      unknown who 2 1 (cfrPayoff who) iteration (decode (.second x y a b)) = 0 := by
  have live : cfrDCutLive 1 (decode (.second x y a b)) = true := by
    simp only [cfrDCutLive, decide_eq_true_eq]
    exact ⟨by decide, fun impossible => impossible⟩
  have tail : carriedResolvedTail (model fullPrior) (livePublicResolver K) unknown who 1
      (privateIterationState (model fullPrior) (liveResolvePlays index) 2 iteration
        (decode (.second x y a b))) =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (liveFairContinuation who))
        1 (decode (.second x y a b)) := by
    unfold carriedResolvedTail
    rw [if_pos (show cfrDCutLive 1
      (privateIterationState (model fullPrior) (liveResolvePlays index) 2 iteration
        (decode (.second x y a b))).history = true from live)]
    exact FinDist.pure_bind _ _
  unfold privateResolvedLoss
  rw [tail]
  exact sub_eq_zero.mpr (congrArg (fun law => law.expect (cfrPayoff who))
    (liveResolve_second_run (index iteration) unknown who x y a b))

/-- The conditional comparison is proved under the dominating opponent
reference, including histories that have zero probability in the search model. -/
theorem livePublicResolver_local (index : K → Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who opponent : Player) :
    CFRDResolverLocal (model fullPrior) (liveResolvePlays index) (livePublicResolver K)
      cfrFallback unknown who opponent 2 1 (cfrPayoff who) 0 := by
  apply CFRDResolverLocal_of_pointwise
  intro iteration history reached live
  have not_terminal : ¬ (protocol fullPrior).terminal history.state := by
    have parts : (1 : Nat) ≠ 0 ∧ ¬ (protocol fullPrior).terminal history.state := by
      simpa only [cfrDCutLive, decide_eq_true_eq] using live
    exact parts.2
  have depth : history.trace.length = 2 := by
    rcases (model fullPrior).terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      _ 2 (protocol fullPrior).initHistory history reached with terminal | length
    · exact False.elim (not_terminal terminal)
    · exact length
  obtain ⟨row, rfl⟩ := decode_surjective history
  cases row with
  | initial => have bad : (0 : Nat) = 2 := depth; omega
  | drawn x y => have bad : (1 : Nat) = 2 := depth; omega
  | second x y a b => rw [liveResolve_second_loss]
  | finished x y a b c d => have bad : (3 : Nat) = 2 := depth; omega

/-- A constructed positive control for actual carried-prefix re-solving:
no additional loss occurs against any seed-blind unknown opponent. -/
theorem livePublicResolver_no_loss (seed : FinDist K) (index : K → Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who opponent : Player)
    (different : opponent ≠ who) :
    (privateCarriedContinue (model fullPrior) seed (liveResolvePlays index)
      unknown who 2 1).expect (cfrPayoff who) ≤
    (privateCarriedResolve (model fullPrior) seed (liveResolvePlays index)
      (livePublicResolver K) unknown who 2 1).expect (cfrPayoff who) := by
  have bound := privateCarriedResolve_loss_le (model fullPrior) (perfectRecall fullPrior)
    seed (liveResolvePlays index) (livePublicResolver K) cfrFallback unknown who opponent
    different 2 1 (cfrPayoff who) 0 (le_refl _)
    (livePublicResolver_local index unknown who opponent)
  linarith

/-- The complete positive example retains finite-time error while both the
value accuracy and continuation/re-solving loss contracts are proved at zero. -/
theorem livePublicResolver_security
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun history who => cfrPayoff who history)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (who opponent : Player)
    (different : opponent ≠ who) (t : Nat) [NeZero t] :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff who) -
      (cfrDDepthFiniteConstant (model fullPrior) decisionClock cfrFallback 2 1 2 0 +
        cfrDDepthFiniteConstant (model fullPrior) decisionClock cfrFallback 2 1 2 1) /
          Real.sqrt t ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t)
        (liveResolvePlays (fun n : Fin t => n.val)) (livePublicResolver (Fin t))
        unknown who 2 1).expect (cfrPayoff who) := by
  simpa only [mul_zero, zero_add, add_zero] using
    cfrDDepth_resolved_security (model fullPrior) decisionClock (perfectRecall fullPrior)
      cfrFallback cfrPayoff (cumulative_zeroSum fullPrior) 2 1 liveControlOracle 2 0 0
      (by norm_num) (le_refl _) (le_refl _) cfrPayoff_abs_le_two
      liveControl_accurate liveControl_leaf_optimal reference equilibrium unknown who opponent
      different t (livePublicResolver (Fin t)) 0 (le_refl _)
      (livePublicResolver_local (fun n : Fin t => n.val) unknown who opponent)

end GameTheory.ReBeL.Examples.HiddenTypes
