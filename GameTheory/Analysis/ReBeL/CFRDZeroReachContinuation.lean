/-
# Zero-own-reach completion from positive conditional roots

The root of this theorem is any legal history, not the initial history.
Only selected players need positive original own reach. Other players may
use arbitrary policies, including complete unilateral deviations. The proof
uses the actual supported joint draws and the canonical continuation runner.
-/

import GameTheory.Analysis.ReBeL.CFRDZeroReachCompletion

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Completing any selected players preserves the entire continuation law
when each selected player's original own reach is nonzero at the root.
No positivity or policy constraint is imposed on the unselected players. -/
theorem cfrDCompleteZeroReach_selected_continuation (hrecall : M.PerfectRecall)
    (base completion unknown : Profile M.behavioralSignature) (selected : Finset ι)
    (fuel : Nat) (history : E.History)
    (positive : ∀ who ∈ selected,
      M.playerReachProbability base who history.trace ≠ 0) :
    M.runBehavioralFrom
        (fun who => if who ∈ selected then cfrDCompleteZeroReach M base completion who
          else unknown who) fuel history =
      M.runBehavioralFrom
        (fun who => if who ∈ selected then base who else unknown who) fuel history := by
  classical
  let first : Profile M.behavioralSignature := fun who =>
    if who ∈ selected then cfrDCompleteZeroReach M base completion who else unknown who
  let second : Profile M.behavioralSignature := fun who =>
    if who ∈ selected then base who else unknown who
  suffices result : ∀ (n : Nat) (root : E.History),
      (∀ who ∈ selected, M.playerReachProbability base who root.trace ≠ 0) →
      M.runBehavioralFrom first n root = M.runBehavioralFrom second n root from
    result fuel history positive
  intro n
  induction n with
  | zero => intro root _; rfl
  | succ n ih =>
      intro root positive
      by_cases terminal : E.terminal root.state
      · rw [M.runBehavioralFrom_of_terminal first (n + 1) terminal,
          M.runBehavioralFrom_of_terminal second (n + 1) terminal]
      · have choices : (fun player => first player (M.infoOf player root.trace)) =
            (fun player => second player (M.infoOf player root.trace)) := by
          funext player
          by_cases member : player ∈ selected
          · simp only [first, second, if_pos member]
            apply cfrDCompleteZeroReach_of_ne
            rw [informationOwnReach_eq_player M hrecall base player root]
            exact positive player member
          · simp only [first, second, if_neg member]
        have joints : M.behavioralJoint first root.trace terminal =
            M.behavioralJoint second root.trace terminal := by
          unfold InformationModel.behavioralJoint
          rw [choices]
        rw [M.runBehavioralFrom_succ_of_not_terminal first n terminal,
          M.runBehavioralFrom_succ_of_not_terminal second n terminal, joints]
        apply FinDist.bind_congr
        intro draw supported
        apply FinDist.bindOnSupport_congr
        intro reached realized
        apply ih
        intro player member
        have product : (∏ i, (second i (M.infoOf i root.trace)).prob
            (M.choicesOfLegal root.trace draw i)) ≠ 0 := by
          rw [← M.behavioralJoint_prob_eq_prod second root.trace terminal draw]
          exact fun zero => (FinDist.prob_eq_zero_iff.mp zero) supported
        have factor : (second player (M.infoOf player root.trace)).prob
            (M.choicesOfLegal root.trace draw player) ≠ 0 := by
          intro zero
          exact product (Finset.prod_eq_zero (Finset.mem_univ player) zero)
        have step : M.playerStepProb base player root.trace draw ≠ 0 := by
          simpa only [InformationModel.playerStepProb, second, if_pos member] using factor
        simpa only [History.extend, InformationModel.playerReachProbability] using
          mul_ne_zero (positive player member) step

/-- At a root with positive own reach for every player, joint zero-reach
completion preserves the canonical continuation law, not just its mean. -/
theorem cfrDCompleteZeroReach_positive_continuation (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (fuel : Nat) (history : E.History)
    (positive : ∀ who, M.playerReachProbability base who history.trace ≠ 0) :
    M.runBehavioralFrom (cfrDCompleteZeroReach M base completion) fuel history =
      M.runBehavioralFrom base fuel history := by
  simpa using cfrDCompleteZeroReach_selected_continuation M hrecall base completion base
    Finset.univ fuel history (fun who _ => positive who)

end GameTheory.ReBeL
