/-
# Full-game regret from the actual depth-limited value solver

Trunk regret comes from the numerical recurrence. The remaining difference
comes from local conditional continuation optimality. Their sum bounds every
complete behavioral deviation, including deviations that change the cut PBS.
The two oracle errors are explicit and the finite-iteration term is retained.
-/

import GameTheory.Analysis.ReBeL.CFRDTrunkRegret
import GameTheory.Analysis.ReBeL.CFRDLeafContract
import GameTheory.Analysis.ReBeL.CFRNash

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- The root bound is proved for the actual coupled learner and every complete
behavioral deviation. Its assumptions contain neither root regret, a solver
output certificate, nor a separate hypothetical sequence of strategies. -/
theorem cfrDDepth_root_cumulative_le (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (bound error loss : ℝ) (hbound : 0 ≤ bound) (herror : 0 ≤ error) (hloss : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (who : ι) (target : M.BehavioralPolicy who) (t : Nat) :
    (∑ n ∈ Finset.range t,
      ((M.runBehavioral (Profile.update
          (cfrDDepthPlay M clock fallback payoff cut remaining oracle n) who target)
          (cut + remaining)).expect (payoff who) -
        (M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
          (cut + remaining)).expect (payoff who))) ≤
      cfrDTrunkBudget M clock fallback cut remaining bound error who t + (t : ℝ) * loss := by
  let plays := cfrDDepthPlay M clock fallback payoff cut remaining oracle
  let prefix (n : Nat) :=
    (M.runBehavioral (Profile.update (plays n) who
      (cfrDPrefixPolicy M clock (plays n) who target cut)) (cut + remaining)).expect (payoff who) -
      (M.runBehavioral (plays n) (cut + remaining)).expect (payoff who)
  have hstep (n : Nat) :
      (M.runBehavioral (Profile.update (plays n) who target) (cut + remaining)).expect
          (payoff who) - (M.runBehavioral (plays n) (cut + remaining)).expect (payoff who) ≤
        prefix n + loss := by
    have htail := cfrDLeafOptimal_tail_gain_le M clock hrecall (plays n) fallback who target
      (payoff who) cut remaining loss hloss (optimal n who)
    dsimp only [prefix]
    linarith
  have htrunk := cfrDDepth_prefix_cumulative_le M clock hrecall fallback payoff cut remaining
    oracle bound error hbound herror bounded accurate who target t
  calc
    _ ≤ ∑ n ∈ Finset.range t, (prefix n + loss) :=
      Finset.sum_le_sum fun n _ => hstep n
    _ = (∑ n ∈ Finset.range t, prefix n) + (t : ℝ) * loss := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ _ := add_le_add htrunk (le_refl _)

/-- Explicit mean allowance for one player. Numerical value error, local
continuation error, payoff size and the complete searched schedule stay visible. -/
def cfrDDepthMeanBudget (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (cut remaining : Nat) (bound error loss : ℝ) (who : ι) (t : Nat) : ℝ :=
  cfrDTrunkBudget M clock fallback cut remaining bound error who t / t + loss

/-- Uniform private iteration sampling has the proved mean root-regret bound.
The zero-round case is excluded because it has no uniform iteration law. -/
theorem cfrDDepth_mean_regret_le (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (bound error loss : ℝ) (hbound : 0 ≤ bound) (herror : 0 ≤ error) (hloss : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (who : ι) (target : M.BehavioralPolicy who) (t : Nat) [NeZero t] :
    (cfrIterationLaw t).expect (fun n =>
      (M.runBehavioral (Profile.update
        (cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val) who target)
        (cut + remaining)).expect (payoff who) -
      (M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
        (cut + remaining)).expect (payoff who)) ≤
      cfrDDepthMeanBudget M clock fallback cut remaining bound error loss who t := by
  rw [cfrIterationLaw_expect]
  have positive : 0 < (t : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne t))
  have nonzero : (t : ℝ) ≠ 0 := ne_of_gt positive
  calc
    _ ≤ (cfrDTrunkBudget M clock fallback cut remaining bound error who t +
        (t : ℝ) * loss) / t :=
      div_le_div_of_nonneg_right (cfrDDepth_root_cumulative_le M clock hrecall fallback payoff
        cut remaining oracle bound error loss hbound herror hloss bounded accurate optimal
        who target t) positive.le
    _ = _ := by
      unfold cfrDDepthMeanBudget
      field_simp

end GameTheory.ReBeL
