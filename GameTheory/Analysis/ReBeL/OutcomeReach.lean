/-
# Terminal-aware outcome probabilities from own reach

The probability at a requested horizon equals the canonical probability at a
history's own depth, provided that history is at the cut or already terminal.
This connects realization identities for own reach to complete history laws,
including early absorption and branches of zero current probability.
-/

import GameTheory.ReBeL.ReachFactorization

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι]

/-- A supported behavioral continuation is an actual legal continuation,
not an arbitrary history chosen by a probability representation. -/
theorem behavioral_support_reaches (strategy : Profile M.behavioralSignature) :
    ∀ (fuel : ℕ) (start target : E.History),
      target ∈ (M.runBehavioralFrom strategy fuel start).support →
        E.ReachesWithin fuel start target := by
  intro fuel
  induction fuel with
  | zero =>
      intro start target htarget
      rw [InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, FinDist.mem_support_pure] at htarget
      subst target
      exact .refl 0 start
  | succ fuel ih =>
      intro start target htarget
      by_cases hterm : E.terminal start.state
      · rw [M.runBehavioralFrom_of_terminal strategy (fuel + 1) hterm,
          FinDist.mem_support_pure] at htarget
        subst target
        exact .refl (fuel + 1) start
      · rw [M.runBehavioralFrom_succ_of_not_terminal strategy fuel hterm,
          FinDist.support_bind] at htarget
        simp only [Set.mem_iUnion] at htarget
        obtain ⟨draw, _hdraw, hinner⟩ := htarget
        rw [FinDist.support_bindOnSupport] at hinner
        simp only [Set.mem_iUnion] at hinner
        obtain ⟨reached, realized, hrest⟩ := hinner
        exact .step draw.1 draw.2 realized
          (ih (start.extend draw.2 realized) target hrest)

omit [Fintype ι] in
/-- A legal continuation can add at most one transition per unit of fuel. -/
theorem reaches_depth_upper {fuel : ℕ} {start target : E.History}
    (hreach : E.ReachesWithin fuel start target) :
    target.trace.length ≤ start.trace.length + fuel := by
  induction hreach with
  | refl fuel history => omega
  | step joint isLegal realized rest ih =>
      simp only [ExecutionProtocol.History.extend, ExecutionProtocol.Trace.length] at ih
      omega

/-- The canonical root runner never puts mass on a history beyond its cut. -/
theorem behavioral_support_depth (strategy : Profile M.behavioralSignature)
    (fuel : ℕ) (history : E.History)
    (hsupport : history ∈ (M.runBehavioral strategy fuel).support) :
    history.trace.length ≤ fuel := by
  have h := reaches_depth_upper (behavioral_support_reaches M strategy fuel
    E.initHistory history hsupport)
  simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
    Nat.zero_add] using h

/-- Once a terminal history has been reached, increasing the root horizon
preserves its probability. Other terminal histories remain distinct. -/
theorem terminal_probability_stable (strategy : Profile M.behavioralSignature)
    (history : E.History) (hterm : E.terminal history.state) (fuel : ℕ)
    (hcut : history.trace.length ≤ fuel) :
    (M.runBehavioral strategy fuel).prob history =
      M.historyReachProbability strategy history := by
  classical
  have hsplit : M.runBehavioral strategy fuel =
      (M.runBehavioral strategy history.trace.length).bind
        (M.runBehavioralFrom strategy (fuel - history.trace.length)) := by
    calc
      _ = M.runBehavioral strategy
          (history.trace.length + (fuel - history.trace.length)) := by
        rw [Nat.add_sub_of_le hcut]
      _ = _ := M.runBehavioralFrom_add strategy _ _ E.initHistory
  rw [hsplit, FinDist.prob_bind]
  have hkernel : ∀ prior ∈ (M.runBehavioral strategy history.trace.length).support,
      (M.runBehavioralFrom strategy (fuel - history.trace.length) prior).prob history =
        if history = prior then 1 else 0 := by
    intro prior hprior
    by_cases hequal : history = prior
    · subst prior
      simp [M.runBehavioralFrom_of_terminal strategy _ hterm]
    · by_cases hpriorTerminal : E.terminal prior.state
      · simp [M.runBehavioralFrom_of_terminal strategy _ hpriorTerminal,
          FinDist.prob_pure_eq_ite, hequal, Ne.symm hequal]
      · have hdepth : prior.trace.length = history.trace.length := by
          rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
              strategy history.trace.length E.initHistory prior hprior with ht | hl
          · exact False.elim (hpriorTerminal ht)
          · simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
              Nat.zero_add] using hl
        have hzero :
            (M.runBehavioralFrom strategy (fuel - history.trace.length) prior).prob
              history = 0 := by
          apply FinDist.prob_eq_zero_iff.mpr
          intro hsupport
          have hreach := behavioral_support_reaches M strategy
            (fuel - history.trace.length) prior history hsupport
          exact hequal (hreach.eq_of_trace_length_eq hdepth)
        simp [hzero, hequal]
  calc
    _ = (M.runBehavioral strategy history.trace.length).expect
        (fun prior => if history = prior then (1 : ℝ) else 0) := by
      apply FinDist.expect_congr
      exact hkernel
    _ = (M.runBehavioral strategy history.trace.length).prob history := by
      simpa using FinDist.expect_ite_eq
        (M.runBehavioral strategy history.trace.length) history (1 : ℝ)
    _ = _ := rfl

/-- The complete outcome law has a strategy-independent cut/terminal mask.
A history's own-depth reach alone would incorrectly retain unfinished prefixes. -/
theorem run_probability_at_cut (strategy : Profile M.behavioralSignature)
    (fuel : ℕ) (history : E.History) :
    (M.runBehavioral strategy fuel).prob history =
      if history.trace.length ≤ fuel ∧
          (history.trace.length = fuel ∨ E.terminal history.state) then
        M.historyReachProbability strategy history else 0 := by
  classical
  by_cases hcut : history.trace.length ≤ fuel ∧
      (history.trace.length = fuel ∨ E.terminal history.state)
  · rw [if_pos hcut]
    rcases hcut.2 with hequal | hterm
    · rw [← hequal]
      rfl
    · exact terminal_probability_stable M strategy history hterm fuel hcut.1
  · rw [if_neg hcut]
    apply FinDist.prob_eq_zero_iff.mpr
    intro hsupport
    apply hcut
    refine ⟨behavioral_support_depth M strategy fuel history hsupport, ?_⟩
    rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        strategy fuel E.initHistory history hsupport with hterm | hdepth
    · exact Or.inr hterm
    · left
      simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
        Nat.zero_add] using hdepth

/-- At a fixed horizon the factor not controlled by players is chance reach
with the canonical terminal/cut mask. It has no strategy argument. -/
def outcomeChanceWeight (fuel : ℕ) (history : E.History) : ℝ := by
  classical
  exact if history.trace.length ≤ fuel ∧
      (history.trace.length = fuel ∨ E.terminal history.state) then
    chanceReach history.trace else 0

/-- Full history probabilities factor into the masked chance weight and all
players' actual own reaches, even for early terminal outcomes. -/
theorem run_probability_factorization (strategy : Profile M.behavioralSignature)
    (fuel : ℕ) (history : E.History) :
    (M.runBehavioral strategy fuel).prob history =
      outcomeChanceWeight fuel history *
        ∏ who, M.playerReachProbability strategy who history.trace := by
  classical
  rw [run_probability_at_cut M strategy fuel history]
  unfold outcomeChanceWeight
  split
  · exact historyReach_factorization M strategy history.trace
  · simp

/-- Agreement of all players' full own-reach functions implies agreement of
complete outcome laws, not merely equal payoffs under one selected observable. -/
theorem run_eq_of_ownReach_eq (first second : Profile M.behavioralSignature)
    (hown : ∀ who (history : E.History),
      M.playerReachProbability first who history.trace =
        M.playerReachProbability second who history.trace) (fuel : ℕ) :
    M.runBehavioral first fuel = M.runBehavioral second fuel := by
  apply FinDist.ext_of_prob
  intro history
  rw [run_probability_factorization M, run_probability_factorization M]
  simp_rw [hown]

end GameTheory.ReBeL
