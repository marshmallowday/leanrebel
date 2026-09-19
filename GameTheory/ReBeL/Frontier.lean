/-
# Public stopping frontiers and exact continuation factorization

The stopped process uses the canonical behavioral runner, not a second game
semantics. A frontier is observable from the public trace. Each stopped leaf
retains its unused fuel, so a terminal, a search cut and exhausted fuel are
not silently identified. No continuation correctness is stored as a field.
-/

import GameTheory.ReBeL.PublicSubgame

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- A stopping decision made using public observations only. -/
abbrev PublicFrontier (S : InfoSignals E) := List S.PublicSignal → Bool

/-- Equal full action-observation histories receive the same public stopping decision. -/
theorem publicFrontier_info_closed (S : InfoSignals E) (frontier : PublicFrontier S)
    (who : ι) (first second : E.History)
    (same : (fullSignals S).infoOf who first.trace =
      (fullSignals S).infoOf who second.trace) :
    frontier (publicTrace S first.trace) = frontier (publicTrace S second.trace) := by
  rw [publicTrace_eq_of_infoOf_eq S who first.trace second.trace same]

variable [Fintype ι] (M : InformationModel E)

/-- Stop at the first public frontier or true terminal; retain unused continuation fuel. -/
def frontierRun (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) : Nat → E.History → FinDist (Nat × E.History)
  | 0, history => FinDist.pure (0, history)
  | fuel + 1, history => by
      classical
      exact if E.terminal history.state ∨ frontier (publicTrace M.toInfoSignals history.trace)
        then FinDist.pure (fuel + 1, history)
        else (M.runBehavioralFrom profile 1 history).bind (frontierRun frontier profile fuel)

@[simp]
theorem frontierRun_zero (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (history : E.History) :
    frontierRun M frontier profile 0 history = FinDist.pure (0, history) := rfl

/-- A real terminal is absorbing even when the public frontier has not been reached. -/
theorem frontierRun_terminal (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (fuel : Nat) (history : E.History)
    (terminal : E.terminal history.state) :
    frontierRun M frontier profile fuel history = FinDist.pure (fuel, history) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [frontierRun, if_pos (Or.inl terminal)]

/-- A public cut stops search without asserting that the game has terminated. -/
theorem frontierRun_cut (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (fuel : Nat) (history : E.History)
    (cut : frontier (publicTrace M.toInfoSignals history.trace) = true) :
    frontierRun M frontier profile fuel history = FinDist.pure (fuel, history) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [frontierRun, if_pos (Or.inr cut)]

/-- Resuming each stopped leaf with its unused fuel exactly recovers the full runner. -/
theorem frontierRun_bind_continuation (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (fuel : Nat) (history : E.History) :
    (frontierRun M frontier profile fuel history).bind
        (fun leaf => M.runBehavioralFrom profile leaf.1 leaf.2) =
      M.runBehavioralFrom profile fuel history := by
  classical
  induction fuel generalizing history with
  | zero => simp only [frontierRun, FinDist.pure_bind]
  | succ fuel ih =>
      by_cases halt : E.terminal history.state ∨
        frontier (publicTrace M.toInfoSignals history.trace)
      · simp only [frontierRun, if_pos halt, FinDist.pure_bind]
      · rw [frontierRun, if_neg halt, FinDist.bind_bind]
        calc
          _ = (M.runBehavioralFrom profile 1 history).bind
                (M.runBehavioralFrom profile fuel) :=
            FinDist.bind_congr fun next _ => ih next
          _ = _ := by simpa only [Nat.add_comm] using
            (M.runBehavioralFrom_add profile 1 fuel history).symm

/-- Every stopped outcome is fuel-exhausted, terminal, or at the chosen public frontier. -/
theorem frontierRun_support (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (fuel : Nat) (history : E.History)
    (leaf : Nat × E.History)
    (reached : leaf ∈ (frontierRun M frontier profile fuel history).support) :
    leaf.1 = 0 ∨ E.terminal leaf.2.state ∨
      frontier (publicTrace M.toInfoSignals leaf.2.trace) = true := by
  classical
  induction fuel generalizing history with
  | zero =>
      rw [frontierRun_zero, FinDist.mem_support_pure] at reached
      subst leaf
      exact Or.inl rfl
  | succ fuel ih =>
      by_cases halt : E.terminal history.state ∨
        frontier (publicTrace M.toInfoSignals history.trace)
      · rw [frontierRun, if_pos halt, FinDist.mem_support_pure] at reached
        subst leaf
        exact Or.inr halt
      · rw [frontierRun, if_neg halt, FinDist.support_bind] at reached
        obtain ⟨next, _, tail⟩ := Set.mem_iUnion₂.mp reached
        exact ih next tail

/-- True terminal rewards and exhausted-fuel rewards do not use a learned value. -/
def frontierLeafValue (payoff : E.History → ℝ) (prediction : Nat → E.History → ℝ)
    (leaf : Nat × E.History) : ℝ := by
  classical
  exact if leaf.1 = 0 ∨ E.terminal leaf.2.state then payoff leaf.2
    else prediction leaf.1 leaf.2

/-- Back up a leaf-value oracle through the actual stopped history law. -/
def frontierValue (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (payoff : E.History → ℝ)
    (prediction : Nat → E.History → ℝ) (fuel : Nat) (history : E.History) : ℝ :=
  (frontierRun M frontier profile fuel history).expect (frontierLeafValue payoff prediction)

/-- Supplying canonical continuation values makes the stopped backup exact. -/
theorem frontierValue_exact (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (payoff : E.History → ℝ)
    (fuel : Nat) (history : E.History) :
    frontierValue M frontier profile payoff
        (fun remaining next => (M.runBehavioralFrom profile remaining next).expect payoff)
        fuel history = (M.runBehavioralFrom profile fuel history).expect payoff := by
  classical
  unfold frontierValue
  calc
    _ = (frontierRun M frontier profile fuel history).expect
          (fun leaf => (M.runBehavioralFrom profile leaf.1 leaf.2).expect payoff) := by
      apply FinDist.expect_congr
      intro leaf _
      unfold frontierLeafValue
      split_ifs with stopped
      · rcases stopped with exhausted | terminal
        · simp [exhausted, InformationModel.runBehavioralFrom]
        · rw [M.runBehavioralFrom_of_terminal profile leaf.1 terminal, FinDist.expect_pure]
      · rfl
    _ = _ := by rw [← FinDist.expect_bind, frontierRun_bind_continuation]

/-- Pointwise leaf error is not amplified by stochastic backup through the trunk. -/
theorem frontierValue_error (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (payoff : E.History → ℝ)
    (prediction : Nat → E.History → ℝ) (fuel : Nat) (history : E.History)
    (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : ∀ leaf ∈ (frontierRun M frontier profile fuel history).support,
      leaf.1 ≠ 0 → ¬ E.terminal leaf.2.state →
      |prediction leaf.1 leaf.2 -
        (M.runBehavioralFrom profile leaf.1 leaf.2).expect payoff| ≤ error) :
    |frontierValue M frontier profile payoff prediction fuel history -
      (M.runBehavioralFrom profile fuel history).expect payoff| ≤ error := by
  classical
  rw [← frontierValue_exact M frontier profile payoff fuel history]
  unfold frontierValue
  rw [← FinDist.expect_sub]
  apply FinDist.abs_expect_le_of_abs_bound
  intro leaf reached
  unfold frontierLeafValue
  split_ifs with stopped
  · simpa only [sub_self, abs_zero] using nonneg
  · exact accurate leaf reached (fun h => stopped (Or.inl h))
      (fun h => stopped (Or.inr h))

end GameTheory.ReBeL
