/-
# Exact execution law for the joint-PBS root construction

This uses the canonical randomized history runner on both protocols. A single
administrative draw is followed by exactly the requested original continuation
fuel. Equality is of complete laws, not only one expected utility or on-policy
support. Terminal sampled roots and zero continuation fuel are included.
-/

import GameTheory.Analysis.ReBeL.PBSRootProtocol

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol
open GameTheory.Math.Probability

universe uι us ua
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- Lift an analyst-level randomized chooser; the root is always a no-op.
Information-local behavioral adapters are proved separately. -/
def pbsRootActionLaw (roots : FinDist E.History) (chooser : E.RandomizedChooser) :
    (state : (pbsRootProtocol roots).State) → ¬ (pbsRootProtocol roots).terminal state →
      FinDist {joint // (pbsRootProtocol roots).Legal state joint}
  | none, _ => FinDist.pure ⟨fun _ => none, not_false, fun _ => not_false⟩
  | some history, nonterminal => chooser history nonterminal

/-- Use the original retained history, rather than inventing a new execution semantics. -/
def pbsRootChooser (roots : FinDist E.History) (chooser : E.RandomizedChooser) :
    (pbsRootProtocol roots).RandomizedChooser :=
  fun history nonterminal => pbsRootActionLaw roots chooser history.state nonterminal

/-- Starting after the root draw preserves the full original continuation law. -/
theorem pbsRoot_runFrom_some (roots : FinDist E.History) (chooser : E.RandomizedChooser)
    (fuel : Nat) (original : E.History)
    (trace : (pbsRootProtocol roots).Trace (some original)) :
    ((pbsRootProtocol roots).runRandomizedFor (pbsRootChooser roots chooser) fuel
      ⟨some original, trace⟩).map History.state =
      (E.runRandomizedFor chooser fuel original).map some := by
  induction fuel generalizing original with
  | zero => simp only [runRandomizedFor_zero, FinDist.map_pure]
  | succ fuel ih =>
      by_cases hterminal : E.terminal original.state
      · rw [runRandomizedFor_of_terminal (E := pbsRootProtocol roots)
            (pbsRootChooser roots chooser) (fuel + 1) (h := ⟨some original, trace⟩) hterminal,
          runRandomizedFor_of_terminal chooser (fuel + 1) hterminal]
        simp only [FinDist.map_pure]
      · rw [runRandomizedFor_succ_of_not_terminal (E := pbsRootProtocol roots)
            (pbsRootChooser roots chooser) fuel (h := ⟨some original, trace⟩) hterminal,
          runRandomizedFor_succ_of_not_terminal chooser fuel hterminal]
        simp only [pbsRootChooser, pbsRootActionLaw, FinDist.map_bind, FinDist.map_bindOnSupport]
        apply FinDist.bind_congr
        intro draw _
        let tail : Option E.History → FinDist (Option E.History) := fun next =>
          match next with
          | none => FinDist.pure none
          | some history => (E.runRandomizedFor chooser fuel history).map some
        calc
          _ = ((pbsRootProtocol roots).step (some original) draw).bind tail := by
            apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
            intro next realized
            obtain ⟨target, htarget, rfl⟩ :=
              (pbsRootProtocol_step_support roots original draw next).mp realized
            exact ih (original.extend draw.2 htarget) _
          _ = _ := by
            simp only [pbsRootProtocol, FinDist.bind_bindOnSupport]
            apply FinDist.bindOnSupport_congr
            intro target realized
            rw [FinDist.pure_bind]

/-- One extra fuel unit performs the actual joint-belief draw. The equality
holds for every original history-dependent chooser, including deviations. -/
theorem pbsRoot_run_initial (roots : FinDist E.History) (chooser : E.RandomizedChooser)
    (fuel : Nat) :
    ((pbsRootProtocol roots).runRandomizedFor (pbsRootChooser roots chooser) (fuel + 1)
      (pbsRootProtocol roots).initHistory).map History.state =
      (roots.bind (E.runRandomizedFor chooser fuel)).map some := by
  have nonterminal : ¬ (pbsRootProtocol roots).terminal
      (pbsRootProtocol roots).initHistory.state := not_false
  rw [runRandomizedFor_succ_of_not_terminal _ _ nonterminal]
  simp only [pbsRootChooser, pbsRootActionLaw, initHistory, FinDist.pure_bind,
    FinDist.map_bindOnSupport]
  let tail : Option E.History → FinDist (Option E.History) := fun next =>
    match next with
    | none => FinDist.pure none
    | some history => (E.runRandomizedFor chooser fuel history).map some
  calc
    _ = (roots.map some).bind tail := by
      apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
      intro next realized
      have member : next ∈ (roots.map some).support := realized
      rw [FinDist.support_map] at member
      obtain ⟨original, _, rfl⟩ := member
      exact pbsRoot_runFrom_some roots chooser fuel original _
    _ = _ := by
      rw [FinDist.bind_map, FinDist.map_bind]

/-- Zero continuation fuel still samples the joint roots once, but executes
no original action or transition. It is distinct from zero administrative fuel. -/
theorem pbsRoot_run_one (roots : FinDist E.History) (chooser : E.RandomizedChooser) :
    ((pbsRootProtocol roots).runRandomizedFor (pbsRootChooser roots chooser) 1
      (pbsRootProtocol roots).initHistory).map History.state = roots.map some := by
  have kernel : E.runRandomizedFor chooser 0 = (fun history => FinDist.pure history) := by
    funext history
    rfl
  simpa only [kernel, FinDist.bind_pure] using pbsRoot_run_initial roots chooser 0

end GameTheory.ReBeL
