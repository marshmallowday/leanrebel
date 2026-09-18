/-
# Mixed and behavioral realization from a public belief

Private continuation seeds are independent across players and fresh at the
public cut. The proof disintegrates those seeds along each legal joint answer,
then uses the relative-record conditioning theorem. It works from every
supported root of an arbitrary correlated joint PBS, not only from the
protocol's initial history or one policy's positive-reach region.
-/

import GameTheory.Analysis.ReBeL.ContinuationConsistency
import GameTheory.ReBeL.BeliefExecution

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι]

/-- Relative-record Kuhn realization, with an explicit induction invariant
for the seeds that remain after earlier continuation answers. -/
theorem runMixedFrom_continuationBehavioral (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (cut : ℕ) (fallback : (i : ι) → M.Policy i) :
    ∀ (fuel : ℕ) (mixed : (i : ι) → M.MixedPolicy i) (history : E.History),
      cut ≤ history.trace.length →
      (∀ i, (mixed i).support ⊆
        continuationConsistentAt M clock cut i (M.infoOf i history.trace)) →
      M.runMixedFrom mixed fuel history =
        M.runBehavioralFrom
          (fun i => continuationBehavioral M clock cut (mixed i) (fallback i)) fuel history := by
  classical
  intro fuel
  induction fuel with
  | zero => intro mixed history _ _; exact FinDist.bind_const _ _
  | succ fuel ih =>
    intro mixed history hcut hsub
    by_cases terminal : E.terminal history.state
    · rw [runMixedFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_of_terminal _ _ terminal]
      refine Eq.trans (FinDist.bind_congr fun policies _ => ?_) (FinDist.bind_const _ _)
      rw [runFrom, ExecutionProtocol.runHistoryFor_of_terminal _ _ terminal]
    · have draw : (FinDist.pi fun i =>
          continuationBehavioral M clock cut (mixed i) (fallback i)
            (M.infoOf i history.trace)) =
            FinDist.map (M.answerAt history) (FinDist.pi mixed) := by
        rw [show (fun i => continuationBehavioral M clock cut (mixed i) (fallback i)
            (M.infoOf i history.trace)) =
              (fun i => FinDist.map (fun policy => policy (M.infoOf i history.trace))
                (mixed i)) from funext fun i =>
                  continuationBehavioral_eq_map M clock cut (mixed i) (fallback i) _ (hsub i),
          FinDist.pi_map]
        rfl
      conv_lhs => rw [runMixedFrom,
        FinDist.eq_bind_condOnFibre (FinDist.pi mixed) (M.answerAt history),
        FinDist.bind_bind, FinDist.bind_map]
      rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel terminal, behavioralJoint, draw]
      conv_rhs => rw [FinDist.map_comp, FinDist.bind_map]
      refine FinDist.bind_congr fun profile supported => ?_
      have fibre : ∃ q ∈ M.answerAt history ⁻¹' {M.answerAt history profile},
          q ∈ (FinDist.pi mixed).support := ⟨profile, rfl, supported⟩
      have coordinate : ∀ i, ∃ q ∈ M.AnsweredBy history (M.answerAt history profile) i,
          q ∈ (mixed i).support :=
        fun i => ⟨profile i, rfl, FinDist.mem_support_pi.mp supported i⟩
      have legal : E.Legal history.state (fun i => ((M.answerAt history profile) i).1) :=
        ExecutionProtocol.legal_of_legalOption terminal fun i =>
          (M.menu_adequate i history.trace _).mp ((M.answerAt history profile) i).2
      rw [FinDist.condOnFibre, dif_pos fibre,
        M.condOn_answerAt mixed history (M.answerAt history profile) fibre coordinate]
      have step : (FinDist.pi fun i =>
            (mixed i).condOn (M.AnsweredBy history (M.answerAt history profile) i)
              (coordinate i)).bind (fun q => M.runFrom q (fuel + 1) history) =
          (FinDist.pi fun i =>
            (mixed i).condOn (M.AnsweredBy history (M.answerAt history profile) i)
              (coordinate i)).bind
            (fun q => (E.step history.state
              ⟨fun i => ((M.answerAt history profile) i).1, legal⟩).bindOnSupport
                fun _ realized => M.runFrom q fuel (history.extend legal realized)) :=
        FinDist.bind_congr fun q hq =>
          M.runFrom_succ_of_chooser_eq q terminal ⟨_, legal⟩
            (Subtype.ext (funext fun i => by
              show ((q i) (M.infoOf i history.trace)).1 = _
              rw [(FinDist.support_condOn _ _ (coordinate i)
                (FinDist.mem_support_pi.mp hq i)).1])) fuel
      rw [step, FinDist.bind_bindOnSupport_comm]
      refine FinDist.bindOnSupport_congr fun reached realized => ?_
      have hsub' : ∀ i,
          ((mixed i).condOn (M.AnsweredBy history (M.answerAt history profile) i)
            (coordinate i)).support ⊆ continuationConsistentAt M clock cut i
              (M.infoOf i (history.extend legal realized).trace) := by
        intro i q hq
        obtain ⟨answered, prior⟩ := FinDist.support_condOn _ _ (coordinate i) hq
        exact continuationConsistentAt_step M hrecall clock cut i history
          (M.answerAt history profile) legal realized q (hsub i prior) answered
      have hcut' : cut ≤ (history.extend legal realized).trace.length := by
        simp only [History.extend, Trace.length]
        omega
      rw [show (FinDist.pi fun i =>
            (mixed i).condOn (M.AnsweredBy history (M.answerAt history profile) i)
              (coordinate i)).bind
            (fun q => M.runFrom q fuel (history.extend legal realized)) =
          M.runMixedFrom
            (fun i => (mixed i).condOn (M.AnsweredBy history (M.answerAt history profile) i)
              (coordinate i)) fuel (history.extend legal realized) from rfl,
        ih _ _ hcut' hsub']
      refine M.runBehavioralFrom_congr fuel _ fun later reaches _ i => ?_
      cases action : ((M.answerAt history profile) i).1 with
      | none =>
          rw [M.condOn_answeredBy_eq_self i legal action (mixed i) (coordinate i)]
      | some chosen =>
          exact continuationBehavioral_condOn M clock cut (mixed i) (fallback i) _ _
            (coordinate i)
            (continuationConsistentAt_subset_answered M hrecall clock cut i history hcut
              (M.answerAt history profile) legal realized action reaches)

omit [Fintype ι] in
/-- All supported histories in a PBS have one public clock, regardless of
correlations, the current policy, or any zero-probability private type. -/
theorem publicBelief_root_depth {root : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals root) (history : E.History)
    (supported : history ∈ belief.law.support) : history.trace.length = root.length - 1 := by
  have depth : (publicTrace M.toInfoSignals history.trace).length =
      history.trace.length + 1 := by
    clear supported
    rcases history with ⟨state, trace⟩
    induction trace with
    | start => rfl
    | extend prior joint legal realized ih =>
        simp only [publicTrace, List.length_cons, Trace.length, ih]
  rw [belief.supported history supported] at depth
  omega

/-- Arbitrary fresh independent mixed policies admit one common behavioral
realization across the entire correlated PBS, with all opponents fixed. -/
theorem publicBelief_mixed_realization (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (fallback : (i : ι) → M.Policy i)
    (fuel : ℕ) (mixed : (i : ι) → M.MixedPolicy i)
    {root : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals root) :
    belief.law.bind (M.runMixedFrom mixed fuel) =
      PublicBelief.continuationLaw M
        (fun i => continuationBehavioral M clock (root.length - 1) (mixed i) (fallback i))
        fuel belief := by
  apply FinDist.bind_congr
  intro history supported
  have depth := publicBelief_root_depth M belief history supported
  exact runMixedFrom_continuationBehavioral M hrecall clock (root.length - 1) fallback
    fuel mixed history depth.ge
    (fun i policy _ => continuationConsistentAt_at_cut M hrecall clock _ i history
      depth.le policy)

omit [Fintype ι] in
/-- A pure seed read with itself as fallback is that exact behavioral policy,
including information states inconsistent with that seed. -/
theorem continuationBehavioral_pure_self (clock : ObservationClock M) (cut : ℕ)
    {who : ι} (policy : M.Policy who) :
    continuationBehavioral M clock cut (FinDist.pure policy) policy = policy.toBehavioral := by
  classical
  funext info
  rw [continuationBehavioral]
  split
  · rw [FinDist.condOn_pure, FinDist.map_pure]
    rfl
  · rfl

end GameTheory.ReBeL
