/-
# Conditioning private continuation seeds after a public cut

The ordinary mixed-to-behavioral reading conditions on all past own actions.
A fresh seed drawn at a PBS must instead condition only on actions after that
public cut. These definitions use the same canonical policies, menus, records
and FinDist conditioning; no new execution or game semantics are introduced.
-/

import GameTheory.ReBeL.Schedule

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Every own-action record entry predates the current observation clock. -/
theorem ownPlay_depth_lt (clock : ObservationClock M) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    ∀ entry ∈ M.ownPlay who trace, clock.depth who entry.1 < trace.length := by
  induction trace with
  | start =>
      intro entry hentry
      simp [InfoSignals.ownPlay] at hentry
  | @extend source target prior joint legal realized ih =>
      intro entry hentry
      rw [InfoSignals.ownPlay_extend] at hentry
      cases hchoice : joint who with
      | none =>
          rw [hchoice] at hentry
          exact Nat.lt_succ_of_lt (ih entry hentry)
      | some action =>
          rw [hchoice] at hentry
          rcases List.mem_cons.mp hentry with rfl | hprior
          · simpa only [clock.correct who ⟨source, prior⟩, Trace.length] using
              Nat.lt_succ_self prior.length
          · exact Nat.lt_succ_of_lt (ih entry hprior)

/-- A continuation seed is constrained by the player's own actions at or
at or after the public cut, not by actions that preceded drawing that seed. -/
def continuationConsistentAt (clock : ObservationClock M) (cut : ℕ)
    (who : ι) (info : M.InfoState who) : Set (M.Policy who) :=
  {policy | ∀ entry ∈ M.recordAt who info,
    cut ≤ clock.depth who entry.1 → (policy entry.1).1 = some entry.2}

/-- Perfect recall makes the filtered constraints information-local. -/
theorem continuationConsistentAt_eq (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (cut : ℕ) (who : ι) (history : E.History) :
    continuationConsistentAt M clock cut who (M.infoOf who history.trace) =
      {policy | ∀ entry ∈ M.ownPlay who history.trace,
        cut ≤ clock.depth who entry.1 → (policy entry.1).1 = some entry.2} := by
  unfold continuationConsistentAt
  rw [M.recordAt_eq_ownPlay hrecall]

/-- At the cut itself every fresh policy seed is possible, even if its
prescriptions before the cut disagree with the observed past. -/
theorem continuationConsistentAt_at_cut (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (cut : ℕ) (who : ι) (history : E.History)
    (hcut : history.trace.length ≤ cut) (policy : M.Policy who) :
    policy ∈ continuationConsistentAt M clock cut who (M.infoOf who history.trace) := by
  rw [continuationConsistentAt_eq M hrecall]
  intro entry hentry hafter
  have hbefore := ownPlay_depth_lt M clock who history.trace entry hentry
  omega

/-- One observed answer extends the continuation constraints correctly. -/
theorem continuationConsistentAt_step (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (cut : ℕ) (who : ι) (history : E.History)
    (answer : (i : ι) → M.Choice i (M.infoOf i history.trace))
    (legal : E.Legal history.state (fun i => (answer i).1))
    {target : E.State} (realized : target ∈ (E.step history.state ⟨_, legal⟩).support)
    (policy : M.Policy who)
    (prior : policy ∈ continuationConsistentAt M clock cut who
      (M.infoOf who history.trace))
    (answered : policy ∈ M.AnsweredBy history answer who) :
    policy ∈ continuationConsistentAt M clock cut who
      (M.infoOf who (history.extend legal realized).trace) := by
  rw [continuationConsistentAt_eq M hrecall] at prior ⊢
  intro entry hentry hdepth
  rw [show M.ownPlay who (history.extend legal realized).trace =
      M.ownPlay who (Trace.extend history.trace (fun i => (answer i).1) legal realized)
      from rfl, InfoSignals.ownPlay_extend] at hentry
  cases hchoice : (answer who).1 with
  | none =>
      rw [hchoice] at hentry
      exact prior entry hentry hdepth
  | some action =>
      rw [hchoice] at hentry
      rcases List.mem_cons.mp hentry with rfl | hprior
      · show (policy (M.infoOf who history.trace)).1 = some action
        rw [answered, hchoice]
      · exact prior entry hprior hdepth

/-- A later compatible continuation seed necessarily gave each intervening
own answer. This is the key tower-conditioning premise. -/
theorem continuationConsistentAt_subset_answered (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (cut : ℕ) (who : ι) (history : E.History)
    (hcut : cut ≤ history.trace.length)
    (answer : (i : ι) → M.Choice i (M.infoOf i history.trace))
    (legal : E.Legal history.state (fun i => (answer i).1))
    {target : E.State} (realized : target ∈ (E.step history.state ⟨_, legal⟩).support)
    {action : E.Action who} (hact : (answer who).1 = some action)
    {fuel : ℕ} {later : E.History}
    (reaches : E.ReachesWithin fuel (history.extend legal realized) later) :
    continuationConsistentAt M clock cut who (M.infoOf who later.trace) ⊆
      M.AnsweredBy history answer who := by
  intro policy consistent
  apply Subtype.ext
  have current : (M.infoOf who history.trace, action) ∈
      M.ownPlay who (history.extend legal realized).trace := by
    rw [show M.ownPlay who (history.extend legal realized).trace =
        M.ownPlay who (Trace.extend history.trace (fun i => (answer i).1) legal realized)
        from rfl, InfoSignals.ownPlay_extend, hact]
    exact List.mem_cons_self
  rw [continuationConsistentAt_eq M hrecall] at consistent
  have recorded := (M.ownPlay_isSuffix_of_reachesWithin who reaches).subset current
  have depth : cut ≤ clock.depth who (M.infoOf who history.trace) := by
    rw [clock.correct]
    exact hcut
  exact (consistent _ recorded depth).trans hact.symm

/-- Read a fresh private continuation seed as an information-local behavioral
policy. The supplied fallback is held fixed under subsequent conditioning. -/
def continuationBehavioral (clock : ObservationClock M) (cut : ℕ) {who : ι}
    (mixed : M.MixedPolicy who) (fallback : M.Policy who) : M.BehavioralPolicy who := by
  classical
  exact fun info =>
    if reachable : ∃ policy ∈ continuationConsistentAt M clock cut who info,
        policy ∈ mixed.support then
      (mixed.condOn (continuationConsistentAt M clock cut who info) reachable).map
        (fun policy => policy info)
    else FinDist.pure (fallback info)

/-- If all remaining seeds are compatible, the reading is their plain action
marginal. There is no implicit positive-reach assumption. -/
theorem continuationBehavioral_eq_map (clock : ObservationClock M) (cut : ℕ) {who : ι}
    (mixed : M.MixedPolicy who) (fallback : M.Policy who) (info : M.InfoState who)
    (compatible : mixed.support ⊆ continuationConsistentAt M clock cut who info) :
    continuationBehavioral M clock cut mixed fallback info =
      mixed.map (fun policy => policy info) := by
  classical
  obtain ⟨policy, supported⟩ := mixed.support_nonempty
  rw [continuationBehavioral, dif_pos ⟨policy, compatible supported, supported⟩,
    FinDist.condOn_of_support_subset _ _ _ compatible]

/-- Conditioning on an answer already entailed by the later information
cannot change the later reading, including its zero-mass fallback. -/
theorem continuationBehavioral_condOn (clock : ObservationClock M) (cut : ℕ) {who : ι}
    (mixed : M.MixedPolicy who) (fallback : M.Policy who) (info : M.InfoState who)
    (answered : Set (M.Policy who))
    (positive : ∃ policy ∈ answered, policy ∈ mixed.support)
    (narrow : continuationConsistentAt M clock cut who info ⊆ answered) :
    continuationBehavioral M clock cut (mixed.condOn answered positive) fallback info =
      continuationBehavioral M clock cut mixed fallback info := by
  classical
  simp only [continuationBehavioral]
  by_cases existsSeed : ∃ policy ∈ continuationConsistentAt M clock cut who info,
      policy ∈ mixed.support
  · obtain ⟨policy, consistent, supported⟩ := existsSeed
    have conditioned : ∃ q ∈ continuationConsistentAt M clock cut who info,
        q ∈ (mixed.condOn answered positive).support :=
      ⟨policy, consistent, FinDist.mem_support_condOn _ _ _ (narrow consistent) supported⟩
    rw [dif_pos conditioned, dif_pos ⟨policy, consistent, supported⟩,
      FinDist.condOn_condOn mixed positive ⟨policy, consistent, supported⟩
        (Set.inter_subset_left.trans narrow) conditioned]
  · have conditioned : ¬ ∃ q ∈ continuationConsistentAt M clock cut who info,
        q ∈ (mixed.condOn answered positive).support := by
      rintro ⟨policy, consistent, supported⟩
      exact existsSeed ⟨policy, consistent, (FinDist.support_condOn _ _ positive supported).2⟩
    rw [dif_neg conditioned, dif_neg existsSeed]

end GameTheory.ReBeL
