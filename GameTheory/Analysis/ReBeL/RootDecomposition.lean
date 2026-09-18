/-
# Constructed whole-policy root regret decomposition

The actual exhaustive schedule drives a chain of canonical unilateral local
replacements. Its root gain telescopes to baseline counterfactual regrets with
the fixed deviation's own-reach coefficients. No gain identity, solver result,
or local-regret bound is supplied as an assumption.
-/

import GameTheory.Analysis.ReBeL.PolicyPatching

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι] [Fintype E.History]

/-- One genuine decision's contribution uses the fixed target's own reach
and the original profile's counterfactual action regrets. -/
def targetRegretTerm (clock : ObservationClock M)
    (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (horizon : ℕ) (site : M.InformationSite who) : ℝ :=
  M.playerReachProbability (Profile.update strategy who target) who site.2.choose.1.trace *
    (target site.1).expect (M.counterfactualActionRegret strategy who site payoff
      (horizon - clock.depth who site.1))

/-- Telescoping is proved for an explicit partial patch and the remaining
chronological list. Its premises describe only enumeration, coverage and depth;
all numerical root identities are derived from canonical execution. -/
theorem partial_root_gain_sum (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (horizon : ℕ) :
    ∀ (sites : List (M.InformationSite who)) (done : Finset (M.InfoState who)),
      sites.Nodup →
      sites.Pairwise (fun a b => clock.depth who a.1 ≤ clock.depth who b.1) →
      (∀ site ∈ sites, site.1 ∉ done) →
      (∀ info ∈ done, ∀ site ∈ sites, clock.depth who info ≤ clock.depth who site.1) →
      (∀ history : E.History, history.trace.length < horizon →
        ¬ E.terminal history.state → E.active history.state who →
        M.infoOf who history.trace ∈ done ∨
          ∃ site ∈ sites, site.1 = M.infoOf who history.trace) →
      (∀ site ∈ sites, clock.depth who site.1 < horizon) →
      (M.runBehavioral (Profile.update strategy who target) horizon).expect payoff -
          (M.runBehavioral (partialProfile M strategy who target done) horizon).expect payoff =
        (sites.map (targetRegretTerm M clock strategy who target payoff horizon)).sum := by
  intro sites
  induction sites with
  | nil =>
      intro done _hnodup _horder _hseparate _hpast hcover _hbounded
      have hr := run_partialProfile_eq_target M strategy who target done horizon
        (fun history hbefore hterm hactive => by
          rcases hcover history hbefore hterm hactive with hdone | ⟨site, hmem, _⟩
          · exact hdone
          · simp at hmem)
      rw [hr, sub_self]
      rfl
  | cons site sites ih =>
      intro done hnodup horder hseparate hpast hcover hbounded
      have hhead : site ∈ site :: sites := List.mem_cons_self
      have htail (later : M.InformationSite who) (hmem : later ∈ sites) :
          later ∈ site :: sites := List.mem_cons_of_mem _ hmem
      have horderTail := (List.pairwise_cons.mp horder).2
      have hheadBefore := (List.pairwise_cons.mp horder).1
      have hnodupTail := (List.nodup_cons.mp hnodup).2
      have hheadNot := (List.nodup_cons.mp hnodup).1
      have hsiteBound := hbounded site hhead
      have hprior : ∀ history : E.History,
          history.trace.length < clock.depth who site.1 →
          ¬ E.terminal history.state → E.active history.state who →
          M.infoOf who history.trace ∈ done := by
        intro history hbefore hterm hactive
        rcases hcover history (lt_trans hbefore hsiteBound) hterm hactive with
          hdone | ⟨later, hmem, hinfo⟩
        · exact hdone
        · have hdepth : clock.depth who later.1 = history.trace.length := by
            rw [hinfo, clock.correct]
          have hle : clock.depth who site.1 ≤ clock.depth who later.1 := by
            rcases List.mem_cons.mp hmem with hequal | hlater
            · subst later
              exact le_rfl
            · exact hheadBefore later hlater
          omega
      have hstep :
          (M.runBehavioral
              (partialProfile M strategy who target (insert site.1 done)) horizon).expect payoff -
            (M.runBehavioral (partialProfile M strategy who target done) horizon).expect payoff =
          targetRegretTerm M clock strategy who target payoff horizon site := by
        calc
          _ = M.playerReachProbability (partialProfile M strategy who target done) who
                site.2.choose.1.trace *
              (target site.1).expect
                (M.counterfactualActionRegret (partialProfile M strategy who target done)
                  who site payoff (horizon - clock.depth who site.1)) := by
            rw [partialProfile_insert]
            exact root_withLaw_eq_reach_mul_expect M clock hrecall
              (partialProfile M strategy who target done) who site (target site.1)
              payoff horizon (Nat.le_of_lt hsiteBound)
          _ = M.playerReachProbability (Profile.update strategy who target) who
                site.2.choose.1.trace *
              (target site.1).expect (M.counterfactualActionRegret strategy who site payoff
                (horizon - clock.depth who site.1)) := by
            rw [partialProfile_ownReach_eq_target M clock strategy who target done site hprior]
            apply congrArg (fun value : ℝ =>
              M.playerReachProbability (Profile.update strategy who target) who
                site.2.choose.1.trace * value)
            apply FinDist.expect_congr
            intro choice _
            exact partialProfile_actionRegret M clock strategy who target done site
              (hseparate site hhead) (fun info hmem => hpast info hmem site hhead)
              payoff (horizon - clock.depth who site.1) choice
          _ = _ := rfl
      have hrest := ih (insert site.1 done) hnodupTail horderTail
        (fun later hmem hdone => by
          rcases Finset.mem_insert.mp hdone with hequal | hold
          · have hsame : later = site := Subtype.ext hequal
            subst later
            exact hheadNot hmem
          · exact hseparate later (htail later hmem) hold)
        (fun info hinfo later hlater => by
          rcases Finset.mem_insert.mp hinfo with hequal | hold
          · rw [hequal]
            exact hheadBefore later hlater
          · exact hpast info hold later (htail later hlater))
        (fun history hbefore hterm hactive => by
          rcases hcover history hbefore hterm hactive with hdone | ⟨later, hmem, hinfo⟩
          · exact Or.inl (Finset.mem_insert_of_mem hdone)
          · rcases List.mem_cons.mp hmem with hequal | hlater
            · subst later
              left
              rw [← hinfo]
              exact Finset.mem_insert_self _ _
            · exact Or.inr ⟨later, hlater, hinfo⟩)
        (fun later hmem => hbounded later (htail later hmem))
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- Full-game root gain against every behavioral deviation is the sum of
original counterfactual regrets weighted by that fixed deviation's own reach.
The list, coverage, order, single-site identities and all telescoping premises
are constructed, not supplied by a caller or a hypothetical solver. -/
theorem scheduled_root_gain (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (horizon : ℕ) :
    (M.runBehavioral (Profile.update strategy who target) horizon).expect payoff -
        (M.runBehavioral strategy horizon).expect payoff =
      ((scheduledSites M clock horizon who).map
        (targetRegretTerm M clock strategy who target payoff horizon)).sum := by
  have h := partial_root_gain_sum M clock hrecall strategy who target payoff horizon
    (scheduledSites M clock horizon who) ∅
    (scheduledSites_nodup M clock horizon who)
    (scheduledSites_ordered M clock horizon who)
    (by simp)
    (by simp)
    (fun history hbefore hterm hactive =>
      Or.inr (scheduledSites_covers M clock horizon who history hbefore hterm hactive))
    (fun site hmem => (mem_scheduledSites M clock horizon who site).mp hmem)
  simpa only [partialProfile_empty] using h

end GameTheory.ReBeL
