/-
# A policy-independent finite cover and pure-plan deviations

All canonical legal histories, including off-policy and terminal histories,
contribute to the cover. The finite table does not grant access to a hidden
state: each coordinate is still one information state and its canonical menu.
The fallback is supplied, not inferred from progress at nonterminal states.
-/

import GameTheory.ReBeL.Finite
import GameTheory.ReBeL.Response

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- A cover of all information states occurring on any legal history. -/
def finiteSites [Fintype E.History] (i : ι) : Finset (M.InfoState i) := by
  classical
  exact Finset.univ.image fun h : E.History => M.infoOf i h.trace

/-- Membership is independent of the support of any chosen policy. -/
theorem mem_finiteSites [Fintype E.History] (i : ι) (info : M.InfoState i) :
    info ∈ finiteSites M i ↔ ∃ h : E.History, M.infoOf i h.trace = info := by
  classical
  simp [finiteSites]

/-- The same cover works for every root, horizon and unilateral deviation. -/
theorem finiteSites_coversFrom [Fintype E.History] (fuel : ℕ) (root : E.History) :
    M.CoversInformationSitesFrom (finiteSites M) fuel root := by
  intro later _ _ i
  exact (mem_finiteSites M i _).mpr ⟨later, rfl⟩

/-- Initial-history specialization of the policy-independent cover. -/
theorem finiteSites_covers [Fintype E.History] (fuel : ℕ) :
    M.CoversInformationSites (finiteSites M) fuel :=
  finiteSites_coversFrom M fuel E.initHistory

/-- A pure plan is a finite information-local table, not a state-reading strategy. -/
abbrev FinitePlan [Fintype E.History] (i : ι) :=
  (info : finiteSites M i) → M.Choice i info.1

/-- Explicit assembly reuses the canonical finite predrawing implementation. -/
def FinitePlan.toPolicy [Fintype E.History] {i : ι}
    (fallback : M.Policy i) (plan : FinitePlan M i) : M.Policy i :=
  InformationModel.Policy.assembleWithin M fallback (finiteSites M i) plan

/-- Finite actions and the finite cover yield a genuinely finite plan space. -/
def finitePlanFintype [Fintype E.History] (i : ι) [Fintype (E.Action i)] :
    Fintype (FinitePlan M i) := by
  classical
  exact inferInstance

section Realization

variable [Fintype ι] [DecidableEq ι]

/-- Finite predrawing commutes with unilateral replacement. The replacement's
fallback may differ from the fixed opponents' fallbacks. -/
omit [Fintype ι] in
 theorem finitePredraw_update
    (sites : (i : ι) → Finset (M.InfoState i))
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (replacementFallback : M.Policy who) :
    (fun i => ((Profile.update behavioral who replacement) i).toMixedWithin
      (sites i) ((Profile.update fallback who replacementFallback) i)) =
    Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixedWithin (sites i) (fallback i)) who
      (replacement.toMixedWithin (sites who) replacementFallback) := by
  funext i
  by_cases hi : i = who
  · subst i
    rw [Profile.update_same, Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi,
      Profile.update_of_ne _ _ hi]

/-- Outcome-law equality holds for an arbitrary replacement against the same
fixed opponents; it is not an equality only for one reference profile. -/
theorem run_finitePredraw_update
    (hrecall : M.PerfectRecall) (sites : (i : ι) → Finset (M.InfoState i))
    (fuel : ℕ) (hcover : M.CoversInformationSites sites fuel)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (replacementFallback : M.Policy who) :
    M.runMixed (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixedWithin (sites i) (fallback i)) who
      (replacement.toMixedWithin (sites who) replacementFallback)) fuel =
    M.runBehavioral (Profile.update behavioral who replacement) fuel := by
  rw [← finitePredraw_update]
  exact M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites _ _ fuel hcover

/-- One player's mixed run is the mixture of that player's pure replacements.
This is the canonical game-form identity, not a second payoff evaluator. -/
theorem runMixed_update_bind (mixed : Profile M.strategicSignature.mixed)
    (who : ι) (replacement : M.MixedPolicy who) (fuel : ℕ) :
    M.runMixed (Profile.update mixed who replacement) fuel =
      replacement.bind fun policy =>
        M.runMixed (Profile.update mixed who (FinDist.pure policy)) fuel :=
  GameForm.mixed_play_update (M.toGameForm fuel) mixed who replacement

/-- An arbitrary behavioral deviation has exactly the expected payoff of a
finite law of pure information-local tables. The opponents are held fixed. -/
theorem deviationValue_eq_expect_finitePlans [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (payoff : E.History → ℝ) :
    (M.runBehavioral (Profile.update behavioral who replacement) fuel).expect payoff =
      (FinDist.pi fun info : finiteSites M who => replacement info.1).expect
        fun plan => (M.runBehavioral (Profile.update behavioral who
          (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel).expect payoff := by
  rw [← run_finitePredraw_update M hrecall (finiteSites M) fuel
    (finiteSites_covers M fuel) behavioral fallback who replacement (fallback who)]
  rw [runMixed_update_bind, FinDist.expect_bind,
    InformationModel.BehavioralPolicy.toMixedWithin_eq_map_pi, FinDist.expect_map]
  apply congrArg
  funext plan
  let purePlan : M.Policy who := FinitePlan.toPolicy M (fallback who) plan
  have hreal := run_finitePredraw_update M hrecall (finiteSites M) fuel
    (finiteSites_covers M fuel) behavioral fallback who purePlan.toBehavioral purePlan
  rw [InformationModel.Policy.toBehavioral_toMixedWithin] at hreal
  exact congrArg (fun law => law.expect payoff) hreal

/-- Checking every finite pure plan controls all behavioral deviations, with
the very same bound. No equilibrium or best-response oracle is assumed. -/
theorem deviationValue_le_of_finitePlans_le [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (payoff : E.History → ℝ) (bound : ℝ)
    (hbound : ∀ plan : FinitePlan M who,
      (M.runBehavioral (Profile.update behavioral who
        (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel).expect payoff ≤ bound)
    (replacement : M.BehavioralPolicy who) :
    (M.runBehavioral (Profile.update behavioral who replacement) fuel).expect payoff ≤ bound := by
  rw [deviationValue_eq_expect_finitePlans M hrecall fuel behavioral fallback]
  exact FinDist.expect_le_of_forall _ _ _ fun plan _ => hbound plan

/-- A maximum is attained by a finite pure plan even against arbitrary fixed
behavioral opponents. This proves existence, not just an IsGreatest equivalence. -/
theorem exists_finitePlan_bestResponse [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι) [Fintype (E.Action who)]
    (payoff : E.History → ℝ) :
    ∃ plan : FinitePlan M who, ∀ replacement : M.BehavioralPolicy who,
      (M.runBehavioral (Profile.update behavioral who replacement) fuel).expect payoff ≤
      (M.runBehavioral (Profile.update behavioral who
        (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel).expect payoff := by
  letI := finitePlanFintype M who
  letI : Nonempty (FinitePlan M who) := ⟨fun info => fallback who info.1⟩
  obtain ⟨plan, hplan⟩ := Finite.exists_max fun plan : FinitePlan M who =>
    (M.runBehavioral (Profile.update behavioral who
      (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel).expect payoff
  exact ⟨plan, deviationValue_le_of_finitePlans_le M hrecall fuel behavioral fallback
    who payoff _ hplan⟩

/-- The attaining finite table is a best response in the existing canonical
behavioral game, for the cumulative rewards used throughout ReBeL. -/
theorem exists_pure_bestResponse [Fintype E.History]
    (hrecall : M.PerfectRecall) (reward : StageReward E) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι) [Fintype (E.Action who)] :
    ∃ policy : M.Policy who,
      IsBestResponse (M.toBehavioralGameForm fuel)
        (euPreference (cumulativeUtility reward)) who behavioral policy.toBehavioral := by
  obtain ⟨plan, hplan⟩ := exists_finitePlan_bestResponse M hrecall fuel behavioral
    fallback who (fun history => cumulativeUtility reward history who)
  exact ⟨FinitePlan.toPolicy M (fallback who) plan, hplan⟩

end Realization
end GameTheory.ReBeL
