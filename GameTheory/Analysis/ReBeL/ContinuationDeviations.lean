/-
# All unilateral deviations at a PBS

Finite predrawing covers every legal continuation root, not just the initial
history. The result is an equality for an arbitrary behavioral replacement
against fixed opponents, and therefore justifies checking finite pure plans
when transferring Nash to a PBS-rooted behavioral game.
-/

import GameTheory.ReBeL.FiniteSites
import GameTheory.ReBeL.BeliefExecution

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Predrawing the counterfactual cover preserves a unilateral replacement
from every root; all other players retain their original laws. -/
theorem runFrom_finitePredraw_update
    (hrecall : M.PerfectRecall) (sites : (i : ι) → Finset (M.InfoState i))
    (fuel : ℕ) (root : E.History) (hcover : M.CoversInformationSitesFrom sites fuel root)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (replacementFallback : M.Policy who) :
    M.runMixedFrom (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixedWithin (sites i) (fallback i)) who
      (replacement.toMixedWithin (sites who) replacementFallback)) fuel root =
    M.runBehavioralFrom (Profile.update behavioral who replacement) fuel root := by
  rw [← finitePredraw_update]
  exact M.runMixedFrom_toMixedWithin
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall) sites _ _ fuel root hcover

/-- The canonical mixed-game update identity applies to any continuation
root without changing strategies, legality or the returned history law. -/
theorem runMixedFrom_update_bind (mixed : Profile M.strategicSignature.mixed)
    (who : ι) (replacement : M.MixedPolicy who) (fuel : ℕ) (root : E.History) :
    M.runMixedFrom (Profile.update mixed who replacement) fuel root =
      replacement.bind fun policy =>
        M.runMixedFrom (Profile.update mixed who (FinDist.pure policy)) fuel root :=
  GameForm.mixed_play_update
    { sig := M.strategicSignature, play := fun policies => M.runFrom policies fuel root }
    mixed who replacement

/-- Every behavioral deviation is an average of the actual finite pure-plan
deviations, simultaneously for all legal roots including off-policy roots. -/
theorem continuationDeviationValue_eq_expect_finitePlans [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ) (root : E.History)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (payoff : E.History → ℝ) :
    (M.runBehavioralFrom (Profile.update behavioral who replacement) fuel root).expect payoff =
      (FinDist.pi fun info : finiteSites M who => replacement info.1).expect
        fun plan => (M.runBehavioralFrom (Profile.update behavioral who
          (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel root).expect payoff := by
  rw [← runFrom_finitePredraw_update M hrecall (finiteSites M) fuel root
    (finiteSites_coversFrom M fuel root) behavioral fallback who replacement (fallback who)]
  rw [runMixedFrom_update_bind, FinDist.expect_bind,
    BehavioralPolicy.toMixedWithin_eq_map_pi, FinDist.expect_map]
  apply congrArg
  funext plan
  let purePlan : M.Policy who := FinitePlan.toPolicy M (fallback who) plan
  have realized := runFrom_finitePredraw_update M hrecall (finiteSites M) fuel root
    (finiteSites_coversFrom M fuel root) behavioral fallback who purePlan.toBehavioral purePlan
  rw [Policy.toBehavioral_toMixedWithin] at realized
  exact congrArg (fun law => law.expect payoff) realized

/-- The same finite law works across every root of the joint PBS. There is
no independent-marginal approximation and no conditioning on the deviator's
positive reach. -/
theorem publicBelief_deviationValue_eq_expect_finitePlans [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (payoff : E.History → ℝ)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations) :
    (PublicBelief.continuationLaw M
      (Profile.update behavioral who replacement) fuel belief).expect payoff =
      (FinDist.pi fun info : finiteSites M who => replacement info.1).expect
        fun plan => (PublicBelief.continuationLaw M (Profile.update behavioral who
          (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel belief).expect payoff := by
  unfold PublicBelief.continuationLaw
  rw [FinDist.expect_bind]
  calc
    _ = belief.law.expect (fun root =>
        (FinDist.pi fun info : finiteSites M who => replacement info.1).expect
          fun plan => (M.runBehavioralFrom (Profile.update behavioral who
            (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel root).expect payoff) :=
      FinDist.expect_congr fun root _ =>
        continuationDeviationValue_eq_expect_finitePlans M hrecall fuel root behavioral
          fallback who replacement payoff
    _ = _ := by
      rw [FinDist.expect_comm]
      simp only [FinDist.expect_bind]

/-- Uniform control of all finite pure plans controls every behavioral
replacement at the same PBS against the exact same opponents. -/
theorem publicBelief_deviationValue_le_of_finitePlans_le [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (payoff : E.History → ℝ) (bound : ℝ)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (hbound : ∀ plan : FinitePlan M who,
      (PublicBelief.continuationLaw M (Profile.update behavioral who
        (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel belief).expect payoff ≤ bound)
    (replacement : M.BehavioralPolicy who) :
    (PublicBelief.continuationLaw M
      (Profile.update behavioral who replacement) fuel belief).expect payoff ≤ bound := by
  rw [publicBelief_deviationValue_eq_expect_finitePlans M hrecall]
  exact FinDist.expect_le_of_forall _ _ _ fun plan _ => hbound plan

end GameTheory.ReBeL
