/-
# Arbitrary behavioral deviations from a PBS

A deviation is a mixture of the existing finite pure information-local plans,
with every opponent held fixed. The equality is at the full outcome-law level
and works for an arbitrary joint root law; no product-of-marginals replacement
or positive-reach assumption is introduced.
-/

import GameTheory.Analysis.ReBeL.ValuePlans

noncomputable section

namespace GameTheory.ReBeL.PublicBelief

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- The canonical mixed-game unilateral-mixture identity at any history. -/
theorem runMixedFrom_update_bind (mixed : Profile M.strategicSignature.mixed)
    (who : ι) (replacement : M.MixedPolicy who) (fuel : ℕ) (root : E.History) :
    M.runMixedFrom (Profile.update mixed who replacement) fuel root =
      replacement.bind fun policy =>
        M.runMixedFrom (Profile.update mixed who (FinDist.pure policy)) fuel root :=
  GameForm.mixed_play_update
    { sig := M.strategicSignature, play := fun policies => M.runFrom policies fuel root }
    mixed who replacement

/-- Finite predrawing commutes with a unilateral deviation at every root,
using a policy-independent cover of counterfactual information states. -/
theorem run_finitePredrawFrom_update (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i)) (fuel : ℕ) (root : E.History)
    (cover : M.CoversInformationSitesFrom sites fuel root)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (replacementFallback : M.Policy who) :
    M.runMixedFrom (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixedWithin (sites i) (fallback i)) who
      (replacement.toMixedWithin (sites who) replacementFallback)) fuel root =
      M.runBehavioralFrom (Profile.update behavioral who replacement) fuel root := by
  rw [← finitePredraw_update]
  exact M.runMixedFrom_toMixedWithin
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall) sites _ _ fuel root cover

/-- The entire law of a behavioral deviation is a finite mixture of pure
plan laws from any fixed root. Terminal roots remain absorbed. -/
theorem deviationLaw_eq_bind_finitePlans_from [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ) (root : E.History)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) :
    M.runBehavioralFrom (Profile.update behavioral who replacement) fuel root =
      (FinDist.pi fun info : finiteSites M who => replacement info.1).bind
        fun plan => M.runBehavioralFrom (Profile.update behavioral who
          (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel root := by
  rw [← run_finitePredrawFrom_update M hrecall (finiteSites M) fuel root
    (finiteSites_coversFrom M fuel root) behavioral fallback who replacement (fallback who)]
  rw [runMixedFrom_update_bind, BehavioralPolicy.toMixedWithin_eq_map_pi, FinDist.bind_map]
  apply FinDist.bind_congr
  intro plan _
  let purePlan : M.Policy who := FinitePlan.toPolicy M (fallback who) plan
  have realized := run_finitePredrawFrom_update M hrecall (finiteSites M) fuel root
    (finiteSites_coversFrom M fuel root) behavioral fallback who purePlan.toBehavioral purePlan
  rw [Policy.toBehavioral_toMixedWithin] at realized
  exact realized

/-- The same one finite mixture realizes the deviation across the entire
joint root law. It is not a different plan selection at each hidden history. -/
theorem deviationLaw_eq_bind_finitePlans [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    {root : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals root) :
    continuationLaw M (Profile.update behavioral who replacement) fuel belief =
      (FinDist.pi fun info : finiteSites M who => replacement info.1).bind
        fun plan => continuationLaw M (Profile.update behavioral who
          (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel belief := by
  unfold continuationLaw
  calc
    _ = belief.law.bind (fun history =>
        (FinDist.pi fun info : finiteSites M who => replacement info.1).bind
          fun plan => M.runBehavioralFrom (Profile.update behavioral who
            (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel history) := by
      apply FinDist.bind_congr
      intro history _
      exact deviationLaw_eq_bind_finitePlans_from M hrecall fuel history
        behavioral fallback who replacement
    _ = _ := FinDist.bind_comm _ _ _

/-- A bound on every finite pure deviation bounds every behavioral deviation
with exactly the same payoff and bound at the same PBS. -/
theorem deviationValue_le_of_finitePlans_le [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    {root : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals root)
    (payoff : E.History → ℝ) (bound : ℝ)
    (bounded : ∀ plan : FinitePlan M who,
      (continuationLaw M (Profile.update behavioral who
        (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel belief).expect payoff ≤
          bound)
    (replacement : M.BehavioralPolicy who) :
    (continuationLaw M (Profile.update behavioral who replacement) fuel belief).expect payoff ≤
      bound := by
  rw [deviationLaw_eq_bind_finitePlans M hrecall fuel behavioral fallback who replacement,
    FinDist.expect_bind]
  exact FinDist.expect_le_of_forall _ _ _ fun plan _ => bounded plan

end GameTheory.ReBeL.PublicBelief
