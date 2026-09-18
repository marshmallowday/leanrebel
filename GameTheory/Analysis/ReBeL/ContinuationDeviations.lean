/-
# Expected-value consequences of PBS deviation laws

These public compatibility lemmas are consequences of the complete outcome-law
identities in `ValueDeviations`. A single finite plan law works across the
joint PBS, with all opponents fixed, including counterfactual roots.
-/

import GameTheory.Analysis.ReBeL.ValueDeviations

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Predrawing preserves a unilateral replacement from every legal root. -/
theorem runFrom_finitePredraw_update
    (hrecall : M.PerfectRecall) (sites : (i : ι) → Finset (M.InfoState i))
    (fuel : ℕ) (root : E.History) (hcover : M.CoversInformationSitesFrom sites fuel root)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (replacementFallback : M.Policy who) :
    M.runMixedFrom (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixedWithin (sites i) (fallback i)) who
      (replacement.toMixedWithin (sites who) replacementFallback)) fuel root =
      M.runBehavioralFrom (Profile.update behavioral who replacement) fuel root :=
  PublicBelief.run_finitePredrawFrom_update M hrecall sites fuel root hcover
    behavioral fallback who replacement replacementFallback

/-- Canonical mixed-game replacement is a mixture of pure replacements. -/
theorem runMixedFrom_update_bind (mixed : Profile M.strategicSignature.mixed)
    (who : ι) (replacement : M.MixedPolicy who) (fuel : ℕ) (root : E.History) :
    M.runMixedFrom (Profile.update mixed who replacement) fuel root =
      replacement.bind fun policy =>
        M.runMixedFrom (Profile.update mixed who (FinDist.pure policy)) fuel root :=
  PublicBelief.runMixedFrom_update_bind M mixed who replacement fuel root

/-- Every behavioral deviation is an average of actual finite pure plans. -/
theorem continuationDeviationValue_eq_expect_finitePlans [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ) (root : E.History)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (payoff : E.History → ℝ) :
    (M.runBehavioralFrom (Profile.update behavioral who replacement) fuel root).expect payoff =
      (FinDist.pi fun info : finiteSites M who => replacement info.1).expect
        fun plan => (M.runBehavioralFrom (Profile.update behavioral who
          (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel root).expect payoff := by
  rw [PublicBelief.deviationLaw_eq_bind_finitePlans_from M hrecall, FinDist.expect_bind]

/-- The exact same plan law works simultaneously across all hidden roots. -/
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
  rw [PublicBelief.deviationLaw_eq_bind_finitePlans M hrecall, FinDist.expect_bind]

/-- Pure-deviation bounds suffice for arbitrary behavioral deviations. -/
theorem publicBelief_deviationValue_le_of_finitePlans_le [Fintype E.History]
    (hrecall : M.PerfectRecall) (fuel : ℕ)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (payoff : E.History → ℝ) (bound : ℝ)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (hbound : ∀ plan : FinitePlan M who,
      (PublicBelief.continuationLaw M (Profile.update behavioral who
        (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) fuel belief).expect payoff ≤
          bound)
    (replacement : M.BehavioralPolicy who) :
    (PublicBelief.continuationLaw M
      (Profile.update behavioral who replacement) fuel belief).expect payoff ≤ bound :=
  PublicBelief.deviationValue_le_of_finitePlans_le M hrecall fuel behavioral fallback who
    belief payoff bound hbound replacement

end GameTheory.ReBeL
