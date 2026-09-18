/-
# Existence of a Nash equilibrium at a public belief

Finite legal plans compile through the canonical protocol runner to an
ordinary GameForm. Finite mixed Nash existence is reused there. PBS-relative
seed realization preserves complete outcome laws; finite predrawing then
extends the transferred pure-deviation inequalities to all behavioral laws.
The joint PBS need not factor into independent private-type marginals.
-/

import GameTheory.Analysis.Nash
import GameTheory.Analysis.ReBeL.ContinuationRealization
import GameTheory.Analysis.ReBeL.ContinuationDeviations
import GameTheory.ReBeL.StrategicEquivalence

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι] [Fintype E.History]

/-- Finite legal plans retain the canonical protocol history as their outcome. -/
abbrev finiteBeliefSignature : GameSignature ι where
  Strategy := FinitePlan M
  Outcome := E.History

/-- The finite strategic-form extraction runs the existing legal plans from
the existing joint belief; it introduces no new execution or equilibrium rule. -/
abbrev finiteBeliefForm (fallback : Profile M.strategicSignature)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fuel : ℕ) : GameForm ι where
  sig := finiteBeliefSignature M
  play plans := belief.law.bind fun root =>
    M.runFrom (fun i => FinitePlan.toPolicy M (fallback i) (plans i)) fuel root

/-- The behavioral presentation of the exact same joint continuation runner.
For full AOH memory this is definitionally `Prescription.originalGame`. -/
abbrev behavioralBeliefForm {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ) : GameForm ι where
  sig := M.behavioralSignature
  play profile := PublicBelief.continuationLaw M profile fuel belief

/-- Each private mixed plan is read using the relative public-cut record.
Assembly and reading fallbacks are separate so a pure deviation can use itself
as its reading fallback without changing any opponent coordinate. -/
def finiteBeliefRealization (clock : ObservationClock M)
    (fallback readingFallback : Profile M.strategicSignature) (cut : ℕ)
    (mixed : Profile (finiteBeliefSignature M).mixed) : Profile M.behavioralSignature :=
  fun i => continuationBehavioral M clock cut
    ((mixed i).map (FinitePlan.toPolicy M (fallback i))) (readingFallback i)

omit [DecidableEq ι] in
/-- Independent private plan draws commute with the correlated initial root
law. The correlation of the latter is not discarded. -/
theorem finiteBeliefForm_mixed_law (fallback : Profile M.strategicSignature)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fuel : ℕ) (mixed : Profile (finiteBeliefSignature M).mixed) :
    (finiteBeliefForm M fallback belief fuel).mixed.play mixed =
      belief.law.bind (M.runMixedFrom
        (fun i => (mixed i).map (FinitePlan.toPolicy M (fallback i))) fuel) := by
  rw [GameForm.mixed_play]
  show (FinDist.pi mixed).bind (fun plans => belief.law.bind fun root =>
      M.runFrom (fun i => FinitePlan.toPolicy M (fallback i) (plans i)) fuel root) = _
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro root _
  rw [runMixedFrom, FinDist.pi_map, FinDist.bind_map]

omit [DecidableEq ι] in
/-- Mixed finite plans and their PBS-relative behavioral reading have the
same complete history law, for any fixed reading fallback. -/
theorem finiteBeliefForm_realization_law (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (fallback readingFallback : Profile M.strategicSignature)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fuel : ℕ) (mixed : Profile (finiteBeliefSignature M).mixed) :
    (finiteBeliefForm M fallback belief fuel).mixed.play mixed =
      (behavioralBeliefForm M belief fuel).play
        (finiteBeliefRealization M clock fallback readingFallback
          (observations.length - 1) mixed) := by
  rw [finiteBeliefForm_mixed_law]
  exact publicBelief_mixed_realization M hrecall clock readingFallback fuel _ belief

omit [Fintype ι] in
/-- Reading a pure replacement commutes with unilateral update, even at
information states where the replaced private seed has zero posterior mass. -/
theorem finiteBeliefRealization_update (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (cut : ℕ)
    (mixed : Profile (finiteBeliefSignature M).mixed) (who : ι) (plan : FinitePlan M who) :
    finiteBeliefRealization M clock fallback
      (Profile.update fallback who (FinitePlan.toPolicy M (fallback who) plan)) cut
      (Profile.update mixed who (FinDist.pure plan)) =
        Profile.update (finiteBeliefRealization M clock fallback fallback cut mixed) who
          (FinitePlan.toPolicy M (fallback who) plan).toBehavioral := by
  funext other
  by_cases same : other = who
  · subst other
    simp only [finiteBeliefRealization, Profile.update_same, FinDist.map_pure]
    exact continuationBehavioral_pure_self M clock cut _
  · simp only [finiteBeliefRealization, Profile.update_of_ne _ _ same]

/-- Outcome-law equality holds after each pure-plan unilateral deviation,
not merely for the original candidate profile. -/
theorem finiteBeliefForm_deviation_law (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fuel : ℕ) (mixed : Profile (finiteBeliefSignature M).mixed)
    (who : ι) (plan : FinitePlan M who) :
    (finiteBeliefForm M fallback belief fuel).mixed.play
      (Profile.update mixed who (FinDist.pure plan)) =
        (behavioralBeliefForm M belief fuel).play
          (Profile.update
            (finiteBeliefRealization M clock fallback fallback (observations.length - 1) mixed)
            who (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) := by
  rw [finiteBeliefForm_realization_law M hrecall clock fallback
    (Profile.update fallback who (FinitePlan.toPolicy M (fallback who) plan)),
    finiteBeliefRealization_update]

/-- A canonical mixed finite-plan equilibrium induces a canonical behavioral
PBS equilibrium. Arbitrary behavioral deviations are controlled by their
finite pure-plan decomposition, not by an assumed realization certificate. -/
theorem finiteBeliefForm_nash_realization (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fuel : ℕ) (utility : E.History → ι → ℝ)
    (mixed : Profile (finiteBeliefSignature M).mixed)
    (equilibrium : IsNash (finiteBeliefForm M fallback belief fuel).mixed
      (euPreference utility) mixed) :
    IsNash (behavioralBeliefForm M belief fuel) (euPreference utility)
      (finiteBeliefRealization M clock fallback fallback (observations.length - 1) mixed) := by
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  apply publicBelief_deviationValue_le_of_finitePlans_le M hrecall fuel _ fallback who
    (fun history => utility history who) _ belief
  intro plan
  have bound := equilibrium who (FinDist.pure plan)
  rw [euPreference_apply, finiteBeliefForm_deviation_law M hrecall clock,
    finiteBeliefForm_realization_law M hrecall clock fallback fallback] at bound
  exact bound

/-- Finite actions, finite legal histories, perfect recall and a legal total
fallback imply existence at every joint PBS. No equilibrium is supplied as an
input and no positivity of private-type reach is assumed. -/
theorem exists_publicBelief_nash [∀ i, Fintype (E.Action i)]
    (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature)
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fuel : ℕ) (utility : E.History → ι → ℝ) :
    ∃ profile : Profile M.behavioralSignature,
      IsNash (behavioralBeliefForm M belief fuel) (euPreference utility) profile := by
  classical
  let : ∀ i, Fintype (FinitePlan M i) := fun i => finitePlanFintype M i
  let : ∀ i, Nonempty (FinitePlan M i) := fun i => ⟨fun info => fallback i info.1⟩
  obtain ⟨mixed, equilibrium⟩ := exists_isNash_mixed
    (F := finiteBeliefForm M fallback belief fuel) utility
  exact ⟨finiteBeliefRealization M clock fallback fallback (observations.length - 1) mixed,
    finiteBeliefForm_nash_realization M hrecall clock fallback belief fuel utility mixed equilibrium⟩

/-- Full action-observation histories discharge recall and the observation
clock structurally, yielding existence in the existing M03 original game. -/
theorem exists_originalGame_nash [∀ i, Fintype (E.Action i)]
    (fallback : Profile (fullInformation M).strategicSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : ℕ)
    (utility : E.History → ι → ℝ) :
    ∃ profile : Profile (fullInformation M).behavioralSignature,
      IsNash (Prescription.originalGame M belief fuel) (euPreference utility) profile :=
  exists_publicBelief_nash (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) (fullObservationClock M)
      fallback belief.2 fuel utility

/-- The corresponding public-prescription game also has an equilibrium,
through M03's two-sided unilateral strategic equivalence. -/
theorem exists_prescriptionGame_nash [∀ i, Fintype (E.Action i)]
    (fallback : Profile (fullInformation M).strategicSignature)
    (reading : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : ℕ)
    (utility : E.History → ι → ℝ) :
    ∃ profile : Profile (Prescription.signature M),
      IsNash (Prescription.beliefGame M reading belief fuel) (euPreference utility) profile := by
  obtain ⟨profile, equilibrium⟩ := exists_originalGame_nash M fallback belief fuel utility
  exact ⟨Prescription.encodeProfile M profile,
    (Prescription.isNash_encode_iff M reading belief fuel profile utility).mp equilibrium⟩

end GameTheory.ReBeL
