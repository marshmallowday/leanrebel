/-
# Finite-budget children at the actual factual public queries

Every live public posterior is solved by the finite-plan regret-matching
recurrence with its own derived mass budget. The public cut-prefix splice
retains the trunk and realizes every child and every behavioral deviation.
This adaptive normal-form reference is distinct from information-set CFR.
-/

import GameTheory.Analysis.ReBeL.PBSFinitePlanSolver
import GameTheory.Analysis.ReBeL.CFRDFactualMixture
import GameTheory.Analysis.ReBeL.CFRDClamp

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Finite solves at actual live joint posteriors; no Nash witness is selected.
Impossible public observations receive only the explicit legal fallback. -/
def cfrDFiniteChildTable (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    List M.PublicSignal → Profile (fullInformation M).behavioralSignature := fun obs => by
  classical
  exact if possible : CFRDFactualChildPossible M trunk cut remaining obs then
    pbsConditionalBudgetProfile (fullInformation M) (fullObservationClock M) fallback
      (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining utility bound loss
  else fun who => (fallback who).toBehavioral

/-- A single information-local profile uses each finite child's returned
policy, selected by the remembered public cut prefix, while preserving the past. -/
def cfrDFiniteChildProfile (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk
    (cfrDPublicContinuation M cut
      (cfrDFiniteChildTable M trunk fallback cut remaining utility bound loss))

/-- The finite solve never changes an already searched decision. -/
theorem cfrDFiniteChildProfile_before
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2)
    (info : (fullInformation M).InfoState who)
    (before : (fullObservationClock M).depth who info < cut) :
    cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss who info =
      trunk who info := by
  simp only [cfrDFiniteChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_pos before]

/-- The whole factual joint prefix law, not only the private marginals, is preserved. -/
theorem cfrDFiniteChildProfile_prefixLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    (fullInformation M).runBehavioral
        (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss) cut =
      (fullInformation M).runBehavioral trunk cut := by
  apply runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
  exact cfrDFiniteChildProfile_before M trunk fallback cut remaining utility bound loss

/-- All legal descendants retain the same public child's policy, irrespective
of current reach. The unknown future history is not a policy input. -/
theorem cfrDFiniteChildProfile_of_reaches
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2)
    (first later : E.History) (atCut : first.trace.length = cut) {fuel : Nat}
    (reaches : E.ReachesWithin fuel first later) :
    cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss who
        ((fullInformation M).infoOf who later.trace) =
      cfrDFiniteChildTable M trunk fallback cut remaining utility bound loss
        (publicTrace M.toInfoSignals first.trace) who
        ((fullInformation M).infoOf who later.trace) := by
  have after : ¬ (fullObservationClock M).depth who
      ((fullInformation M).infoOf who later.trace) < cut := by
    rw [(fullObservationClock M).correct]
    have monotone := reaches.trace_length_le
    omega
  simp only [cfrDFiniteChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_neg after]
  exact cfrDPublicContinuation_eq_of_reaches M cut _ who first later atCut reaches

/-- The spliced profile executes the complete joint law of its finite child. -/
theorem cfrDFiniteChildProfile_beliefLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut) (fuel : Nat) :
    PublicBelief.continuationLaw (fullInformation M)
        (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss) fuel belief =
      PublicBelief.continuationLaw (fullInformation M)
        (cfrDFiniteChildTable M trunk fallback cut remaining utility bound loss obs)
        fuel belief := by
  apply FinDist.bind_congr
  intro first supported
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ who
  simpa only [rootPublic] using cfrDFiniteChildProfile_of_reaches M trunk fallback cut remaining
    utility bound loss who first later (atCut first supported) reaches

/-- Every complete unilateral deviation has the same law in the child game.
An equality of played values alone would not justify approximate Nash transfer. -/
theorem cfrDFiniteChildProfile_deviationLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut)
    (fuel : Nat) (who : Fin 2) (target : (fullInformation M).BehavioralPolicy who) :
    PublicBelief.continuationLaw (fullInformation M)
        (Profile.update (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss)
          who target) fuel belief =
      PublicBelief.continuationLaw (fullInformation M)
        (Profile.update (cfrDFiniteChildTable M trunk fallback cut remaining utility bound loss obs)
          who target) fuel belief := by
  apply FinDist.bind_congr
  intro first supported
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
    simpa only [rootPublic] using cfrDFiniteChildProfile_of_reaches M trunk fallback cut remaining
      utility bound loss player first later (atCut first supported) reaches

/-- Approximate factual child Nash is derived from the finite recurrence.
One posterior-dependent root budget controls all supported private types. -/
theorem cfrDFiniteChildProfile_isNash
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h who, |utility h who| ≤ bound) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs) :
    IsNash (behavioralBeliefForm (fullInformation M)
        (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining)
      (euPreferenceWithin
        ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.positiveMassFloor * loss)
        utility) (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss) := by
  have equilibrium := pbsFiniteBudgetProfile_isNash (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) (fullObservationClock M) fallback
    (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining utility zeroSum bound
    nonneg bounded _ (mul_pos (FinDist.positiveMassFloor_pos _) positive)
  have table : cfrDFiniteChildTable M trunk fallback cut remaining utility bound loss obs =
      pbsConditionalBudgetProfile (fullInformation M) (fullObservationClock M) fallback
        (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining
        utility bound loss := by
    simp only [cfrDFiniteChildTable, dif_pos possible]
  rw [isNash_iff] at equilibrium ⊢
  intro who target
  have atCut := cfrDFactualChildBelief_atCut M trunk cut remaining obs possible
  simpa only [euPreferenceWithin_apply, behavioralBeliefForm,
    cfrDFiniteChildProfile_beliefLaw M trunk fallback cut remaining utility bound loss _ atCut,
    cfrDFiniteChildProfile_deviationLaw M trunk fallback cut remaining utility bound loss _ atCut,
    table, pbsConditionalBudgetProfile] using equilibrium who target

end GameTheory.ReBeL
