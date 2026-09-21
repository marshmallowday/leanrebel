/-
# Information-set CFR children at factual joint public queries

Every live posterior receives an actual information-set regret-matching solve
with a finite posterior-dependent budget. The public cut-prefix splice retains
the trunk and preserves complete baseline and unilateral continuation laws.
This is distinct from the inherited complete-plan normal-form child backend.
-/

import GameTheory.Analysis.ReBeL.PBSInformationBudget
import GameTheory.Analysis.ReBeL.CFRDFactualMixture
import GameTheory.Analysis.ReBeL.CFRDClamp

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Lift a legal local fallback without recovering any hidden history. -/
def cfrDInformationFallback (fallback : Profile M.strategicSignature) :
    Profile (fullInformation M).strategicSignature :=
  fun who => liftPolicy M who (fallback who)

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Live joint posteriors receive computed information-set CFR output.
An impossible public observation uses only the explicit legal fallback. -/
def cfrDInformationChildTable (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    List M.PublicSignal → Profile (fullInformation M).behavioralSignature := fun obs => by
  classical
  exact if possible : CFRDFactualChildPossible M trunk cut remaining obs then
    pbsInformationConditionalProfile M
      (cfrDFactualChildBelief M trunk cut remaining obs possible) fallback remaining
      utility bound loss
  else fun who => (cfrDInformationFallback M fallback who).toBehavioral

/-- One local profile retains past decisions and selects the child by its
remembered public cut prefix, never by a hidden root or opponent observation. -/
def cfrDInformationChildProfile (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk
    (cfrDPublicContinuation M cut
      (cfrDInformationChildTable M trunk fallback cut remaining utility bound loss))

/-- The constructed child cannot change an already searched decision. -/
theorem cfrDInformationChildProfile_before
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2)
    (info : (fullInformation M).InfoState who)
    (before : (fullObservationClock M).depth who info < cut) :
    cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who info =
      trunk who info := by
  simp only [cfrDInformationChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_pos before]

/-- The entire factual joint prefix law is preserved, not just its marginals. -/
theorem cfrDInformationChildProfile_prefixLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    (fullInformation M).runBehavioral
        (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss) cut =
      (fullInformation M).runBehavioral trunk cut := by
  apply runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
  exact cfrDInformationChildProfile_before M trunk fallback cut remaining utility bound loss

/-- Every legal descendant retains its public child's action law, including
paths with zero current policy reach. -/
theorem cfrDInformationChildProfile_of_reaches
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2)
    (first later : E.History) (atCut : first.trace.length = cut) {fuel : Nat}
    (reaches : E.ReachesWithin fuel first later) :
    cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who
        ((fullInformation M).infoOf who later.trace) =
      cfrDInformationChildTable M trunk fallback cut remaining utility bound loss
        (publicTrace M.toInfoSignals first.trace) who
        ((fullInformation M).infoOf who later.trace) := by
  have after : ¬ (fullObservationClock M).depth who
      ((fullInformation M).infoOf who later.trace) < cut := by
    rw [(fullObservationClock M).correct]
    have monotone := reaches.trace_length_le
    omega
  simp only [cfrDInformationChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_neg after]
  exact cfrDPublicContinuation_eq_of_reaches M cut _ who first later atCut reaches

/-- The spliced information-set output executes its complete joint child law. -/
theorem cfrDInformationChildProfile_beliefLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut) (fuel : Nat) :
    PublicBelief.continuationLaw (fullInformation M)
        (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss)
        fuel belief =
      PublicBelief.continuationLaw (fullInformation M)
        (cfrDInformationChildTable M trunk fallback cut remaining utility bound loss obs)
        fuel belief := by
  apply FinDist.bind_congr
  intro first supported
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ who
  simpa only [rootPublic] using cfrDInformationChildProfile_of_reaches M trunk fallback cut
    remaining utility bound loss who first later (atCut first supported) reaches

/-- Every unilateral behavioral replacement also preserves the complete law;
played-value equality alone would not justify an equilibrium transfer. -/
theorem cfrDInformationChildProfile_deviationLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut)
    (fuel : Nat) (who : Fin 2) (target : (fullInformation M).BehavioralPolicy who) :
    PublicBelief.continuationLaw (fullInformation M)
        (Profile.update
          (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss)
          who target) fuel belief =
      PublicBelief.continuationLaw (fullInformation M)
        (Profile.update
          (cfrDInformationChildTable M trunk fallback cut remaining utility bound loss obs)
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
    simpa only [rootPublic] using cfrDInformationChildProfile_of_reaches M trunk fallback cut
      remaining utility bound loss player first later (atCut first supported) reaches

/-- Actual information-set CFR supplies the mass-scaled factual Nash budget.
No child Nash witness, root independence or probability-floor premise is assumed. -/
theorem cfrDInformationChildProfile_isNash
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h who, |utility h who| ≤ bound) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs) :
    IsNash (behavioralBeliefForm (fullInformation M)
        (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining)
      (euPreferenceWithin
        ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.positiveMassFloor * loss)
        utility)
      (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss) := by
  have equilibrium := pbsInformationConditionalProfile_isNash M
    (cfrDFactualChildBelief M trunk cut remaining obs possible) fallback remaining utility
    zeroSum bound loss nonneg positive bounded
  have table : cfrDInformationChildTable M trunk fallback cut remaining utility bound loss obs =
      pbsInformationConditionalProfile M
        (cfrDFactualChildBelief M trunk cut remaining obs possible) fallback remaining
        utility bound loss := by
    simp only [cfrDInformationChildTable, dif_pos possible]
  rw [isNash_iff] at equilibrium ⊢
  intro who target
  have atCut := cfrDFactualChildBelief_atCut M trunk cut remaining obs possible
  simpa only [euPreferenceWithin_apply, behavioralBeliefForm,
    cfrDInformationChildProfile_beliefLaw M trunk fallback cut remaining
      utility bound loss _ atCut,
    cfrDInformationChildProfile_deviationLaw M trunk fallback cut remaining
      utility bound loss _ atCut, table] using equilibrium who target

end GameTheory.ReBeL
