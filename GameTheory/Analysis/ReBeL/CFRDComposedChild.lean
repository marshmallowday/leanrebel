/-
# Compositional children for structurally recursive CFR-D

A child solver is an actual function of the factual joint PBS and a requested
accuracy. This module lifts its accuracy theorem through public splicing and
zero-own-reach completion. The premise is an induction interface, not a claimed
solver implementation; the recursive consumer must discharge it from smaller
calls. All complete baseline and unilateral history laws are preserved.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationContinuation

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Computational child interface: no equilibrium or correctness proof is data. -/
abbrev PBSChildSolve :=
  {obs : List M.PublicSignal} → PublicBelief (fullInformation M).toInfoSignals obs →
    ℝ → Profile (fullInformation M).behavioralSignature

/-- Induction statement for a smaller child computation at every positive target. -/
def PBSChildSolveAccurate (solve : PBSChildSolve M)
    (utility : E.History → Fin 2 → ℝ) (remaining : Nat) : Prop :=
  ∀ {obs} (belief : PublicBelief (fullInformation M).toInfoSignals obs) tolerance,
    0 < tolerance →
      IsNash (behavioralBeliefForm (fullInformation M) belief remaining)
        (euPreferenceWithin tolerance utility) (solve belief tolerance)

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- The actual parent trunk determines both the child root and its mass-scaled target. -/
def cfrDComposedChildTable (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) :
    List M.PublicSignal → Profile (fullInformation M).behavioralSignature := fun obs => by
  classical
  exact if possible : CFRDFactualChildPossible M trunk cut remaining obs then
    let belief := cfrDFactualChildBelief M trunk cut remaining obs possible
    solve belief (belief.law.positiveMassFloor * loss)
  else fun who => (cfrDInformationFallback M fallback who).toBehavioral

/-- Retain the incumbent before the cut and the selected public child afterwards. -/
def cfrDComposedChildProfile (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) : Profile (fullInformation M).behavioralSignature :=
  cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk
    (cfrDPublicContinuation M cut
      (cfrDComposedChildTable M trunk fallback cut remaining loss solve))

/-- The new child cannot alter an already searched decision. -/
theorem cfrDComposedChildProfile_before
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (who : Fin 2) (info : (fullInformation M).InfoState who)
    (before : (fullObservationClock M).depth who info < cut) :
    cfrDComposedChildProfile M trunk fallback cut remaining loss solve who info =
      trunk who info := by
  simp only [cfrDComposedChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_pos before]

/-- Preserve the factual joint cut law, not just a played payoff or public marginal. -/
theorem cfrDComposedChildProfile_prefixLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) :
    (fullInformation M).runBehavioral
      (cfrDComposedChildProfile M trunk fallback cut remaining loss solve) cut =
        (fullInformation M).runBehavioral trunk cut := by
  apply runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
  exact cfrDComposedChildProfile_before M trunk fallback cut remaining loss solve

/-- The public child is retained on every legal descendant, even at zero reach. -/
theorem cfrDComposedChildProfile_of_reaches
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (who : Fin 2) (first later : E.History)
    (atCut : first.trace.length = cut) {fuel : Nat}
    (reaches : E.ReachesWithin fuel first later) :
    cfrDComposedChildProfile M trunk fallback cut remaining loss solve who
        ((fullInformation M).infoOf who later.trace) =
      cfrDComposedChildTable M trunk fallback cut remaining loss solve
        (publicTrace M.toInfoSignals first.trace) who
        ((fullInformation M).infoOf who later.trace) := by
  have after : ¬ (fullObservationClock M).depth who
      ((fullInformation M).infoOf who later.trace) < cut := by
    rw [(fullObservationClock M).correct]
    have monotone := reaches.trace_length_le
    omega
  simp only [cfrDComposedChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_neg after]
  exact cfrDPublicContinuation_eq_of_reaches M cut _ who first later atCut reaches

/-- Complete baseline continuation laws agree with the selected child. -/
theorem cfrDComposedChildProfile_beliefLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut) (fuel : Nat) :
    PublicBelief.continuationLaw (fullInformation M)
      (cfrDComposedChildProfile M trunk fallback cut remaining loss solve) fuel belief =
    PublicBelief.continuationLaw (fullInformation M)
      (cfrDComposedChildTable M trunk fallback cut remaining loss solve obs) fuel belief := by
  apply FinDist.bind_congr
  intro first supported
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ who
  simpa only [rootPublic] using cfrDComposedChildProfile_of_reaches M trunk fallback
    cut remaining loss solve who first later (atCut first supported) reaches

/-- All unilateral behavioral deviations preserve their complete history laws too. -/
theorem cfrDComposedChildProfile_deviationLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut) (fuel : Nat)
    (who : Fin 2) (target : (fullInformation M).BehavioralPolicy who) :
    PublicBelief.continuationLaw (fullInformation M)
      (Profile.update (cfrDComposedChildProfile M trunk fallback cut remaining loss solve)
        who target) fuel belief =
    PublicBelief.continuationLaw (fullInformation M)
      (Profile.update (cfrDComposedChildTable M trunk fallback cut remaining loss solve obs)
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
    simpa only [rootPublic] using cfrDComposedChildProfile_of_reaches M trunk fallback
      cut remaining loss solve player first later (atCut first supported) reaches

/-- Transfer the smaller solve's derived accuracy through the actual public splice. -/
theorem cfrDComposedChildProfile_isNash
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (positive : 0 < loss) (solve : PBSChildSolve M) (utility : E.History → Fin 2 → ℝ)
    (smaller : PBSChildSolveAccurate M solve utility remaining) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs) :
    IsNash (behavioralBeliefForm (fullInformation M)
      (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining)
      (euPreferenceWithin
        ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.positiveMassFloor * loss)
        utility) (cfrDComposedChildProfile M trunk fallback cut remaining loss solve) := by
  let belief := cfrDFactualChildBelief M trunk cut remaining obs possible
  have equilibrium := smaller belief (belief.law.positiveMassFloor * loss)
    (mul_pos (FinDist.positiveMassFloor_pos belief.law) positive)
  have table : cfrDComposedChildTable M trunk fallback cut remaining loss solve obs =
      solve belief (belief.law.positiveMassFloor * loss) := by
    simp only [cfrDComposedChildTable, dif_pos possible, belief]
  rw [isNash_iff] at equilibrium ⊢
  intro who target
  have atCut := cfrDFactualChildBelief_atCut M trunk cut remaining obs possible
  simpa only [euPreferenceWithin_apply, behavioralBeliefForm,
    cfrDComposedChildProfile_beliefLaw M trunk fallback cut remaining loss solve _ atCut,
    cfrDComposedChildProfile_deviationLaw M trunk fallback cut remaining loss solve _ atCut,
    table] using equilibrium who target

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Continuation replacement preserves the old counterfactual reference prefix. -/
theorem cfrDComposedChildProfile_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
      (cfrDComposedChildProfile M trunk fallback cut remaining loss solve)
      (cfrDInformationFallback M fallback) who cut =
    unilateralReferenceLaw (fullInformation M) trunk
      (cfrDInformationFallback M fallback) who cut :=
  cfrDDepthProfile_referenceLaw (fullInformation M) (fullObservationClock M)
    trunk _ (cfrDInformationFallback M fallback) who cut

/-- The factual joint-law floor controls every supported private-type loss. -/
theorem cfrDComposedChildProfile_referenceBudget
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (positive : 0 < loss) (solve : PBSChildSolve M) (utility : E.History → Fin 2 → ℝ)
    (smaller : PBSChildSolveAccurate M solve utility remaining)
    (who : Fin 2) (obs : List M.PublicSignal) (root type : PublicRootType M obs who)
    (sampled : (type.val, true) ∈ (((fullInformation M).runBehavioral
      (cfrDComposedChildProfile M trunk fallback cut remaining loss solve) cut).map
      (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support) :
    ∃ (own : FinDist (PublicRootType M obs who)) (error : ℝ),
      IsNash (behavioralBeliefForm (fullInformation M)
        ((cfrDReferenceSlice M
          (cfrDComposedChildProfile M trunk fallback cut remaining loss solve)
          (cfrDInformationFallback M fallback) cut remaining root).mixture own) remaining)
        (euPreferenceWithin error utility)
        (cfrDComposedChildProfile M trunk fallback cut remaining loss solve) ∧
      type ∈ own.support ∧ error ≤ own.prob type * loss := by
  classical
  let base := cfrDComposedChildProfile M trunk fallback cut remaining loss solve
  have prefixLaw : (fullInformation M).runBehavioral base cut =
      (fullInformation M).runBehavioral trunk cut :=
    cfrDComposedChildProfile_prefixLaw M trunk fallback cut remaining loss solve
  have possible : CFRDFactualChildPossible M base cut remaining obs := by
    have witness := sampled
    rw [FinDist.support_map] at witness
    obtain ⟨h, reached, same⟩ := witness
    refine ⟨h, ⟨?_, congrArg Prod.snd same⟩, reached⟩
    rw [publicRoot_trace_eq]
    have known := congrArg AOH.publicHistory (congrArg Prod.fst same)
    simpa only [publicHistory_infoOf, cfrD_publicRootType_public M type] using known
  have original : CFRDFactualChildPossible M trunk cut remaining obs := by
    simpa only [CFRDFactualChildPossible, prefixLaw] using possible
  let belief := cfrDFactualChildBelief M base cut remaining obs possible
  let own := cfrDFactualChildTypeLaw M base cut remaining possible root
  have beliefExt (first second : PublicBelief (fullInformation M).toInfoSignals obs)
      (equal : first.law = second.law) : first = second := by
    cases first
    cases second
    cases equal
    rfl
  have beliefEq : belief = cfrDFactualChildBelief M trunk cut remaining obs original := by
    apply beliefExt
    dsimp only [belief, cfrDFactualChildBelief]
    simp only [prefixLaw]
  have mixture : (cfrDReferenceSlice M base (cfrDInformationFallback M fallback)
      cut remaining root).mixture own = belief :=
    beliefExt _ _ (cfrDFactualChild_referenceMixture M base
      (cfrDInformationFallback M fallback) cut remaining possible root)
  have supported : type ∈ own.support :=
    (cfrDFactualChildTypeLaw_support M base cut remaining possible root type).mpr sampled
  have floor : belief.law.positiveMassFloor ≤ own.prob type :=
    belief.law.positiveMassFloor_le_map
      (fun h => (publicRootMemory M root).typeAt ((fullInformation M).infoOf who h.trace))
      type supported
  refine ⟨own, belief.law.positiveMassFloor * loss, ?_, supported,
    mul_le_mul_of_nonneg_right floor positive.le⟩
  rw [mixture, beliefEq]
  exact cfrDComposedChildProfile_isNash M trunk fallback cut remaining loss positive
    solve utility smaller obs original

/-- Counterfactual completion retains factual children and fills zero-own-reach types. -/
def cfrDComposedChildContinuation (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (utility : E.History → Fin 2 → ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  let base := cfrDComposedChildProfile M trunk fallback cut remaining loss solve
  cfrDCompleteZeroReach (fullInformation M) base
    (cfrDPublicResponseCompletion M cut
      (cfrDReferenceTable M base (cfrDInformationFallback M fallback) cut remaining)
      (cfrDInformationFallback M fallback) remaining utility base)

/-- Completion preserves the same incumbent reference law. -/
theorem cfrDComposedChildContinuation_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (utility : E.History → Fin 2 → ℝ) (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
      (cfrDComposedChildContinuation M trunk fallback cut remaining loss solve utility)
      (cfrDInformationFallback M fallback) who cut =
    unilateralReferenceLaw (fullInformation M) trunk
      (cfrDInformationFallback M fallback) who cut := by
  unfold cfrDComposedChildContinuation
  rw [cfrDCompleteZeroReach_referenceLaw (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals), cfrDComposedChildProfile_referenceLaw]

/-- The smaller solver theorem implies all live reference-query bounds,
including queries omitted by the factual parent's zero own reach. -/
theorem cfrDComposedChildContinuation_leafOptimal
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat) (loss : ℝ)
    (positive : 0 < loss) (solve : PBSChildSolve M) (utility : E.History → Fin 2 → ℝ)
    (smaller : PBSChildSolveAccurate M solve utility remaining) (who : Fin 2) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDComposedChildContinuation M trunk fallback cut remaining loss solve utility)
      (cfrDInformationFallback M fallback) who (fun h => utility h who) cut remaining loss := by
  apply cfrDReferenceTable_approx_leafOptimal
  · exact positive.le
  · exact cfrDComposedChildProfile_referenceBudget M trunk fallback cut remaining loss positive
      solve utility smaller who

end GameTheory.ReBeL
