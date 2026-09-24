/-
# Nested noisy depth solvers at factual public children

The child of the actual parent trunk is itself a budgeted depth-limited solve,
not a full-root CFR replacement. Its factual joint law determines the accuracy
allocation. Public splicing and zero-own-reach completion then derive the
all-query counterfactual child contract. The deepest backend remains full-root
CFR; this is one constructed nesting step, not arbitrary-depth recursion.
-/

import GameTheory.Analysis.ReBeL.PBSInformationDepthBudget
import GameTheory.Analysis.ReBeL.CFRDInformationContinuation

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- A predictor may inspect the modeled joint root and the rooted query.
It has no actual hidden input history or unknown execution opponent argument. -/
abbrev PBSDepthNoiseFamily := (roots : FinDist E.History) → PBSRootDepthNoise M roots

/-- A numerical prediction bound at each actual joint-root allocation.
This is not a child Nash, regret, or recursive-security certificate. -/
def PBSDepthChildNoiseBound (fallback : Profile M.strategicSignature)
    (childCut childRemaining : Nat) (loss : ℝ) (noise : PBSDepthNoiseFamily M) : Prop :=
  ∀ roots n trunk who info, |noise roots n trunk who info| ≤
    pbsDepthAllocationError
      (pbsRootDepthErrorFactor M roots fallback childCut childRemaining)
      (roots.positiveMassFloor * loss)

/-- A concrete nonzero predictor using half of each root's allocated allowance. -/
def pbsDepthChildHalfNoise (fallback : Profile M.strategicSignature)
    (childCut childRemaining : Nat) (loss : ℝ) : PBSDepthNoiseFamily M :=
  fun roots _ _ _ _ =>
    pbsDepthAllocationError
      (pbsRootDepthErrorFactor M roots fallback childCut childRemaining)
      (roots.positiveMassFloor * loss) / 2

/-- Every positive requested child loss gives a strictly positive actual bias. -/
theorem pbsDepthChildHalfNoise_pos (fallback : Profile M.strategicSignature)
    (childCut childRemaining : Nat) (loss : ℝ) (positive : 0 < loss) :
    ∀ roots n trunk who info,
      0 < pbsDepthChildHalfNoise M fallback childCut childRemaining loss
        roots n trunk who info := by
  intro roots n trunk who info
  have allowance := pbsDepthAllocationError_pos
    (pbsRootDepthErrorFactor M roots fallback childCut childRemaining)
    (roots.positiveMassFloor * loss)
    (mul_pos (FinDist.positiveMassFloor_pos roots) positive)
  dsimp only [pbsDepthChildHalfNoise]
  positivity

/-- The same constructed predictor meets the complete numerical contract. -/
theorem pbsDepthChildHalfNoise_bounded (fallback : Profile M.strategicSignature)
    (childCut childRemaining : Nat) (loss : ℝ) (positive : 0 < loss) :
    PBSDepthChildNoiseBound M fallback childCut childRemaining loss
      (pbsDepthChildHalfNoise M fallback childCut childRemaining loss) := by
  intro roots n trunk who info
  have allowance := pbsDepthAllocationError_pos
    (pbsRootDepthErrorFactor M roots fallback childCut childRemaining)
    (roots.positiveMassFloor * loss)
    (mul_pos (FinDist.positiveMassFloor_pos roots) positive)
  dsimp only [pbsDepthChildHalfNoise]
  rw [abs_of_pos (by positivity)]
  linarith

/-- Live factual public roots receive a computed noisy depth-limited child.
Impossible observations retain the same explicit legal fallback as before. -/
def cfrDDepthChildTable (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M) :
    List M.PublicSignal → Profile (fullInformation M).behavioralSignature := fun obs => by
  classical
  exact if possible : CFRDFactualChildPossible M trunk cut (childCut + childRemaining) obs then
    let belief := cfrDFactualChildBelief M trunk cut (childCut + childRemaining) obs possible
    pbsInformationConditionalDepthProfile M belief fallback (fun who h => utility h who)
      childCut childRemaining bound loss (noise belief.law)
  else fun who => (cfrDInformationFallback M fallback who).toBehavioral

/-- Splice only after the actual public cut, preserving the entire past trunk. -/
def cfrDDepthChildProfile (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M) :
    Profile (fullInformation M).behavioralSignature :=
  cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk
    (cfrDPublicContinuation M cut
      (cfrDDepthChildTable M trunk fallback cut childCut childRemaining utility bound loss noise))

/-- Installing the computed child does not alter an already searched decision. -/
theorem cfrDDepthChildProfile_before
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (before : (fullObservationClock M).depth who info < cut) :
    cfrDDepthChildProfile M trunk fallback cut childCut childRemaining utility bound loss noise
      who info = trunk who info := by
  simp only [cfrDDepthChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_pos before]

/-- Preserve the full factual joint cut law, not merely its public marginal. -/
theorem cfrDDepthChildProfile_prefixLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M) :
    (fullInformation M).runBehavioral
      (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining utility bound loss noise)
      cut = (fullInformation M).runBehavioral trunk cut := by
  apply runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
  exact cfrDDepthChildProfile_before M trunk fallback cut childCut childRemaining
    utility bound loss noise

/-- Every legal descendant retains its public child's complete local policy,
including descendants of zero probability under the current policy. -/
theorem cfrDDepthChildProfile_of_reaches
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M)
    (who : Fin 2) (first later : E.History) (atCut : first.trace.length = cut) {fuel : Nat}
    (reaches : E.ReachesWithin fuel first later) :
    cfrDDepthChildProfile M trunk fallback cut childCut childRemaining utility bound loss noise
      who ((fullInformation M).infoOf who later.trace) =
    cfrDDepthChildTable M trunk fallback cut childCut childRemaining utility bound loss noise
      (publicTrace M.toInfoSignals first.trace) who
      ((fullInformation M).infoOf who later.trace) := by
  have after : ¬ (fullObservationClock M).depth who
      ((fullInformation M).infoOf who later.trace) < cut := by
    rw [(fullObservationClock M).correct]
    have monotone := reaches.trace_length_le
    omega
  simp only [cfrDDepthChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_neg after]
  exact cfrDPublicContinuation_eq_of_reaches M cut _ who first later atCut reaches

/-- The public splice executes the same complete joint continuation law. -/
theorem cfrDDepthChildProfile_beliefLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M)
    {obs : List M.PublicSignal} (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut) (fuel : Nat) :
    PublicBelief.continuationLaw (fullInformation M)
      (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining utility bound loss noise)
      fuel belief =
    PublicBelief.continuationLaw (fullInformation M)
      (cfrDDepthChildTable M trunk fallback cut childCut childRemaining
        utility bound loss noise obs) fuel belief := by
  apply FinDist.bind_congr
  intro first supported
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ who
  simpa only [rootPublic] using cfrDDepthChildProfile_of_reaches M trunk fallback cut
    childCut childRemaining utility bound loss noise who first later (atCut first supported) reaches

/-- Every unilateral behavioral deviation also preserves its complete law. -/
theorem cfrDDepthChildProfile_deviationLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M)
    {obs : List M.PublicSignal} (belief : PublicBelief (fullInformation M).toInfoSignals obs)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut) (fuel : Nat)
    (who : Fin 2) (target : (fullInformation M).BehavioralPolicy who) :
    PublicBelief.continuationLaw (fullInformation M)
      (Profile.update (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining
        utility bound loss noise) who target) fuel belief =
    PublicBelief.continuationLaw (fullInformation M)
      (Profile.update (cfrDDepthChildTable M trunk fallback cut childCut childRemaining
        utility bound loss noise obs) who target) fuel belief := by
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
    simpa only [rootPublic] using cfrDDepthChildProfile_of_reaches M trunk fallback cut
      childCut childRemaining utility bound loss noise player first later (atCut first supported)
      reaches

/-- Factual child Nash accuracy follows from the constructed depth solver and
its numeric predictor bound. No child equilibrium certificate is supplied. -/
theorem cfrDDepthChildProfile_isNash
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h who, |utility h who| ≤ bound) (noise : PBSDepthNoiseFamily M)
    (noiseBound : PBSDepthChildNoiseBound M fallback childCut childRemaining loss noise)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut (childCut + childRemaining) obs) :
    IsNash (behavioralBeliefForm (fullInformation M)
      (cfrDFactualChildBelief M trunk cut (childCut + childRemaining) obs possible)
      (childCut + childRemaining))
      (euPreferenceWithin
        ((cfrDFactualChildBelief M trunk cut
          (childCut + childRemaining) obs possible).law.positiveMassFloor * loss) utility)
      (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining
        utility bound loss noise) := by
  let belief := cfrDFactualChildBelief M trunk cut (childCut + childRemaining) obs possible
  have equilibrium := pbsInformationConditionalDepthProfile_isNash M belief fallback
    (fun who h => utility h who) zeroSum childCut childRemaining bound loss nonneg positive
    (fun who h => bounded h who) (noise belief.law) (noiseBound belief.law)
  have table : cfrDDepthChildTable M trunk fallback cut childCut childRemaining
      utility bound loss noise obs =
      pbsInformationConditionalDepthProfile M belief fallback (fun who h => utility h who)
        childCut childRemaining bound loss (noise belief.law) := by
    simp only [cfrDDepthChildTable, dif_pos possible, belief]
  rw [isNash_iff] at equilibrium ⊢
  intro who target
  have atCut := cfrDFactualChildBelief_atCut M trunk cut
    (childCut + childRemaining) obs possible
  simpa only [euPreferenceWithin_apply, behavioralBeliefForm,
    cfrDDepthChildProfile_beliefLaw M trunk fallback cut childCut childRemaining
      utility bound loss noise _ atCut,
    cfrDDepthChildProfile_deviationLaw M trunk fallback cut childCut childRemaining
      utility bound loss noise _ atCut, table] using equilibrium who target

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- The reference cut law is independent of this replacement continuation. -/
theorem cfrDDepthChildProfile_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M)
    (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
      (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining utility bound loss noise)
      (cfrDInformationFallback M fallback) who cut =
    unilateralReferenceLaw (fullInformation M) trunk
      (cfrDInformationFallback M fallback) who cut :=
  cfrDDepthProfile_referenceLaw (fullInformation M) (fullObservationClock M)
    trunk _ (cfrDInformationFallback M fallback) who cut

/-- The actual joint mass floor discharges every supported reference-type loss. -/
theorem cfrDDepthChildProfile_referenceBudget
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h player, |utility h player| ≤ bound) (noise : PBSDepthNoiseFamily M)
    (noiseBound : PBSDepthChildNoiseBound M fallback childCut childRemaining loss noise)
    (who : Fin 2) (obs : List M.PublicSignal) (root type : PublicRootType M obs who)
    (sampled : (type.val, true) ∈ (((fullInformation M).runBehavioral
      (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining utility bound loss noise)
      cut).map (fun h =>
        ((fullInformation M).infoOf who h.trace,
          cfrDCutLive (childCut + childRemaining) h))).support) :
    ∃ (own : FinDist (PublicRootType M obs who)) (error : ℝ),
      IsNash (behavioralBeliefForm (fullInformation M)
        ((cfrDReferenceSlice M
          (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining
            utility bound loss noise)
          (cfrDInformationFallback M fallback) cut (childCut + childRemaining) root).mixture own)
        (childCut + childRemaining))
        (euPreferenceWithin error utility)
        (cfrDDepthChildProfile M trunk fallback cut childCut childRemaining
          utility bound loss noise) ∧
      type ∈ own.support ∧ error ≤ own.prob type * loss := by
  classical
  let base := cfrDDepthChildProfile M trunk fallback cut childCut childRemaining
    utility bound loss noise
  let remaining := childCut + childRemaining
  have prefixLaw : (fullInformation M).runBehavioral base cut =
      (fullInformation M).runBehavioral trunk cut :=
    cfrDDepthChildProfile_prefixLaw M trunk fallback cut childCut childRemaining
      utility bound loss noise
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
  exact cfrDDepthChildProfile_isNash M trunk fallback cut childCut childRemaining
    utility zeroSum bound loss nonneg positive bounded noise noiseBound obs original

/-- Complete omitted zero-own-reach types, retaining the computed factual child. -/
def cfrDDepthChildContinuation (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M) :
    Profile (fullInformation M).behavioralSignature :=
  let base := cfrDDepthChildProfile M trunk fallback cut childCut childRemaining
    utility bound loss noise
  cfrDCompleteZeroReach (fullInformation M) base
    (cfrDPublicResponseCompletion M cut
      (cfrDReferenceTable M base (cfrDInformationFallback M fallback)
        cut (childCut + childRemaining))
      (cfrDInformationFallback M fallback) (childCut + childRemaining) utility base)

/-- Zero-own-reach completion also preserves the incumbent reference cut law. -/
theorem cfrDDepthChildContinuation_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (noise : PBSDepthNoiseFamily M)
    (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
      (cfrDDepthChildContinuation M trunk fallback cut childCut childRemaining
        utility bound loss noise) (cfrDInformationFallback M fallback) who cut =
    unilateralReferenceLaw (fullInformation M) trunk
      (cfrDInformationFallback M fallback) who cut := by
  unfold cfrDDepthChildContinuation
  rw [cfrDCompleteZeroReach_referenceLaw (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals), cfrDDepthChildProfile_referenceLaw]

/-- The computed nested solver satisfies every live counterfactual child query,
including zero factual reach. Only numeric noise accuracy is a supplied bound. -/
theorem cfrDDepthChildContinuation_leafOptimal
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut childCut childRemaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h player, |utility h player| ≤ bound) (noise : PBSDepthNoiseFamily M)
    (noiseBound : PBSDepthChildNoiseBound M fallback childCut childRemaining loss noise)
    (who : Fin 2) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDDepthChildContinuation M trunk fallback cut childCut childRemaining
        utility bound loss noise) (cfrDInformationFallback M fallback) who
      (fun h => utility h who) cut (childCut + childRemaining) loss := by
  apply cfrDReferenceTable_approx_leafOptimal
  · exact positive.le
  · exact cfrDDepthChildProfile_referenceBudget M trunk fallback cut childCut childRemaining
      utility zeroSum bound loss nonneg positive bounded noise noiseBound who

end GameTheory.ReBeL
