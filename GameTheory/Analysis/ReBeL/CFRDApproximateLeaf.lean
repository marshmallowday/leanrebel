/-
# Probability-budgeted approximate child games supply the leaf contract

Factual queries use canonical approximate PBS Nash with an error budget
scaled by the queried type's probability. Nonfactual queries use the existing
constructed zero-own-reach response. The reference table supplies compatible
kernels and legal public-state splicing. No conditional payoff inequality is
stored in the query premises, and no finite child algorithm is assumed built.
-/

import GameTheory.Analysis.ReBeL.PBSApproximateOptimality
import GameTheory.Analysis.ReBeL.CFRDReferenceSlice

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- A zero-own-reach root is solved exactly by the constructed response.
A supported root instead uses the probability-budgeted approximate Nash
estimate. Neither branch silently upgrades root error to conditional error. -/
theorem cfrDPublicResponseCompletion_loss_of_root_cases (cut : Nat)
    (table : CFRDPublicSliceTable M) (fallback : Profile (fullInformation M).strategicSignature)
    (remaining : Nat) (utility : E.History → ι → ℝ)
    (base : Profile (fullInformation M).behavioralSignature)
    {observations : List M.PublicSignal} {who : ι} {T : Type ut}
    (slice : TypeBeliefSlice (fullInformation M) observations who T)
    (present : table observations who = some ⟨T, slice⟩) (type : T)
    (atCut : ∀ h ∈ (slice.kernel type).law.support, h.trace.length = cut)
    (opponents : ∀ h ∈ (slice.kernel type).law.support, ∀ other, other ≠ who →
      (fullInformation M).playerReachProbability base other h.trace ≠ 0)
    (loss : ℝ) (nonneg : 0 ≤ loss)
    (rootCase :
      (∀ h ∈ (slice.kernel type).law.support,
        (fullInformation M).playerReachProbability base who h.trace = 0) ∨
      ∃ (own : FinDist T) (error : ℝ),
        IsNash (behavioralBeliefForm (fullInformation M) (slice.mixture own) remaining)
          (euPreferenceWithin error utility) base ∧ type ∈ own.support ∧
        error ≤ own.prob type * loss ∧
        ∀ h ∈ (slice.kernel type).law.support,
          (fullInformation M).playerReachProbability base who h.trace ≠ 0) :
    slice.infoValue fallback remaining (fun h => utility h who) base type -
      (PublicBelief.continuationLaw (fullInformation M)
        (cfrDCompleteZeroReach (fullInformation M) base
          (cfrDPublicResponseCompletion M cut table fallback remaining utility base))
        remaining (slice.kernel type)).expect (fun h => utility h who) ≤ loss := by
  let completion := cfrDPublicResponseCompletion M cut table fallback remaining utility base
  rcases rootCase with zero | ⟨own, error, equilibrium, supported, budget, positive⟩
  · have actual := cfrDPublicResponseCompletion_value_of_root_cases M cut table fallback
      remaining utility base slice present type atCut opponents (Or.inl zero)
    rw [actual, sub_self]
    exact nonneg
  · have allPositive : ∀ h ∈ (slice.kernel type).law.support, ∀ player,
        (fullInformation M).playerReachProbability base player h.trace ≠ 0 := by
      intro h member player
      by_cases same : player = who
      · subst player
        exact positive h member
      · exact opponents h member player same
    have actual : (PublicBelief.continuationLaw (fullInformation M)
          (cfrDCompleteZeroReach (fullInformation M) base completion)
          remaining (slice.kernel type)).expect (fun h => utility h who) =
        slice.conditionalPayoff base remaining (fun h => utility h who) (base who) type := by
      simpa only [TypeBeliefSlice.conditionalPayoff, Profile.update_eq_self] using
        slice.completeZeroReach_actualPayoff (fullSignals_perfectRecall M.toInfoSignals)
          base completion remaining (fun h => utility h who) type allPositive
    have bound := slice.conditional_gain_le_of_mass_budget
      (fullSignals_perfectRecall M.toInfoSignals) fallback remaining utility own base error loss
      equilibrium type supported budget
      (slice.simultaneousResponse fallback remaining (fun h => utility h who) base).toBehavioral
    rw [slice.simultaneousResponse_attains] at bound
    rw [actual]
    exact bound

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Factual query games supply approximate Nash with a mass-proportional
budget. Entirely unvisited public states need no factual posterior or Nash;
the original counterfactual response construction supplies their zero loss. -/
theorem cfrDPublicResponseCompletion_approx_leafOptimal (cut remaining : Nat)
    (table : CFRDPublicSliceTable M) (fallback : Profile (fullInformation M).strategicSignature)
    (utility : E.History → ι → ℝ) (base : Profile (fullInformation M).behavioralSignature)
    (who : ι) (loss : ℝ) (nonneg : 0 ≤ loss)
    (queries : ∀ info : (fullInformation M).InfoState who,
      (info, true) ∈ ((unilateralReferenceLaw (fullInformation M) base fallback who cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support →
      ∃ (observations : List M.PublicSignal) (T : Type ut)
        (slice : TypeBeliefSlice (fullInformation M) observations who T) (type : T),
        table observations who = some ⟨T, slice⟩ ∧
        (slice.kernel type).law =
          (unilateralReferenceLaw (fullInformation M) base fallback who cut).condOnFibre
            (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
            (info, true) ∧
        ((info, true) ∈ (((fullInformation M).runBehavioral base cut).map
          (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support →
          ∃ (own : FinDist T) (error : ℝ),
            IsNash (behavioralBeliefForm (fullInformation M) (slice.mixture own) remaining)
              (euPreferenceWithin error utility) base ∧ type ∈ own.support ∧
            error ≤ own.prob type * loss)) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDCompleteZeroReach (fullInformation M) base
        (cfrDPublicResponseCompletion M cut table fallback remaining utility base))
      fallback who (fun h => utility h who) cut remaining loss := by
  classical
  intro target info sampled
  rw [cfrDCompleteZeroReach_referenceLaw (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals)] at sampled ⊢
  obtain ⟨observations, T, slice, type, present, kernel, onPath⟩ := queries info sampled
  have roots (history : E.History) (reached : history ∈ (slice.kernel type).law.support) :
      history ∈ ((unilateralReferenceLaw (fullInformation M) base fallback who cut).condOnFibre
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
        (info, true)).support := by simpa only [kernel] using reached
  have opponents : ∀ h ∈ (slice.kernel type).law.support, ∀ other, other ≠ who →
      (fullInformation M).playerReachProbability base other h.trace ≠ 0 := by
    intro history reached other different
    exact cfrDReference_conditional_opponents (fullInformation M) base fallback who cut
      _ (info, true) sampled history (roots history reached) other different
  have gap : slice.infoValue fallback remaining (fun h => utility h who) base type -
      (PublicBelief.continuationLaw (fullInformation M)
        (cfrDCompleteZeroReach (fullInformation M) base
          (cfrDPublicResponseCompletion M cut table fallback remaining utility base)) remaining
        (slice.kernel type)).expect (fun h => utility h who) ≤ loss := by
    apply cfrDPublicResponseCompletion_loss_of_root_cases M cut table fallback remaining
      utility base slice present type
    · intro history reached
      exact cfrDReference_live_rootDepth (fullInformation M) base fallback who cut remaining
        info sampled history (roots history reached)
    · exact opponents
    · exact nonneg
    · by_cases factual : (info, true) ∈ (((fullInformation M).runBehavioral base cut).map
          (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support
      · obtain ⟨own, error, equilibrium, supported, budget⟩ := onPath factual
        refine Or.inr ⟨own, error, equilibrium, supported, budget, ?_⟩
        intro history reached
        exact (cfrDReference_factual_support_iff (fullInformation M)
          (fullSignals_perfectRecall M.toInfoSignals) base fallback who cut _ Prod.fst
          (fun _ => rfl) (info, true) sampled history (roots history reached)).mp factual
      · left
        intro history reached
        exact cfrDReference_factual_absent_own_zero (fullInformation M)
          (fullSignals_perfectRecall M.toInfoSignals) base fallback who cut _ Prod.fst
          (fun _ => rfl) (info, true) sampled factual history (roots history reached)
  have better := slice.conditionalPayoff_le_infoValue
    (fullSignals_perfectRecall M.toInfoSignals) fallback remaining
    (fun h => utility h who) base type target
  rw [← slice.completeZeroReach_conditionalPayoff
    (fullSignals_perfectRecall M.toInfoSignals) base
    (cfrDPublicResponseCompletion M cut table fallback remaining utility base) remaining
    (fun h => utility h who) target type opponents] at better
  have bound := (sub_le_sub_right better _).trans gap
  unfold conditionalOracleValue cfrDLeafGain
  rw [FinDist.expect_sub]
  simpa only [TypeBeliefSlice.conditionalPayoff, PublicBelief.continuationLaw,
    FinDist.expect_bind, kernel] using bound

/-- The actual reference table removes query-existence, kernel-matching and
policy-agreement premises. Only probability-budgeted factual approximate Nash
remains to be supplied by a finite child solver. -/
theorem cfrDReferenceTable_approx_leafOptimal
    (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) (loss : ℝ) (nonneg : 0 ≤ loss)
    (factual : ∀ (observations : List M.PublicSignal)
      (root type : PublicRootType M observations who),
      (type.val, true) ∈ (((fullInformation M).runBehavioral base cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support →
      ∃ (own : FinDist (PublicRootType M observations who)) (error : ℝ),
        IsNash (behavioralBeliefForm (fullInformation M)
          ((cfrDReferenceSlice M base fallback cut remaining root).mixture own) remaining)
          (euPreferenceWithin error utility) base ∧ type ∈ own.support ∧
        error ≤ own.prob type * loss) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDCompleteZeroReach (fullInformation M) base
        (cfrDPublicResponseCompletion M cut (cfrDReferenceTable M base fallback cut remaining)
          fallback remaining utility base)) fallback who (fun h => utility h who)
      cut remaining loss := by
  apply cfrDPublicResponseCompletion_approx_leafOptimal M cut remaining _ fallback utility
    base who loss nonneg
  intro info sampled
  obtain ⟨observations, root, type, present, same, kernel⟩ :=
    cfrDReferenceTable_query M base fallback cut remaining who info sampled
  refine ⟨observations, PublicRootType M observations who,
    cfrDReferenceSlice M base fallback cut remaining root, type, present, kernel, ?_⟩
  intro reached
  apply factual observations root type
  simpa only [same] using reached

end GameTheory.ReBeL
