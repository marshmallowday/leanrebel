/-
# Theorem 1 from the game and joint public belief alone

The full-AOH factory constructs the finite infostate domain, remembered-type
projection and compatible conditional kernels. Finite Nash existence supplies
the equilibrium; no linearity, minimax or value-vector certificate is assumed.
The focal player is labeled zero. The extension depends on the base belief,
but works for every signed weight vector and agrees with all simplex values.
-/

import GameTheory.Analysis.ReBeL.PBSFullAOH
import GameTheory.Analysis.ReBeL.ValueDifferential

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- Existential Theorem 1 on the actual finite joint-PBS game. All infostate
and kernel premises are constructed, and a canonical Nash profile is produced.
This statement includes zero-mass types and does not require differentiability. -/
theorem theorem1_fullAOH {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile (fullInformation M).strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) :
    let slice := fullAOHBeliefSlice M belief 0
    let own := fullAOHOwnLaw M belief 0
    ∃ (profile : Profile (fullInformation M).behavioralSignature)
      (extension : (PublicRootType M observations 0 → ℝ) → ℝ),
      IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
        (euPreference utility) profile ∧
      Set.EqOn extension (slice.value fallback fuel (fun history => utility history 0))
        (stdSimplex ℝ (PublicRootType M observations 0)) ∧
      ConcaveOn ℝ Set.univ extension ∧
      (∀ point, extension point ≤ extension own.prob +
        ∑ type, slice.centeredVector fallback fuel (fun history => utility history 0)
          own.prob profile type * (point type - own.prob type)) ∧
      (∀ type, slice.infoValue fallback fuel (fun history => utility history 0) profile type =
        expectedUtility utility 0
          ((behavioralBeliefForm (fullInformation M) belief fuel).play profile) +
        slice.centeredVector fallback fuel (fun history => utility history 0)
          own.prob profile type) := by
  dsimp only
  obtain ⟨profile, equilibrium⟩ := exists_publicBelief_nash (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) (fullObservationClock M)
    fallback belief fuel utility
  have reconstructed : IsNash (behavioralBeliefForm (fullInformation M)
      ((fullAOHBeliefSlice M belief 0).mixture (fullAOHOwnLaw M belief 0)) fuel)
      (euPreference utility) profile := by
    rw [fullAOHBeliefSlice_eq]
    exact equilibrium
  obtain ⟨extension, agrees, concave, supporting, identity⟩ :=
    (fullAOHBeliefSlice M belief 0).theorem1_canonicalPBS
      (fullSignals_perfectRecall M.toInfoSignals) fallback fuel utility hzero
      (fullAOHOwnLaw M belief 0) profile reconstructed
  refine ⟨profile, extension, equilibrium, agrees, concave, supporting, ?_⟩
  simpa only [fullAOHBeliefSlice_eq] using identity

namespace TypeBeliefSlice

variable {M : InformationModel.{0, us, ua, up, uq, uk} E}
variable {observations : List M.PublicSignal} {T : Type*} [Fintype T]
variable (slice : TypeBeliefSlice M observations 0 T)

/-- The fixed branch's continuous linear functional evaluates to the actual
conditional best-response payoff, with the finite sum orientation reconciled. -/
theorem branchMap_eq_branch (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (own : FinDist T) (profile : Profile M.behavioralSignature) :
    ValueDifferential.branchMap (slice.infoValue fallback fuel payoff profile) own.prob =
      slice.branch fallback fuel payoff own profile := by
  rw [ValueDifferential.branchMap_apply, slice.branch_eq_weightedBranch]
  unfold weightedBranch
  apply Finset.sum_congr rfl
  intro type _
  exact mul_comm _ _

/-- Appendix F's differential calculation is valid for each fixed opponent
branch. Equation (12) uses the actual canonical PBS Nash payoff; no derivative
or concavity of the radial lower envelope is smuggled into this statement. -/
theorem normalized_branch_derivative_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) :
    HasFDerivAt
      (ValueDifferential.normalizedBranch
        (slice.infoValue fallback fuel (fun history => utility history 0) profile))
      (ValueDifferential.branchMap
        (slice.infoValue fallback fuel (fun history => utility history 0) profile) -
        expectedUtility utility 0
          ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) •
            ValueDifferential.massMap) own.prob := by
  have mass : ValueDifferential.massMap own.prob = 1 := by
    rw [ValueDifferential.massMap_apply]
    exact own.prob_mem_stdSimplex.2
  have derivative := ValueDifferential.normalizedBranch_centered_derivative
    (slice.infoValue fallback fuel (fun history => utility history 0) profile) own.prob mass
  unfold ValueDifferential.centeredMap at derivative
  rw [slice.branchMap_eq_branch, slice.branch_eq_equilibriumPayoff hrecall fallback fuel
    utility own profile equilibrium] at derivative
  exact derivative

end TypeBeliefSlice
end GameTheory.ReBeL
