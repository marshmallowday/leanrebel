/-
# Concave ambient extensions of the actual PBS value

The branches here are conditional maxima in the canonical PBS continuation
runner, and their minimum is identified with an existing Nash equilibrium's
value. Finite payoff bounds make their lower envelope real-valued on every
signed vector. This produces a concave extension even around boundary beliefs,
without substituting Appendix F's nonconcave radial normalization.
-/

import GameTheory.Analysis.ReBeL.PBSOptimalOpponent
import GameTheory.Analysis.ReBeL.ValueEnvelope
import GameTheory.Math.Probability.Simplex

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable {M : InformationModel.{0, us, ua, up, uq, uk} E}
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- Finite actual history payoffs bound every conditional best response,
including all off-path kernels and every opponent behavioral strategy. -/
theorem infoValue_uniform_bound (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) :
    ∃ bound : ℝ, ∀ (opponents : Profile M.behavioralSignature) type,
      |slice.infoValue fallback fuel payoff opponents type| ≤ bound := by
  obtain ⟨bound, bounded⟩ := (Set.finite_range fun history => |payoff history|).bddAbove
  refine ⟨bound, fun opponents type => ?_⟩
  unfold infoValue conditionalPayoff
  exact FinDist.abs_expect_le_of_abs_bound _ _ fun history _ => bounded ⟨history, rfl⟩

variable [Fintype T]

/-- The lower envelope of actual conditional best-response branches, defined
on all real own-weight vectors. It is not a negative-weight matrix game. -/
def ambientValue (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (weight : T → ℝ) : ℝ :=
  ValueGeometry.envelope (slice.infoValue fallback fuel payoff) weight

/-- Finite payoff bounds discharge the infimum's boundedness obligation
uniformly, even at signed vectors outside the probability simplex. -/
theorem branches_bounded_below (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) (weight : T → ℝ) :
    BddBelow (Set.range fun opponents : Profile M.behavioralSignature =>
      ValueGeometry.pairing (slice.infoValue fallback fuel payoff opponents) weight) := by
  obtain ⟨bound, bounded⟩ := slice.infoValue_uniform_bound fallback fuel payoff
  exact ValueGeometry.bounded_below_of_abs_bound _ bound bounded weight

/-- The envelope is the actual PBS Nash value on probability weights. Its
attaining branch and its lower bound were derived from legal strategies. -/
theorem ambientValue_eq_value (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T) :
    slice.ambientValue fallback fuel (fun history => utility history who) own.prob =
      slice.value hrecall clock fallback fuel utility own := by
  have least := slice.value_isLeast hrecall clock fallback fuel utility hzero own
  simp only [branch_eq_weightedBranch] at least
  exact least.csInf_eq

/-- This agreement holds at every point of the entire simplex, including
zero-mass coordinates and independently of an equilibrium selection. -/
theorem ambientValue_eq_value_of_simplex
    (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    {weight : T → ℝ} (normalized : weight ∈ stdSimplex ℝ T) :
    slice.ambientValue fallback fuel (fun history => utility history who) weight =
      slice.value hrecall clock fallback fuel utility (FinDist.ofSimplex normalized) := by
  simpa only [FinDist.prob_ofSimplex] using
    slice.ambientValue_eq_value hrecall clock fallback fuel utility hzero
      (FinDist.ofSimplex normalized)

/-- The lower-envelope proof does not need differentiability, a unique Nash
equilibrium, or a unique best-response policy at any type. -/
theorem ambientValue_concave (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) :
    ConcaveOn ℝ Set.univ (slice.ambientValue fallback fuel payoff) := by
  let : Nonempty (Profile M.behavioralSignature) :=
    ⟨fun player => (fallback player).toBehavioral⟩
  exact ValueGeometry.envelope_concave _ (slice.branches_bounded_below fallback fuel payoff)

/-- Lemma 2's own-belief concavity, with the same compatible conditional
joint history kernels fixed as in the actual PBS value agreement above. -/
theorem value_concaveOn_simplex (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ T) (slice.ambientValue fallback fuel payoff) :=
  (slice.ambientValue_concave fallback fuel payoff).subset
    (fun _ _ => Set.mem_univ _) (convex_stdSimplex ℝ T)

/-- A centered conditional value vector. At a Nash opponent it supplies
support; it is not claimed to be a derivative at nonsmooth beliefs. -/
def centeredInfoVector (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (base : FinDist T)
    (opponents : Profile M.behavioralSignature) (type : T) : ℝ :=
  slice.infoValue fallback fuel (fun history => utility history who) opponents type -
    slice.value hrecall clock fallback fuel utility base

/-- An affine mass correction, not degree-zero radial normalization. -/
def ambientExtension (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (base : FinDist T) (point : T → ℝ) : ℝ :=
  ValueGeometry.extension (slice.infoValue fallback fuel (fun history => utility history who))
    (slice.value hrecall clock fallback fuel utility base) point

/-- The corrected extension agrees with the same actual PBS value at every
probability distribution, not just at the chosen base or in the interior. -/
theorem ambientExtension_agrees (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (base own : FinDist T) :
    slice.ambientExtension hrecall clock fallback fuel utility base own.prob =
      slice.value hrecall clock fallback fuel utility own := by
  rw [ambientExtension, ValueGeometry.extension_eq_of_mass_one _ _ _
    (FinDist.prob_mem_stdSimplex own).2]
  exact slice.ambientValue_eq_value hrecall clock fallback fuel utility hzero own

/-- Concavity extends to a full neighborhood of every boundary belief. -/
theorem ambientExtension_concave (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (base : FinDist T) :
    ConcaveOn ℝ Set.univ (slice.ambientExtension hrecall clock fallback fuel utility base) := by
  let : Nonempty (Profile M.behavioralSignature) :=
    ⟨fun player => (fallback player).toBehavioral⟩
  exact ValueGeometry.extension_concave _ _
    (slice.branches_bounded_below fallback fuel (fun history => utility history who))

/-- Every minimizing opponent supplies a global supergradient of the
corrected extension. The minimizer set is characterized by canonical Nash. -/
theorem ambientExtension_support (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (base : FinDist T) (opponents : Profile M.behavioralSignature)
    (optimal : slice.branch fallback fuel (fun history => utility history who) base opponents =
      slice.value hrecall clock fallback fuel utility base) (point : T → ℝ) :
    slice.ambientExtension hrecall clock fallback fuel utility base point ≤
      slice.ambientExtension hrecall clock fallback fuel utility base base.prob +
        ∑ type, slice.centeredInfoVector hrecall clock fallback fuel utility base opponents type *
          (point type - base.prob type) := by
  have atBase := slice.ambientValue_eq_value hrecall clock fallback fuel utility hzero base
  have active : ValueGeometry.envelope
      (slice.infoValue fallback fuel (fun history => utility history who)) base.prob =
        ValueGeometry.pairing
          (slice.infoValue fallback fuel (fun history => utility history who) opponents) base.prob :=
    atBase.trans ((slice.branch_eq_weightedBranch fallback fuel _ base opponents).symm.trans optimal).symm
  have supporting := ValueGeometry.centered_support _
    (slice.branches_bounded_below fallback fuel (fun history => utility history who))
    base.prob (FinDist.prob_mem_stdSimplex base).2 opponents active point
  rw [show ValueGeometry.envelope
    (slice.infoValue fallback fuel (fun history => utility history who)) base.prob =
      slice.value hrecall clock fallback fuel utility base from atBase] at supporting
  simpa only [ambientExtension, centeredInfoVector, ValueGeometry.pairing, Pi.sub_apply,
    mul_comm] using supporting

/-- Theorem 1 for any actual PBS Nash equilibrium: the extension is concave
on all real coordinates and agrees with the actual value on the full simplex.
Equation (2) uses a supporting vector, including at nondifferentiable points. -/
theorem theorem1_from_nash (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (base : FinDist T) (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture base) fuel)
      (euPreference utility) profile) :
    ∃ extension : (T → ℝ) → ℝ,
      (∀ own : FinDist T, extension own.prob =
        slice.value hrecall clock fallback fuel utility own) ∧
      ConcaveOn ℝ Set.univ extension ∧
      (∀ point, extension point ≤ extension base.prob +
        ∑ type, slice.centeredInfoVector hrecall clock fallback fuel utility base profile type *
          (point type - base.prob type)) ∧
      (∀ type, slice.infoValue fallback fuel (fun history => utility history who) profile type =
        slice.value hrecall clock fallback fuel utility base +
          slice.centeredInfoVector hrecall clock fallback fuel utility base profile type) := by
  refine ⟨slice.ambientExtension hrecall clock fallback fuel utility base,
    slice.ambientExtension_agrees hrecall clock fallback fuel utility hzero base,
    slice.ambientExtension_concave hrecall clock fallback fuel utility base,
    slice.ambientExtension_support hrecall clock fallback fuel utility hzero base profile
      (slice.branch_eq_value_of_nash hrecall clock fallback fuel utility hzero base
        profile equilibrium), ?_⟩
  intro type
  unfold centeredInfoVector
  ring

end GameTheory.ReBeL.TypeBeliefSlice
