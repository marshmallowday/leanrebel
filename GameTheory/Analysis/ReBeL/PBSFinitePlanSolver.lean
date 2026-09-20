/-
# Actual finite-iteration PBS solving with a derived conditional budget

The complete payoff matrix is obtained from finiteBeliefForm, preserving all
joint hidden-state correlations. Regret matching is iterated a computed finite
number of times, then realized as legal behavioral policies. A law-specific
positive mass floor supplies one common budget for every supported type.
This is a normal-form reference variant, not information-set child CFR.
-/

import GameTheory.Analysis.ReBeL.FinitePlanBudget
import GameTheory.Analysis.ReBeL.PBSApproximateOptimality
import GameTheory.Math.Probability.FinDistMassFloor

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Enumerate the existing legal finite plans, without a parallel plan type. -/
local instance pbsFinitePlanFintype (who : Fin 2) : Fintype (FinitePlan M who) :=
  finitePlanFintype M who

/-- The specified legal fallback supplies the solver's zero-regret plans. -/
def pbsFinitePlanFallback (fallback : Profile M.strategicSignature) :
    ∀ who, FinitePlan M who := fun who info => fallback who info.val

/-- Solve the actual canonical PBS finite form and realize its private plans.
There is no noncomputable selection of a Nash equilibrium in this definition. -/
def pbsFiniteBudgetProfile (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (bound error : ℝ) : Profile M.behavioralSignature :=
  finiteBeliefRealization M clock fallback fallback (observations.length - 1)
    (finiteGameBudgetSolution (finiteBeliefForm M fallback belief fuel) utility
      (pbsFinitePlanFallback M fallback) bound error)

/-- All complete behavioral deviations satisfy the derived finite-time bound. -/
theorem pbsFiniteBudgetProfile_isNash (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history who, |utility history who| ≤ bound)
    (error : ℝ) (positive : 0 < error) :
    IsNash (behavioralBeliefForm M belief fuel) (euPreferenceWithin error utility)
      (pbsFiniteBudgetProfile M clock fallback belief fuel utility bound error) :=
  finiteBeliefForm_approxNash_realization M hrecall clock fallback belief fuel utility error _
    (finiteGameBudgetSolution_isNash (finiteBeliefForm M fallback belief fuel) utility zeroSum
      (pbsFinitePlanFallback M fallback) bound nonneg bounded error positive)

/-- One joint-law budget, common to all players' supported type observations.
It is recomputed for every PBS and may become arbitrarily small across PBSs. -/
def pbsConditionalBudgetProfile (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) : Profile M.behavioralSignature :=
  pbsFiniteBudgetProfile M clock fallback belief fuel utility bound
    (belief.law.positiveMassFloor * loss)

/-- A finite, explicitly budgeted solve has the requested conditional loss on
every supported type. No approximate-Nash or probability-budget premise is
supplied. Absent types are intentionally not certified by this theorem. -/
theorem pbsConditionalBudgetProfile_gain (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}
    (slice : TypeBeliefSlice M observations who T) (own : FinDist T) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history player, |utility history player| ≤ bound)
    (loss : ℝ) (positive : 0 < loss) (type : T) (supported : type ∈ own.support)
    (target : M.BehavioralPolicy who) :
    let profile := pbsConditionalBudgetProfile M clock fallback (slice.mixture own)
      fuel utility bound loss
    slice.conditionalPayoff profile fuel (fun h => utility h who) target type -
      slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type ≤ loss := by
  have mass : (slice.mixture own).law.positiveMassFloor ≤ own.prob type := by
    have sampled : type ∈ ((slice.mixture own).law.map
        (fun h => slice.memory.typeAt (M.infoOf who h.trace))).support := by
      rw [slice.mixture_typeLaw]
      exact supported
    have floor := (slice.mixture own).law.positiveMassFloor_le_map
      (fun h => slice.memory.typeAt (M.infoOf who h.trace)) type sampled
    simpa only [slice.mixture_typeLaw] using floor
  exact slice.conditional_gain_le_of_mass_budget hrecall fallback fuel utility own _
    ((slice.mixture own).law.positiveMassFloor * loss) loss
    (pbsFiniteBudgetProfile_isNash M hrecall clock fallback (slice.mixture own) fuel utility
      zeroSum bound nonneg bounded _
      (mul_pos (FinDist.positiveMassFloor_pos _) positive))
    type supported (mul_le_mul_of_nonneg_right mass positive.le) target

end GameTheory.ReBeL
