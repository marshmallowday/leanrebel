/-
# Information-fiber value oracles

An oracle vector describes conditional continuation values, not hidden-state
values. Disintegration proves the backup identity and its error bound. The
joint law, its support and the observation map remain explicit. In particular,
a zero-mass observation is never silently certified as a queried posterior.
-/

import GameTheory.ReBeL.Frontier

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

section Disintegration

variable {Leaf Info : Type*}

/-- Exact value of an observation under a specified joint leaf law. Values on
zero-mass fibers use the existing total conditional, but the oracle contract
below only consults fibers in the actual observation-law support. -/
def conditionalOracleValue (law : FinDist Leaf) (observe : Leaf → Info)
    (value : Leaf → ℝ) (info : Info) : ℝ :=
  (law.condOnFibre observe info).expect value

/-- A sampled conditional contains only leaves with the sampled observation. -/
theorem conditionalOracle_support (law : FinDist Leaf) (observe : Leaf → Info)
    (info : Info) (sampled : info ∈ (law.map observe).support)
    (leaf : Leaf) (reached : leaf ∈ (law.condOnFibre observe info).support) :
    observe leaf = info := by
  classical
  have possible : ∃ leaf ∈ observe ⁻¹' {info}, leaf ∈ law.support := by
    rw [FinDist.support_map] at sampled
    obtain ⟨leaf, positive, same⟩ := sampled
    exact ⟨leaf, same, positive⟩
  unfold FinDist.condOnFibre at reached
  rw [dif_pos possible] at reached
  exact (FinDist.support_condOn law _ possible reached).1

/-- Backing up exact information-state values gives the original expected
continuation payoff. The joint law need not factor into independent marginals. -/
theorem conditionalOracle_expect (law : FinDist Leaf) (observe : Leaf → Info)
    (value : Leaf → ℝ) :
    (law.map observe).expect (conditionalOracleValue law observe value) =
      law.expect value := by
  unfold conditionalOracleValue
  calc
    _ = ((law.map observe).bind (law.condOnFibre observe)).expect value :=
      (FinDist.expect_bind _ _ _).symm
    _ = _ := congrArg (fun distribution : FinDist Leaf => distribution.expect value)
      (FinDist.eq_bind_condOnFibre law observe).symm

/-- Uniform error in an information-state vector controls its actual backup.
Pointwise accuracy at each hidden history is NOT required. -/
theorem conditionalOracle_error (law : FinDist Leaf) (observe : Leaf → Info)
    (value : Leaf → ℝ) (prediction : Info → ℝ) (error : ℝ)
    (accurate : ∀ info ∈ (law.map observe).support,
      |prediction info - conditionalOracleValue law observe value info| ≤ error) :
    |(law.map observe).expect prediction - law.expect value| ≤ error := by
  rw [← conditionalOracle_expect law observe value, ← FinDist.expect_sub]
  exact FinDist.abs_expect_le_of_abs_bound _ _ accurate

/-- A coefficient measurable at the information state can be moved outside
its conditional expectation. This is the cancellation needed for own-reach
weights; it would be invalid for an arbitrary hidden-history coefficient. -/
theorem conditionalOracle_weighted_expect (law : FinDist Leaf)
    (observe : Leaf → Info) (value : Leaf → ℝ) (weight : Info → ℝ) :
    law.expect (fun leaf => weight (observe leaf) * value leaf) =
      (law.map observe).expect
        (fun info => weight info * conditionalOracleValue law observe value info) := by
  rw [← conditionalOracle_expect law observe
    (fun leaf => weight (observe leaf) * value leaf)]
  apply FinDist.expect_congr
  intro info sampled
  unfold conditionalOracleValue
  rw [← FinDist.expect_smul]
  apply FinDist.expect_congr
  intro leaf reached
  rw [conditionalOracle_support law observe info sampled leaf reached]
  rfl

/-- Nonnegative bounded information-local reach coefficients propagate the
vector error, without replacing conditional values by hidden-state values. -/
theorem conditionalOracle_weighted_error (law : FinDist Leaf)
    (observe : Leaf → Info) (value : Leaf → ℝ) (prediction weight : Info → ℝ)
    (error bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (weight_bound : ∀ info ∈ (law.map observe).support,
      0 ≤ weight info ∧ weight info ≤ bound)
    (accurate : ∀ info ∈ (law.map observe).support,
      |prediction info - conditionalOracleValue law observe value info| ≤ error) :
    |(law.map observe).expect (fun info => weight info * prediction info) -
      law.expect (fun leaf => weight (observe leaf) * value leaf)| ≤ bound * error := by
  rw [conditionalOracle_weighted_expect, ← FinDist.expect_sub]
  apply FinDist.abs_expect_le_of_abs_bound
  intro info sampled
  rw [← mul_sub, abs_mul, abs_of_nonneg (weight_bound info sampled).1]
  exact mul_le_mul (weight_bound info sampled).2 (accurate info sampled)
    (abs_nonneg _) bound_nonneg

end Disintegration

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable [Fintype ι] (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- A frontier query keeps remaining fuel, the public trace, and one player's
information state. It does not substitute a product of private marginals. -/
def frontierInformationView (who : ι) (leaf : Nat × E.History) :
    Nat × List M.PublicSignal × M.InfoState who :=
  (leaf.1, publicTrace M.toInfoSignals leaf.2.trace, M.infoOf who leaf.2.trace)

/-- The exact information-state vector is defined by the SAME continuation
profile whose canonical runner supplies the backed-up payoff. -/
def frontierConditionalValues (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (who : ι) (payoff : E.History → ℝ)
    (fuel : Nat) (history : E.History) :
    Nat × List M.PublicSignal × M.InfoState who → ℝ :=
  conditionalOracleValue (frontierRun M frontier profile fuel history)
    (frontierInformationView M who)
    (fun leaf => (M.runBehavioralFrom profile leaf.1 leaf.2).expect payoff)

/-- The information-fiber backup recovers the abstract full-game continuation,
not just a separately stipulated leaf game or an equality of mean vectors. -/
theorem frontierConditionalValues_expect (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (who : ι) (payoff : E.History → ℝ)
    (fuel : Nat) (history : E.History) :
    ((frontierRun M frontier profile fuel history).map
        (frontierInformationView M who)).expect
        (frontierConditionalValues M frontier profile who payoff fuel history) =
      (M.runBehavioralFrom profile fuel history).expect payoff := by
  unfold frontierConditionalValues
  rw [conditionalOracle_expect, ← FinDist.expect_bind,
    frontierRun_bind_continuation]

/-- Approximate conditional values transfer to the full canonical continuation. -/
theorem frontierConditionalValues_error (frontier : PublicFrontier M.toInfoSignals)
    (profile : Profile M.behavioralSignature) (who : ι) (payoff : E.History → ℝ)
    (fuel : Nat) (history : E.History)
    (prediction : Nat × List M.PublicSignal × M.InfoState who → ℝ) (error : ℝ)
    (accurate : ∀ info ∈ ((frontierRun M frontier profile fuel history).map
        (frontierInformationView M who)).support,
      |prediction info - frontierConditionalValues M frontier profile who payoff
        fuel history info| ≤ error) :
    |((frontierRun M frontier profile fuel history).map
        (frontierInformationView M who)).expect prediction -
      (M.runBehavioralFrom profile fuel history).expect payoff| ≤ error := by
  rw [← frontierConditionalValues_expect M frontier profile who payoff fuel history]
  rw [← FinDist.expect_sub]
  exact FinDist.abs_expect_le_of_abs_bound _ _ accurate

/-- Actual iteration-specific joint PBS queries. The complete stopped history
law is conditioned on public observations; a private Bayes law is not used as
its replacement. Each query retains the profile index that generated it. -/
def frontierIterationQueries (frontier : PublicFrontier M.toInfoSignals)
    (plays : Nat → Profile M.behavioralSignature) (iteration fuel : Nat)
    (history : E.History) : FinDist (Σ public, PublicBelief M.toInfoSignals public) :=
  PublicBelief.split ((frontierRun M frontier (plays iteration) fuel history).map Prod.snd)

/-- Drawing a queried PBS and then its history recovers the current iteration's
stopped history law. This is a model-belief identity, not a claim that an
unknown opponent is actually sampling the modeled policy. -/
theorem frontierIterationQueries_bind (frontier : PublicFrontier M.toInfoSignals)
    (plays : Nat → Profile M.behavioralSignature) (iteration fuel : Nat)
    (history : E.History) :
    (frontierIterationQueries M frontier plays iteration fuel history).bind
        (fun belief => belief.2.law) =
      (frontierRun M frontier (plays iteration) fuel history).map Prod.snd := by
  exact PublicBelief.split_bind_law _

end GameTheory.ReBeL
