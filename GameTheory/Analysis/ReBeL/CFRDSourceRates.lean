/-
# Source-law bounds for actual-prefix weighted fresh re-solving

The old conditional value change is bounded by the difference of actual
continuation outcome laws. Conditional transport is bounded by unnormalized
reference atoms with the exact unknown-opponent density. Neither a positive
minimum query mass nor a desired security inequality is a hypothesis.
-/

import GameTheory.Math.Probability.FinDistTransportRate
import GameTheory.Analysis.ReBeL.CFRDWeightedTransport

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History]
variable {K : Type*}

/-- L1 variation of the actual continuation outcome laws, not of Nash scalars. -/
def cfrDFreshOutcomeVariation (base next : Profile M.behavioralSignature)
    (remaining : Nat) (history : E.History) : ℝ :=
  FinDist.atomVariation (M.runBehavioralFrom next remaining history)
    (M.runBehavioralFrom base remaining history)

/-- Actual outcome variation is nonnegative. -/
theorem cfrDFreshOutcomeVariation_nonneg (base next : Profile M.behavioralSignature)
    (remaining : Nat) (history : E.History) :
    0 ≤ cfrDFreshOutcomeVariation M base next remaining history :=
  FinDist.atomVariation_nonneg _ _

/-- Reusing the actual continuation has zero source variation. -/
theorem cfrDFreshOutcomeVariation_self (base : Profile M.behavioralSignature)
    (remaining : Nat) (history : E.History) :
    cfrDFreshOutcomeVariation M base base remaining history = 0 :=
  FinDist.atomVariation_self _

variable [∀ who info, Fintype (M.Choice who info)]

/-- Source outcome variation bounds the positive OLD-query value change.
This holds for the total conditional too, but only supported queries are used
by the execution consumer below. No scalar Nash-to-vector implication is assumed. -/
theorem cfrDFreshValueChange_le_source (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (opponent : Fin 2)
    (payoff : E.History → ℝ) (cut remaining : Nat) (bound : ℝ)
    (hb : 0 ≤ bound) (bounded : ∀ h, |payoff h| ≤ bound) (info : M.InfoState opponent) :
    max 0 (cfrDFreshValueChange M base next fallback opponent payoff cut remaining info) ≤
      bound * conditionalOracleValue (unilateralReferenceLaw M base fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (cfrDFreshOutcomeVariation M base next remaining) (info, true) := by
  let law := (unilateralReferenceLaw M base fallback opponent cut).condOnFibre
    (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) (info, true)
  have positive : 0 ≤ law.expect (cfrDFreshOutcomeVariation M base next remaining) := by
    have lower := FinDist.expect_mono (μ := law) (u := fun _ => (0 : ℝ))
      (fun h _ => cfrDFreshOutcomeVariation_nonneg M base next remaining h)
    simpa only [FinDist.expect_const] using lower
  apply max_le (mul_nonneg hb positive)
  have averaged := FinDist.expect_mono (μ := law) (fun h _ =>
    (le_abs_self ((M.runBehavioralFrom next remaining h).expect payoff -
      (M.runBehavioralFrom base remaining h).expect payoff)).trans
        (FinDist.abs_expect_sub_le_atomVariation (M.runBehavioralFrom next remaining h)
          (M.runBehavioralFrom base remaining h) payoff bound bounded))
  unfold cfrDFreshValueChange conditionalOracleValue cfrDFreshOutcomeVariation
  simpa only [FinDist.expect_smul, law] using averaged

/-- Computed source cost for one private parent iteration. The reference-atom
term retains both the actual opponent density and the live gate. New-only atoms
are included in the finite sum; absent NEW queries are never given fake posteriors. -/
def cfrDFreshSourceCost (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (cut remaining : Nat) (bound loss : ℝ) : ℝ :=
  (M.runBehavioral (Profile.update unknown who (base who)) cut).expect
    (fun h => if cfrDCutLive remaining h then
      loss + bound * cfrDFreshOutcomeVariation M base next remaining h else 0) +
    4 * bound * ∑ h,
      (unilateralDensity M base fallback opponent (unknown opponent)
        (M.infoOf opponent h.trace) * (if cfrDCutLive remaining h then 1 else 0)) *
      |(unilateralReferenceLaw M base fallback opponent cut).prob h -
        (unilateralReferenceLaw M next fallback opponent cut).prob h|

/-- Integrate source discrepancies over the SAME private parent seed. Each
summand already uses that seed's actual opposing prefix, not independent marginals. -/
def cfrDSourceEnvelopeLoss (seed : FinDist K)
    (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (cut remaining : Nat) (bound loss : ℝ) : ℝ :=
  seed.expect fun n => cfrDFreshSourceCost M (plays n) (next n) fallback unknown
    who opponent cut remaining bound loss

/-- One actual opposing prefix consumes outcome and density-weighted reference
atom discrepancies. Perfect recall establishes the exact density; it is not an
input bound on an arbitrary certificate or on the final security conclusion. -/
theorem cfrDFreshTransportCharge_prefix_le_source (hrecall : M.PerfectRecall)
    (plays next : K → Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (payoff : E.History → ℝ) (cut remaining : Nat)
    (bound loss : ℝ) (hb : 0 ≤ bound) (bounded : ∀ h, |payoff h| ≤ bound) (n : K) :
    (M.runBehavioral (Profile.update unknown who (plays n who)) cut).expect
      (fun h => cfrDFreshTransportCharge M plays next fallback opponent payoff
        cut remaining bound loss n (M.infoOf opponent h.trace, cfrDCutLive remaining h)) ≤
      cfrDFreshSourceCost M (plays n) (next n) fallback unknown
        who opponent cut remaining bound loss := by
  classical
  let old := unilateralReferenceLaw M (plays n) fallback opponent cut
  let fresh := unilateralReferenceLaw M (next n) fallback opponent cut
  let actual := M.runBehavioral (Profile.update unknown who (plays n who)) cut
  let observe := fun h : E.History => (M.infoOf opponent h.trace, cfrDCutLive remaining h)
  let weight := fun tag : M.InfoState opponent × Bool =>
    unilateralDensity M (plays n) fallback opponent (unknown opponent) tag.1
  let gate := fun tag : M.InfoState opponent × Bool => if tag.2 then (1 : ℝ) else 0
  let localCost := fun h : E.History => if cfrDCutLive remaining h then
    loss + bound * cfrDFreshOutcomeVariation M (plays n) (next n) remaining h else 0
  have density : ∀ h, actual.prob h = old.prob h * weight (observe h) := by
    intro h
    dsimp only [actual, old, weight, observe]
    rw [privateOpponent_profile M (plays n) unknown who opponent different]
    exact unilateralReference_density M hrecall (plays n) fallback
      opponent (unknown opponent) cut h
  have weightNonneg (tag : M.InfoState opponent × Bool) : 0 ≤ weight tag := by
    dsimp only [weight, unilateralDensity]
    exact div_nonneg (informationOwnReach_unitInterval M _ _ _).1
      (informationOwnReach_unitInterval M _ _ _).1
  have gateNonneg (tag : M.InfoState opponent × Bool) : 0 ≤ gate tag := by
    dsimp only [gate]
    split_ifs <;> norm_num
  have query (tag : M.InfoState opponent × Bool)
      (sampled : tag ∈ (old.map observe).support) :
      cfrDFreshTransportCharge M plays next fallback opponent payoff
          cut remaining bound loss n tag ≤
        conditionalOracleValue old observe localCost tag +
          2 * bound * (gate tag * FinDist.conditionalTransportDefect old fresh observe tag) := by
    have localValue := conditionalOracle_live_value old
      (fun h => M.infoOf opponent h.trace) (cfrDCutLive remaining)
      (fun h => loss + bound * cfrDFreshOutcomeVariation M (plays n) (next n) remaining h)
      tag sampled
    have localEq : conditionalOracleValue old observe localCost tag =
        if tag.2 then loss + bound * conditionalOracleValue old observe
          (cfrDFreshOutcomeVariation M (plays n) (next n) remaining) tag else 0 := by
      simpa only [conditionalOracleValue, FinDist.expect_add, FinDist.expect_const,
        FinDist.expect_smul, observe, localCost] using localValue
    rw [localEq]
    rcases tag with ⟨info, flag⟩
    cases flag
    · simp [cfrDFreshTransportCharge, gate]
    · have drift := cfrDFreshValueChange_le_source M (plays n) (next n) fallback opponent
        payoff cut remaining bound hb bounded info
      simpa [cfrDFreshTransportCharge, gate, old, fresh, observe] using
        add_le_add_right (add_le_add_left drift loss)
          (2 * bound * FinDist.conditionalTransportDefect old fresh observe (info, true))
  have integrated : actual.expect (fun h => cfrDFreshTransportCharge M plays next fallback
      opponent payoff cut remaining bound loss n (observe h)) ≤
      actual.expect localCost + 2 * bound * actual.expect (fun h =>
        gate (observe h) * FinDist.conditionalTransportDefect old fresh observe (observe h)) := by
    calc
      _ ≤ actual.expect (fun h => conditionalOracleValue old observe localCost (observe h) +
          2 * bound * (gate (observe h) *
            FinDist.conditionalTransportDefect old fresh observe (observe h))) := by
        apply FinDist.expect_mono
        intro h reached
        apply query
        rw [FinDist.support_map]
        exact ⟨h, informationReweight_support old actual observe weight density reached, rfl⟩
      _ = _ := by
        rw [FinDist.expect_add, FinDist.expect_smul]
        have localEq := conditionalOracle_reweight_exact old actual observe weight density localCost
        rw [FinDist.expect_map] at localEq
        rw [localEq]
  have transported := FinDist.expect_transport_le_of_density old fresh actual observe
    weight gate weightNonneg gateNonneg density
  have scaled := mul_le_mul_of_nonneg_left transported
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
  dsimp only [actual, observe, weight, gate, localCost, old, fresh] at integrated scaled
  unfold cfrDFreshSourceCost
  nlinarith only [integrated, scaled]

/-- The original actual seed/history weighted charge is bounded by computed
source-law errors. This is not the invalid inference that child Nash quality alone
forces a small counterfactual drift or a small change of conditional law. -/
theorem cfrDWeightedTransportLoss_le_source (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (payoff : E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (hb : 0 ≤ bound)
    (bounded : ∀ h, |payoff h| ≤ bound) :
    cfrDWeightedEnvelopeLoss M seed plays unknown who opponent cut remaining
        (cfrDFreshTransportCharge M plays next fallback opponent payoff cut remaining bound loss) ≤
      cfrDSourceEnvelopeLoss M seed plays next fallback unknown
        who opponent cut remaining bound loss := by
  unfold cfrDWeightedEnvelopeLoss cfrDSourceEnvelopeLoss privateCarriedPrefix
  rw [FinDist.expect_bind]
  apply FinDist.expect_mono
  intro n _
  rw [FinDist.expect_map]
  exact cfrDFreshTransportCharge_prefix_le_source M hrecall plays next fallback unknown
    who opponent different payoff cut remaining bound loss hb bounded n

end GameTheory.ReBeL
