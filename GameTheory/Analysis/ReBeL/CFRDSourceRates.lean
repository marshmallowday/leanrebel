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

/-- A quantitative continuation-law rate bounds the positive value change.
The premise concerns actual outcome atoms at every history, not Nash scalars. -/
theorem cfrDFreshValueChange_le_outcomeRate (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (opponent : Fin 2)
    (payoff : E.History → ℝ) (cut remaining : Nat) (bound outcomeRate : ℝ)
    (hb : 0 ≤ bound) (bounded : ∀ h, |payoff h| ≤ bound)
    (small : ∀ h, cfrDFreshOutcomeVariation M base next remaining h ≤ outcomeRate)
    (info : M.InfoState opponent) :
    max 0 (cfrDFreshValueChange M base next fallback opponent payoff cut remaining info) ≤
      bound * outcomeRate := by
  have averaged : conditionalOracleValue (unilateralReferenceLaw M base fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
      (cfrDFreshOutcomeVariation M base next remaining) (info, true) ≤ outcomeRate := by
    apply FinDist.expect_le_of_forall
    intro h _
    exact small h
  exact (cfrDFreshValueChange_le_source M base next fallback opponent payoff
    cut remaining bound hb bounded info).trans (mul_le_mul_of_nonneg_left averaged hb)

/-- Supported FIBER-relative source differences yield an explicit charge.
New-only atoms inside OLD-supported queries are allowed. No minimum reach,
pointwise atom absolute continuity, or bound on the opponent density is assumed. -/
theorem cfrDFreshTransportCharge_le_fiberRates
    (plays next : K → Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (opponent : Fin 2) (payoff : E.History → ℝ) (cut remaining : Nat)
    (bound loss outcomeRate referenceRate : ℝ)
    (hb : 0 ≤ bound) (hl : 0 ≤ loss) (ho : 0 ≤ outcomeRate) (hr : 0 ≤ referenceRate)
    (bounded : ∀ h, |payoff h| ≤ bound) (n : K) (tag : M.InfoState opponent × Bool)
    (sampled : tag ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support)
    (outcomeSmall : ∀ h, cfrDFreshOutcomeVariation M (plays n) (next n) remaining h ≤ outcomeRate)
    (fiberSmall : FinDist.fiberAtomVariation
      (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (unilateralReferenceLaw M (next n) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) tag ≤
        referenceRate * ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
          (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).prob tag) :
    cfrDFreshTransportCharge M plays next fallback opponent payoff
        cut remaining bound loss n tag ≤
      loss + bound * outcomeRate + 4 * bound * referenceRate := by
  rcases tag with ⟨info, flag⟩
  cases flag
  · exact add_nonneg (add_nonneg hl (mul_nonneg hb ho))
      (mul_nonneg (mul_nonneg (by norm_num) hb) hr)
  · have drift := cfrDFreshValueChange_le_outcomeRate M (plays n) (next n) fallback
      opponent payoff cut remaining bound outcomeRate hb bounded outcomeSmall info
    have transport := FinDist.conditionalTransportDefect_le_of_fiberRate
      (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (unilateralReferenceLaw M (next n) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) (info, true)
      sampled referenceRate fiberSmall
    have scaled := mul_le_mul_of_nonneg_left transport
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
    unfold cfrDFreshTransportCharge
    dsimp only
    rw [if_pos rfl]
    nlinarith only [drift, scaled]

/-- Uniform source rates bound the ACTUAL joint private seed/history charge.
Perfect recall supplies the reference support of every actual query. The rates
are independent of the unknown opponent, whose density is not dropped from an
OLD-weighted mean. This does not infer either source premise from child Nash. -/
theorem cfrDWeightedTransportLoss_le_fiberRates (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (payoff : E.History → ℝ)
    (cut remaining : Nat) (bound loss outcomeRate referenceRate : ℝ)
    (hb : 0 ≤ bound) (hl : 0 ≤ loss) (ho : 0 ≤ outcomeRate) (hr : 0 ≤ referenceRate)
    (bounded : ∀ h, |payoff h| ≤ bound)
    (outcomeSmall : ∀ n h,
      cfrDFreshOutcomeVariation M (plays n) (next n) remaining h ≤ outcomeRate)
    (fiberSmall : ∀ n tag, tag ∈
      ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      FinDist.fiberAtomVariation (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (unilateralReferenceLaw M (next n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) tag ≤
      referenceRate * ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).prob tag) :
    cfrDWeightedEnvelopeLoss M seed plays unknown who opponent cut remaining
        (cfrDFreshTransportCharge M plays next fallback opponent payoff cut remaining bound loss) ≤
      loss + bound * outcomeRate + 4 * bound * referenceRate := by
  unfold cfrDWeightedEnvelopeLoss privateCarriedPrefix
  rw [FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro n _
  rw [FinDist.expect_map]
  apply FinDist.expect_le_of_forall
  intro h reached
  have sampled : (M.infoOf opponent h.trace, cfrDCutLive remaining h) ∈
      ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun history =>
          (M.infoOf opponent history.trace, cfrDCutLive remaining history))).support := by
    rw [privateOpponent_profile M (plays n) unknown who opponent different] at reached
    rw [FinDist.support_map]
    exact ⟨h, informationReweight_support
        (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (M.runBehavioral (Profile.update (plays n) opponent (unknown opponent)) cut)
        (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
        (fun tag => unilateralDensity M (plays n) fallback opponent (unknown opponent) tag.1)
        (unilateralReference_density M hrecall (plays n) fallback opponent (unknown opponent) cut)
        reached, rfl⟩
  exact cfrDFreshTransportCharge_le_fiberRates M plays next fallback opponent payoff
    cut remaining bound loss outcomeRate referenceRate hb hl ho hr bounded n
    (M.infoOf opponent h.trace, cfrDCutLive remaining h) sampled (outcomeSmall n)
    (fiberSmall n _ sampled)

/-- A common information-local value target controls the one-sided change.
Each continuation is calibrated under its OWN reference law. Equality of those
source laws is explicit; neither equality of outcome laws nor closeness of Nash
scalars is used. The execution theorem below requires calibration only on
OLD-supported live queries. -/
theorem cfrDFreshValueChange_le_calibration
    (base next : Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (opponent : Fin 2) (payoff : E.History → ℝ) (cut remaining : Nat)
    (info : M.InfoState opponent) (target oldError newError : ℝ)
    (sameReference : unilateralReferenceLaw M next fallback opponent cut =
      unilateralReferenceLaw M base fallback opponent cut)
    (oldCalibration : |conditionalOracleValue
      (unilateralReferenceLaw M base fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
      (fun h => (M.runBehavioralFrom base remaining h).expect payoff) (info, true) -
      target| ≤ oldError)
    (newCalibration : |conditionalOracleValue
      (unilateralReferenceLaw M next fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
      (fun h => (M.runBehavioralFrom next remaining h).expect payoff) (info, true) -
      target| ≤ newError) :
    max 0 (cfrDFreshValueChange M base next fallback opponent payoff cut remaining info) ≤
      oldError + newError := by
  have oldNonneg : 0 ≤ oldError := (abs_nonneg _).trans oldCalibration
  have newNonneg : 0 ≤ newError := (abs_nonneg _).trans newCalibration
  unfold cfrDFreshValueChange conditionalOracleValue
  rw [FinDist.expect_sub]
  unfold conditionalOracleValue at oldCalibration newCalibration
  rw [sameReference] at newCalibration
  apply max_le (add_nonneg oldNonneg newNonneg)
  have lower := (abs_le.mp oldCalibration).1
  have upper := (abs_le.mp newCalibration).2
  linarith only [lower, upper]

/-- Supported value calibration, rather than full outcome-law convergence,
bounds the actual joint private seed/history charge. Perfect recall transfers
actual support to the unilateral reference. The unknown opponent remains
arbitrary, and no assumption is made at an absent or stopped query. In a real
fresh chain, sameReference is discharged by its prefix-preservation theorem;
the two calibration inequalities remain separate source obligations. -/
theorem cfrDWeightedTransportLoss_le_calibration (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (payoff : E.History → ℝ)
    (cut remaining : Nat) (bound loss oldError newError : ℝ)
    (hl : 0 ≤ loss) (ho : 0 ≤ oldError) (hn : 0 ≤ newError)
    (target : K → M.InfoState opponent → ℝ)
    (sameReference : ∀ n, unilateralReferenceLaw M (next n) fallback opponent cut =
      unilateralReferenceLaw M (plays n) fallback opponent cut)
    (oldCalibration : ∀ n info, (info, true) ∈
      ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      |conditionalOracleValue (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (fun h => (M.runBehavioralFrom (plays n) remaining h).expect payoff) (info, true) -
        target n info| ≤ oldError)
    (newCalibration : ∀ n info, (info, true) ∈
      ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      |conditionalOracleValue (unilateralReferenceLaw M (next n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (fun h => (M.runBehavioralFrom (next n) remaining h).expect payoff) (info, true) -
        target n info| ≤ newError) :
    cfrDWeightedEnvelopeLoss M seed plays unknown who opponent cut remaining
        (cfrDFreshTransportCharge M plays next fallback opponent payoff cut remaining bound loss) ≤
      loss + oldError + newError := by
  classical
  have query (n : K) (tag : M.InfoState opponent × Bool)
      (sampled : tag ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support) :
      cfrDFreshTransportCharge M plays next fallback opponent payoff
        cut remaining bound loss n tag ≤ loss + oldError + newError := by
    rcases tag with ⟨info, flag⟩
    cases flag
    · exact add_nonneg (add_nonneg hl ho) hn
    · have drift := cfrDFreshValueChange_le_calibration M (plays n) (next n) fallback
        opponent payoff cut remaining info (target n info) oldError newError
        (sameReference n) (oldCalibration n info sampled) (newCalibration n info sampled)
      have transport : FinDist.conditionalTransportDefect
          (unilateralReferenceLaw M (plays n) fallback opponent cut)
          (unilateralReferenceLaw M (next n) fallback opponent cut)
          (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) (info, true) = 0 := by
        rw [sameReference n]
        simp [FinDist.conditionalTransportDefect]
      unfold cfrDFreshTransportCharge
      dsimp only
      rw [if_pos rfl, transport]
      simpa only [mul_zero, add_zero, add_assoc] using add_le_add_left drift loss
  unfold cfrDWeightedEnvelopeLoss privateCarriedPrefix
  rw [FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro n _
  rw [FinDist.expect_map]
  apply FinDist.expect_le_of_forall
  intro h reached
  apply query n
  rw [privateOpponent_profile M (plays n) unknown who opponent different] at reached
  rw [FinDist.support_map]
  exact ⟨h, informationReweight_support
      (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (M.runBehavioral (Profile.update (plays n) opponent (unknown opponent)) cut)
      (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
      (fun tag => unilateralDensity M (plays n) fallback opponent (unknown opponent) tag.1)
      (unilateralReference_density M hrecall (plays n) fallback opponent (unknown opponent) cut)
      reached, rfl⟩

end GameTheory.ReBeL
