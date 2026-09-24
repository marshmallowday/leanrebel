/-
# Actual fresh-chain consumer of the uniform source-law rate

The biased finite-time parent and two computed children are unchanged. Exact
reference preservation discharges the atom-radius premise; the outcome radius
is kept explicit, with a separate unconditional but nondecaying control.
-/

import GameTheory.Analysis.ReBeL.CFRDUniformSourceRates
import GameTheory.Analysis.ReBeL.Examples.CFRDSourceRates

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- The bound uses all legal histories, not merely current support. -/
local instance uniformSourceHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Include inactive local menus in the original strategy domain. -/
local instance uniformSourceChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Decidable equality is confined to the real-valued parent proof model. -/
local instance uniformSourceInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The fresh chain preserves the reference atoms exactly, so the uniform
source estimate has no density or reference-variation term. The only remaining
radius is an explicit hypothesis about continuation outcome laws. -/
theorem freshChainControl_source_uniform_rate
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t]
    (rate : ℝ) (hr : 0 ≤ rate)
    (outcomes : ∀ n : Fin t, ∀ h,
      cfrDFreshOutcomeVariation (model fullPrior) (freshControlParentPlays t n)
        (cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2) 1 h ≤ rate) :
    cfrDSourceEnvelopeLoss (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (fun n => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
        informationControlFullFallback unknown 0 1 2 1 2 (freshChainControlLoss 1) ≤
      1 / 8 + 2 * rate := by
  have source := cfrDSourceEnvelopeLoss_le_uniform_rate (model fullPrior)
    (cfrIterationLaw t) (freshControlParentPlays t)
    (fun n => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
    informationControlFullFallback unknown 0 1 2 1 2 (freshChainControlLoss 1) rate 0
    (by norm_num) (freshChainControlLoss_pos 1).le hr (fun n _ => outcomes n)
    (by
      intro n _
      have same := cfrDFreshInformationChain_referenceLaw (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 2 1 2 freshChainControlLoss
        (freshControlParentPlays t n) 1 2
      rw [same, FinDist.atomVariation_self])
  simpa [freshChainControlLoss] using source

/-- An unconditional control instantiates a genuine two-solve chain and an
arbitrary unknown opponent. The radius two is valid but deliberately does not
pretend to be a vanishing rate obtained from child Nash accuracy. -/
theorem freshChainControl_source_uniform_control
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t] :
    cfrDSourceEnvelopeLoss (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (fun n => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
        informationControlFullFallback unknown 0 1 2 1 2 (freshChainControlLoss 1) ≤
      33 / 8 := by
  have control := freshChainControl_source_uniform_rate unknown t 2 (by norm_num)
    (fun _ _ => FinDist.atomVariation_le_two _ _)
  norm_num at control ⊢
  exact control

end GameTheory.ReBeL.Examples.HiddenTypes
