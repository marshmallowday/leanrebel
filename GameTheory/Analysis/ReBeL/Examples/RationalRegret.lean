/-
# The executed local regret is the actual canonical CFR update

Concrete history, information, chance, payoff and reach lemmas supply every
premise. Pure local commitments are preserved as complete behavioral policies.
There is no regret oracle, assumed root decomposition or assumed solver trace.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalCounterfactual
import GameTheory.Analysis.ReBeL.Examples.RationalProjection
import GameTheory.Analysis.ReBeL.RationalMatching

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- Enumerate every canonical legal history independently of current policy support. -/
local instance regretHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Proof-level equality supports canonical full-observation policy commitments. -/
local instance regretInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Exact agreement of the numeric instantaneous regret with the original
full-game local counterfactual regret, for every profile and every legal action. -/
theorem instantaneousRegret_correct (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) (who : Player) (key : ActiveKey)
    (horizon : ℕ) (a : Choice key.1) :
    (table.instantaneousRegret numeric who key.1 horizon a : ℝ) =
      (model fullPrior).counterfactualActionRegret semantic who (canonicalSite who key)
        (cfrPayoff who) (horizon - decisionClock.depth who (canonicalSite who key).1)
        (keyChoiceEquiv who key a) := by
  have hbase : RowRealizes numeric (Profile.update semantic who (semantic who)) := by
    rw [Profile.update_eq_self]
    exact hreal
  unfold HistoryTable.instantaneousRegret
  rw [Rat.cast_sub,
    counterfactualValue_correct numeric _ semantic who key
      ((semantic who).commit (decodeInfo key.1) (keyChoiceEquiv who key a))
      hreal (concrete_commit_realizes numeric semantic hreal who key a) horizon,
    counterfactualValue_correct numeric numeric semantic who key (semantic who)
      hreal hbase horizon]
  rfl

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
