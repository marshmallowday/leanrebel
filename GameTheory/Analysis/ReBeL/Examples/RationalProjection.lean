/-
# Stable action projections for the concrete runtime correspondence

Both local menu representations are embedded in the existing optional Boolean
carrier. This is only a finite sum of action weights and a canonical FinDist
pushforward, not another probability law or game semantics. It lets local policy
replacement be compared without transporting a value between dependent menus.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalPrimitives
import GameTheory.Analysis.ReBeL.Examples.RationalSites

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- Each raw menu injects into the original optional action carrier. -/
theorem choiceOption_injective (site : Site) : Function.Injective (choiceOption site) := by
  cases site with
  | idle => intro a b _; exact Subsingleton.elim a b
  | first ownType => exact Option.some.inj
  | second ownType ownAction result => exact Option.some.inj

/-- The weight of one optional action, read from a finite local numeric menu. -/
def optionWeight (site : Site) (law : Choice site → ℚ) (action : Option Bool) : ℚ :=
  ∑ a, if action = choiceOption site a then law a else 0

/-- The injective projection retains every original local weight. -/
theorem optionWeight_at (site : Site) (law : Choice site → ℚ) (a : Choice site) :
    optionWeight site law (choiceOption site a) = law a := by
  simp [optionWeight, (choiceOption_injective site).eq_iff]

/-- Projected numeric and canonical optional-action probabilities agree at
all actual observations, including the initial and terminal singleton menus. -/
def OptionRealizes (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature) : Prop :=
  ∀ who row action, (optionWeight (information who row)
      (numeric who (information who row)) action : ℝ) =
    ((semantic who ((model fullPrior).infoOf who (decode row).trace)).map
      Subtype.val).prob action

/-- Canonical local menus are finite independently of any policy support. -/
local instance projectedChoiceFintype (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Exact representation is preserved by forgetting only the legal-choice wrapper. -/
theorem optionRealizes_of_row (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) : OptionRealizes numeric semantic := by
  classical
  intro who row action
  rw [FinDist.prob_map, FinDist.expect_eq_sum, ← (rowChoiceEquiv who row).sum_comp]
  unfold optionWeight
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  rw [rowChoiceEquiv_val]
  by_cases h : action = choiceOption (information who row) a
  · simp only [if_pos h, mul_one]
    exact hreal who row a
  · simp [h]

/-- No information is lost in the optional-action comparison, since the legal
menu embeddings are injective. This recovers full dependent-menu representation. -/
theorem rowRealizes_of_option (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : OptionRealizes numeric semantic) : RowRealizes numeric semantic := by
  classical
  intro who row a
  have h := hreal who row (choiceOption (information who row) a)
  rw [optionWeight_at, ← rowChoiceEquiv_val who row a,
    FinDist.prob_map_of_injective Subtype.val Subtype.val_injective] at h
  exact h

/-- Projecting a pure local law keeps exactly its selected action. -/
theorem optionWeight_pure (site : Site) (a : Choice site) (action : Option Bool) :
    optionWeight site (pointMass a) action =
      if action = choiceOption site a then 1 else 0 := by
  unfold optionWeight
  rw [Finset.sum_eq_single a]
  · simp [pointMass]
  · intro b _ hne
    simp [pointMass, hne]
  · simp

/-- The action selected through an active-key equivalence is unchanged. -/
theorem keyChoiceEquiv_val (who : Player) (key : ActiveKey) (a : Choice key.1) :
    (keyChoiceEquiv who key a).1 = choiceOption key.1 a := by
  rcases key with ⟨site, hactive⟩
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType => rfl
  | second ownType ownAction result => rfl

/-- Numeric local commitment, viewed in the stable optional-action carrier.
All other players and information coordinates are left unchanged. -/
theorem optionWeight_commit (numeric : NumericProfile)
    (who player : Player) (site observed : Site) (a : Choice site) (action : Option Bool) :
    optionWeight observed
      (HistoryTable.commit (H := Row) numeric who site (pointMass a) player observed) action =
      if player = who ∧ observed = site then
        (if action = choiceOption site a then 1 else 0)
      else optionWeight observed (numeric player observed) action := by
  classical
  unfold HistoryTable.commit
  by_cases hp : player = who
  · subst player
    rw [Profile.update_same]
    by_cases hi : observed = site
    · subst observed
      rw [Profile.update_same, if_pos ⟨rfl, rfl⟩, optionWeight_pure]
    · rw [Profile.update_of_ne _ _ hi, if_neg (fun h => hi h.2)]
  · rw [Profile.update_of_ne _ _ hp, if_neg (fun h => hp h.1)]

/-- Equality on the infinite full-AOH carrier is used only in proof-level
canonical policy replacement; the executable table retains its finite equality. -/
local instance projectedInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- A raw local pure commitment implements exactly the original canonical
behavioral commitment, not a smaller deviation restricted to a Plan family. -/
theorem concrete_commit_realizes (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) (who : Player) (key : ActiveKey)
    (a : Choice key.1) :
    RowRealizes (HistoryTable.commit (H := Row) numeric who key.1 (pointMass a))
      (Profile.update semantic who ((semantic who).commit (decodeInfo key.1)
        (keyChoiceEquiv who key a))) := by
  apply rowRealizes_of_option
  have hprojected := optionRealizes_of_row numeric semantic hreal
  intro player row action
  rw [optionWeight_commit]
  by_cases hp : player = who
  · subst player
    rw [Profile.update_same]
    by_cases hi : information who row = key.1
    · have hcanonical := (information_matches who row key).mpr hi
      rw [if_pos ⟨rfl, hi⟩, hcanonical, BehavioralPolicy.commit_self,
        FinDist.map_pure, FinDist.prob_pure_eq_ite, keyChoiceEquiv_val]
      split <;> simp_all
    · have hcanonical : (model fullPrior).infoOf who (decode row).trace ≠ decodeInfo key.1 :=
        fun h => hi ((information_matches who row key).mp h)
      rw [if_neg (fun h => hi h.2), BehavioralPolicy.commit_of_ne _ _ _ hcanonical]
      exact hprojected who row action
  · rw [if_neg (fun h => hp h.1), Profile.update_of_ne _ _ hp]
    exact hprojected player row action

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
