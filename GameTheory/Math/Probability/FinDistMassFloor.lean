/-
# A derived positive floor for one finite-support law

The floor is recomputed from this particular law. It is not a uniform lower
bound on all laws or all learned beliefs. It controls supported pushforward
atoms without placing any finite-carrier assumption on either observation type.
-/

import GameTheory.Math.Probability.FinDist
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β : Type*}

/-- The least strictly positive atom of this finite-support probability law. -/
def positiveMassFloor (law : FinDist α) : ℝ :=
  law.supportFinset.inf' (by
    obtain ⟨item, member⟩ := law.support_nonempty
    exact ⟨item, mem_supportFinset.mpr member⟩) law.prob

/-- Positivity is derived from nonempty finite probability support. -/
theorem positiveMassFloor_pos (law : FinDist α) : 0 < law.positiveMassFloor := by
  unfold positiveMassFloor
  rw [Finset.lt_inf'_iff]
  intro item member
  exact prob_pos_iff.mpr (mem_supportFinset.mp member)

/-- Only atoms actually in support are bounded below by this floor. -/
theorem positiveMassFloor_le (law : FinDist α) (item : α) (member : item ∈ law.support) :
    law.positiveMassFloor ≤ law.prob item :=
  Finset.inf'_le _ (mem_supportFinset.mpr member)

/-- A supported observed atom contains a supported source atom. Thus one
joint-law floor suffices for every player's possibly different type map. -/
theorem positiveMassFloor_le_map (law : FinDist α) (observe : α → β) (tag : β)
    (sampled : tag ∈ (law.map observe).support) :
    law.positiveMassFloor ≤ (law.map observe).prob tag := by
  classical
  rw [support_map] at sampled
  obtain ⟨witness, member, sameTag⟩ := sampled
  have atom : law.prob witness ≤ (law.map observe).prob tag := by
    rw [prob_map]
    calc
      law.prob witness = law.expect (fun item => if witness = item then 1 else 0) := by
        rw [expect_ite_eq, mul_one]
      _ ≤ _ := by
        apply expect_mono
        intro item _
        by_cases same : witness = item
        · subst item
          simp [sameTag]
        · rw [if_neg same]
          by_cases tagged : tag = observe item <;> simp [tagged]
  exact (law.positiveMassFloor_le witness member).trans atom

end GameTheory.Math.Probability.FinDist
