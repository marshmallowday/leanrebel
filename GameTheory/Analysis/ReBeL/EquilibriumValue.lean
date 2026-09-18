/-
# Exact equilibrium values in the canonical game

This closes the Section 3 value-uniqueness obligation for two given exact
zero-sum equilibria. It applies directly to behavioral strategies, without
adding a second randomization layer or assuming equilibrium existence.
PBS value construction and minimax existence remain separate M05 obligations.
-/

import GameTheory.ReBeL.Payoff
import GameTheory.Core.ZeroSum

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Math.Probability

/-- Two exact equilibria have the same value in any canonical two-player
zero-sum game form. The strategies themselves need not be equal. -/
theorem nash_value_eq (form : GameForm (Fin 2))
    (utility : form.sig.Outcome → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (first second : Profile form.sig)
    (hfirst : IsNash form (euPreference utility) first)
    (hsecond : IsNash form (euPreference utility) second) :
    expectedUtility utility 0 (form.play first) =
      expectedUtility utility 0 (form.play second) := by
  have cross (left right : Profile form.sig) :
      Profile.update left 1 (right 1) = Profile.update right 0 (left 0) := by
    funext who
    rcases (by decide : ∀ who : Fin 2, who = 0 ∨ who = 1) who with rfl | rfl
    · rw [Profile.update_of_ne _ _ (by decide), Profile.update_same]
    · rw [Profile.update_same, Profile.update_of_ne _ _ (by decide)]
  have ordered (left right : Profile form.sig)
      (hleft : IsNash form (euPreference utility) left)
      (hright : IsNash form (euPreference utility) right) :
      expectedUtility utility 0 (form.play left) ≤
        expectedUtility utility 0 (form.play right) := by
    have column : expectedUtility utility 1
        (form.play (Profile.update left 1 (right 1))) ≤
          expectedUtility utility 1 (form.play left) :=
      (isNash_iff.mp hleft) 1 (right 1)
    have row : expectedUtility utility 0
        (form.play (Profile.update right 0 (left 0))) ≤
          expectedUtility utility 0 (form.play right) :=
      (isNash_iff.mp hright) 0 (left 0)
    rw [hzero.expectedUtility_one, hzero.expectedUtility_one, cross] at column
    linarith
  exact le_antisymm (ordered first second hfirst hsecond)
    (ordered second first hsecond hfirst)

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- The value uniqueness statement for the original behavioral game. Its
Nash hypotheses quantify over every complete information-local policy. No
finite Plan restriction, shared seed or assumed existence is introduced. -/
theorem behavioralNash_value_eq (horizon : ℕ) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (first second : Profile M.behavioralSignature)
    (hfirst : IsNash (M.toBehavioralGameForm horizon)
      (euPreference (fun history who => payoff who history)) first)
    (hsecond : IsNash (M.toBehavioralGameForm horizon)
      (euPreference (fun history who => payoff who history)) second) :
    (M.runBehavioral first horizon).expect (payoff 0) =
      (M.runBehavioral second horizon).expect (payoff 0) :=
  nash_value_eq (M.toBehavioralGameForm horizon) (fun history who => payoff who history)
    hzero first second hfirst hsecond

end GameTheory.ReBeL
