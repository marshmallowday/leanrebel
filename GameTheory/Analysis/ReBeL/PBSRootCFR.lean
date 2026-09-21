/-
# Constructed information-set CFR in the joint-PBS rooted game

This is the existing information-set regret-matching recurrence, not learning
in a complete-plan normal form and not a supplied Nash certificate. It uses a
positive fixed iteration count, own-reach averaging and the canonical runner.
Its native rooted-game guarantee is kept separate from a policy correspondence
back to the original continuation game and recursive test-time safety.
-/

import GameTheory.Analysis.ReBeL.PBSRootInformation
import GameTheory.Analysis.ReBeL.CFRNash

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Each root snapshot contains the player's full original AOH. The outer
full-information adapter also retains the complete subsequent local sequence. -/
@[reducible]
def pbsRootFullInformation (roots : FinDist E.History) :
    InformationModel (pbsRootProtocol roots) :=
  fullInformation (pbsRootInformation (fullInformation M) roots)

/-- A total legal initial policy is constructed from an original fallback. -/
def pbsRootFallback (roots : FinDist E.History) (fallback : (who : Fin 2) → M.Policy who)
    (who : Fin 2) : (pbsRootFullInformation M roots).Policy who :=
  liftPolicy (pbsRootInformation (fullInformation M) roots) who
    (pbsRootPolicy (fullInformation M) roots who (liftPolicy M who (fallback who)))

/-- Rooted terminal and partial histories use the actual original payoff.
Zero fuel at the administrative root has value zero, not an invented history. -/
def pbsRootPayoff (roots : FinDist E.History) (payoff : Fin 2 → E.History → ℝ)
    (who : Fin 2) (history : (pbsRootProtocol roots).History) : ℝ :=
  match history.state with
  | none => 0
  | some original => payoff who original

/-- The chance-root adapter preserves the original zero-sum identity. -/
theorem pbsRootPayoff_zeroSum (roots : FinDist E.History) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history)) :
    IsZeroSum (fun history who => pbsRootPayoff roots payoff who history) := by
  intro history
  cases hstate : history.state with
  | none => simp [pbsRootPayoff, hstate]
  | some original => simpa only [pbsRootPayoff, hstate] using hzero original

/-- Uniform payoff bounds include the administrative, terminal and off-path cases. -/
theorem pbsRootPayoff_abs_le (roots : FinDist E.History) (payoff : Fin 2 → E.History → ℝ)
    (who : Fin 2) (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hbound : ∀ original, |payoff who original| ≤ bound)
    (history : (pbsRootProtocol roots).History) :
    |pbsRootPayoff roots payoff who history| ≤ bound := by
  cases hstate : history.state with
  | none => simpa only [pbsRootPayoff, hstate, abs_zero] using hbound0
  | some original => simpa only [pbsRootPayoff, hstate] using hbound original

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (roots : FinDist E.History)

/-- Enumerate rooted histories using the proved strict rank. -/
local instance pbsCFRHistoryFintype : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

/-- Classical equality is used only by the abstract real-valued CFR reference. -/
local instance pbsCFRInfoDecidableEq (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

/-- Each local menu is a subtype of the original finite action options. -/
local instance pbsCFRChoiceFintype (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- The actual fixed-T information-set CFR output. One fuel unit belongs to
joint-root sampling; `fuel` counts original continuation transitions. -/
def pbsRootCFR (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ) (fuel t : ℕ) [NeZero t] :
    Profile (pbsRootFullInformation M roots).behavioralSignature :=
  cfrAveragedProfile (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (fuel + 1) t

/-- The explicit two-player finite-T information-set regret bound. -/
def pbsRootCFRBound (bound : Fin 2 → ℝ) (fuel t : ℕ) : ℝ :=
  cfrCumulativeBound (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (fuel + 1) 0 (bound 0) t / t +
  cfrCumulativeBound (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (fuel + 1) 1 (bound 1) t / t

/-- Every native rooted-game behavioral deviation is bounded for the actual
constructed recurrence. No equilibrium, regret or recall certificate is supplied. -/
theorem pbsRootCFR_isNash (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (fuel t : ℕ) [NeZero t] :
    IsNash ((pbsRootFullInformation M roots).toBehavioralGameForm (fuel + 1))
      (euPreferenceWithin (pbsRootCFRBound M roots bound fuel t)
        (fun history who => pbsRootPayoff roots payoff who history))
      (pbsRootCFR M roots fallback payoff fuel t) :=
  cfrAveragedProfile_isNash (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (fullSignals_perfectRecall (pbsRootInformation (fullInformation M) roots).toInfoSignals)
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff)
    (pbsRootPayoff_zeroSum roots payoff hzero) bound hbound0
    (fun who => pbsRootPayoff_abs_le roots payoff who (bound who) (hbound0 who) (hbound who))
    (fuel + 1) t

end GameTheory.ReBeL
