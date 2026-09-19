/-
# One child table for CFR-D value backup and actual private execution

The oracle adapter constructs its virtual continuation from the very child
policies that its carried public resolver samples. Law equality transfers the
existing finite-time security bound without a replacement-loss hypothesis.
Numerical accuracy and child continuation optimality remain distinct contracts.
-/

import GameTheory.Analysis.ReBeL.CFRDChildResolve

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Child data contains policies and predictions, never a safety certificate. -/
structure CFRDChildResponse (J : Type*) where
  /-- The fresh private child draw, independent of the unknown opponent. -/
  seed : FinDist J
  /-- Complete legal information-local child policies, including off path. -/
  child : J → Profile M.behavioralSignature
  /-- Live-cut information values used in this same parent's numerical backup. -/
  prediction : (who : Fin 2) → M.InfoState who → ℝ

/-- A parent round and current trunk determine one common child response. -/
abbrev CFRDChildOracle (J : Type*) :=
  Nat → Profile M.behavioralSignature → CFRDChildResponse M J

variable {J : Type*} [Fintype J]

/-- The value driver sees the constructed child average, not a separately
selected equilibrium policy. Predictions are read from that same response. -/
def cfrDChildValueOracle (clock : ObservationClock M) (cut : Nat)
    (fallback : (who : Fin 2) → M.Policy who) (family : CFRDChildOracle M J) :
    CFRDValueOracle M := fun n trunk =>
  let response := family n trunk
  { continuation := cfrDChildAverage M clock cut response.seed trunk response.child fallback
    prediction := response.prediction }

variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- The parent trunk is computed by the actual coupled regret recurrence. -/
def cfrDChildTrunk (clock : ObservationClock M) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat)
    (family : CFRDChildOracle M J) (n : Nat) : Profile M.behavioralSignature :=
  cfrProfile M fallback (cfrDState M (cfrDDepthTrunk M clock cut) fallback
    (cfrDDepthOracle M clock fallback payoff cut remaining
      (cfrDChildValueOracle M clock cut fallback family)) n)

/-- Child lookup uses precisely this round's learned trunk. -/
def cfrDChildQuery (clock : ObservationClock M) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat)
    (family : CFRDChildOracle M J) (n : Nat) : CFRDChildResponse M J :=
  family n (cfrDChildTrunk M clock fallback payoff cut remaining family n)

/-- The virtual full profile used by the regret theorem is the same parent
profile whose child table will be sampled by the execution adapter. -/
theorem cfrDChildDepthPlay_eq (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (family : CFRDChildOracle M J) (n : Nat) :
    cfrDDepthPlay M clock fallback payoff cut remaining
        (cfrDChildValueOracle M clock cut fallback family) n =
      cfrDChildParentProfiles M clock cut
        (fun k => (cfrDChildQuery M clock fallback payoff cut remaining family k).seed)
        (cfrDChildTrunk M clock fallback payoff cut remaining family)
        (fun k => (cfrDChildQuery M clock fallback payoff cut remaining family k).child)
        fallback n := rfl

/-- The actual resolver is indexed by the original private parent iteration.
It reads no actual hidden state or opposing policy. The complete child table
may encode information-dependent future choices but is fixed by the query. -/
def cfrDChildDepthResolver (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (family : CFRDChildOracle M J) (t : Nat) :
    CarriedPublicResolver M (Fin t) :=
  cfrDChildPublicResolver M clock cut
    (fun n : Fin t => (cfrDChildQuery M clock fallback payoff cut remaining family n.val).seed)
    (fun n : Fin t => cfrDChildTrunk M clock fallback payoff cut remaining family n.val)
    (fun n : Fin t => (cfrDChildQuery M clock fallback payoff cut remaining family n.val).child)

/-- Actual carried re-solving realizes the same-iteration virtual sequence.
No CFRDResolverLocal premise or supplied final guarantee is used. -/
theorem cfrDChildDepth_resolve_eq (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (family : CFRDChildOracle M J)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (t : Nat) [NeZero t] :
    privateCarriedResolve M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining
          (cfrDChildValueOracle M clock cut fallback family) n.val)
        (cfrDChildDepthResolver M clock fallback payoff cut remaining family t)
        unknown who cut remaining =
      privateIterationLaw M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining
          (cfrDChildValueOracle M clock cut fallback family) n.val)
        unknown who (cut + remaining) := by
  exact cfrDChildResolve_eq M clock hrecall (cfrIterationLaw t)
    (fun n : Fin t => (cfrDChildQuery M clock fallback payoff cut remaining family n.val).seed)
    (fun n : Fin t => cfrDChildTrunk M clock fallback payoff cut remaining family n.val)
    (fun n : Fin t => (cfrDChildQuery M clock fallback payoff cut remaining family n.val).child)
    fallback unknown who cut remaining

/-- Reference predictions can be computed from the constructed child average.
This is an exact mathematical oracle, not a claim of inexpensive execution. -/
def cfrDExactChildFamily (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (seeds : Nat → Profile M.behavioralSignature → FinDist J)
    (children : Nat → Profile M.behavioralSignature → J → Profile M.behavioralSignature) :
    CFRDChildOracle M J := fun n trunk =>
  { seed := seeds n trunk
    child := children n trunk
    prediction := (cfrDExactValueOracle M clock fallback payoff cut remaining
      (fun k strategy => cfrDChildAverage M clock cut (seeds k strategy) strategy
        (children k strategy) fallback) n trunk).prediction }

/-- The constructed exact child oracle discharges numerical accuracy for
its own learned sequence. Child optimality is deliberately not inferred. -/
theorem cfrDExactChildFamily_accurate (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (seeds : Nat → Profile M.behavioralSignature → FinDist J)
    (children : Nat → Profile M.behavioralSignature → J → Profile M.behavioralSignature) :
    CFRDDepthAccurate M clock fallback payoff cut remaining
      (cfrDChildValueOracle M clock cut fallback
        (cfrDExactChildFamily M clock fallback payoff cut remaining seeds children)) 0 := by
  exact cfrDExactValueOracle_accurate M clock fallback payoff cut remaining
    (fun n trunk => cfrDChildAverage M clock cut (seeds n trunk) trunk
      (children n trunk) fallback)

variable [Fintype E.History]

/-- The actual constructed child resolver satisfies the existing corrected
finite-time security bound, with no additional replacement-loss term.
This still requires numerical accuracy and local child continuation quality. -/
theorem cfrDChildDepth_security (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (family : CFRDChildOracle M J) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining
      (cfrDChildValueOracle M clock cut fallback family) error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining
      (cfrDChildValueOracle M clock cut fallback family) loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (t : Nat) [NeZero t] :
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut remaining 0 +
          cfrDDepthErrorConstant M clock fallback cut remaining 1) * error +
        (cfrDDepthFiniteConstant M clock fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant M clock fallback cut remaining bound 1) / Real.sqrt t +
        2 * loss) ≤
      (privateCarriedResolve M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining
          (cfrDChildValueOracle M clock cut fallback family) n.val)
        (cfrDChildDepthResolver M clock fallback payoff cut remaining family t)
        unknown who cut remaining).expect (payoff who) := by
  rw [cfrDChildDepth_resolve_eq M clock hrecall]
  exact cfrDDepth_private_security M clock hrecall fallback payoff hzero cut remaining
    (cfrDChildValueOracle M clock cut fallback family) bound error loss hb he hl
    bounded accurate optimal reference equilibrium unknown who t

end GameTheory.ReBeL
