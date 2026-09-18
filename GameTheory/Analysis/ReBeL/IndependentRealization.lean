/-
# Independent private iteration seeds and behavioral realization

Every player draws its own iteration index once. The seeds are independent
across players, while that player's decisions remain correlated by its fixed
index. Own-reach weighting, rather than coordinate averaging, realizes this
law for every payoff and every finite terminal-aware horizon.
-/

import GameTheory.Analysis.ReBeL.OwnReachAverage
import GameTheory.Analysis.ReBeL.OutcomeReach
import GameTheory.Analysis.ReBeL.PolicyPatching

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- Products of single-coordinate observables factor under independent finite
seed laws. This is not valid for one seed shared by all players. -/
theorem independent_seed_product_expectation {I : Type*} [Fintype I]
    {K : I → Type*} [∀ i, Fintype (K i)]
    (seeds : (i : I) → FinDist (K i)) (observable : (i : I) → K i → ℝ) :
    (FinDist.pi seeds).expect (fun selection => ∏ i, observable i (selection i)) =
      ∏ i, (seeds i).expect (observable i) := by
  classical
  simp_rw [FinDist.expect_eq_sum, FinDist.prob_pi, ← Finset.prod_mul_distrib]
  symm
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (K i)))
      (fun i k => (seeds i).prob k * observable i k))

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- Each player uses the selected iteration's whole behavioral policy, not a
freshly redrawn iteration at each information state. -/
def privateSeedProfile (plays : K → Profile M.behavioralSignature) (selection : ι → K) :
    Profile M.behavioralSignature := fun who => plays (selection who) who

/-- Own reach depends on the focal seed only. Opponents may have different
iteration indices and need not be fixed across the outer expectation. -/
theorem privateSeedProfile_ownReach (plays : K → Profile M.behavioralSignature)
    (selection : ι → K) (who : ι) {state : E.State} (trace : E.Trace state) :
    M.playerReachProbability (privateSeedProfile M plays selection) who trace =
      M.playerReachProbability (plays (selection who)) who trace := by
  apply ownReach_eq_of_agree_before M _ _ who trace.length
  · intro history _ _ _
    rfl
  · exact le_rfl

variable [Fintype ι]

/-- The meaning of private independent iteration randomization: draw a vector
of seeds once, then run the original canonical game. -/
def privateSeedOutcome (seeds : ι → FinDist K)
    (plays : K → Profile M.behavioralSignature) (horizon : ℕ) : FinDist E.History :=
  (FinDist.pi seeds).bind fun selection =>
    M.runBehavioral (privateSeedProfile M plays selection) horizon

variable [Fintype K]

/-- Own-reach weighted behavioral policies realize the full outcome law of
independent private iteration seeds. This includes zero-reach information
states, absorbed terminal histories and arbitrary correlated chance moves. -/
theorem ownReachAverage_realizes_privateSeeds (hrecall : M.PerfectRecall)
    (seeds : ι → FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (horizon : ℕ) :
    M.runBehavioral (ownReachAverageProfile M seeds plays fallback) horizon =
      privateSeedOutcome M seeds plays horizon := by
  classical
  apply FinDist.ext_of_prob
  intro history
  rw [run_probability_factorization M, privateSeedOutcome, FinDist.prob_bind]
  simp_rw [run_probability_factorization M, privateSeedProfile_ownReach M,
    ownReachAverage_playerReach M hrecall]
  rw [FinDist.expect_smul]
  exact congrArg (fun value : ℝ => outcomeChanceWeight horizon history * value)
    (independent_seed_product_expectation seeds
      (fun who k => M.playerReachProbability (plays k) who history.trace)).symm

/-- Realization preserves every expected history payoff, not merely terminal
state marginals or one hand-picked utility function. -/
theorem ownReachAverage_expected_payoff (hrecall : M.PerfectRecall)
    (seeds : ι → FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (horizon : ℕ) (payoff : E.History → ℝ) :
    (M.runBehavioral (ownReachAverageProfile M seeds plays fallback) horizon).expect payoff =
      (FinDist.pi seeds).expect (fun selection =>
        (M.runBehavioral (privateSeedProfile M plays selection) horizon).expect payoff) := by
  rw [ownReachAverage_realizes_privateSeeds M hrecall, privateSeedOutcome, FinDist.expect_bind]

end GameTheory.ReBeL
