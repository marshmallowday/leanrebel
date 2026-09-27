/-
# Fixed-opponent values under changed compatible conditional kernels

Both slices use the canonical continuation runner and the same horizon,
observable and opposing policies. Their complete joint history laws may differ.
The exact L1 kernel discrepancy controls every legal response uniformly, hence
also the attained conditional optimum and the gap of a fixed own policy.
No equality of marginals, on-path premise or small-discrepancy certificate is used.
-/

import GameTheory.Analysis.ReBeL.PBSInfoValue
import GameTheory.Math.Probability.FinDistTransportRate

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe ui us ua up uq uk ut uv
variable {I : Type ui} {E : ExecutionProtocol.{ui, us, ua} I}
variable {M : InformationModel.{ui, us, ua, up, uq, uk} E}
variable [Fintype I] [DecidableEq I] [Fintype E.History]
variable {observations nextObservations : List M.PublicSignal} {who : I}
variable {T : Type ut} {U : Type uv}
variable (old : TypeBeliefSlice M observations who T)

/-- Changing a full conditional root kernel perturbs every fixed legal
response by its exact source-atom discrepancy. New-only atoms are included. -/
theorem conditionalPayoff_abs_sub_le_kernelVariation
    (fresh : TypeBeliefSlice M nextObservations who U)
    (opponents : Profile M.behavioralSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (replacement : M.BehavioralPolicy who) (oldType : T) (newType : U)
    (bound : ℝ) (bounded : ∀ history, |payoff history| ≤ bound) :
    |old.conditionalPayoff opponents fuel payoff replacement oldType -
      fresh.conditionalPayoff opponents fuel payoff replacement newType| ≤
      bound * FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law := by
  unfold conditionalPayoff PublicBelief.continuationLaw
  rw [FinDist.expect_bind, FinDist.expect_bind]
  apply FinDist.abs_expect_sub_le_atomVariation
  intro history
  exact FinDist.abs_expect_le_of_abs_bound _ _ (fun later _ => bounded later)

variable [∀ player, Fintype (E.Action player)]

/-- Uniform control of all legal responses controls the actual attained
Eq. (1) optima, including off-path completed types and nonunique maximizers.
The opponent and horizon are fixed, not independently re-solved. -/
theorem infoValue_abs_sub_le_kernelVariation
    (fresh : TypeBeliefSlice M nextObservations who U) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (opponents : Profile M.behavioralSignature) (oldType : T) (newType : U)
    (bound : ℝ) (bounded : ∀ history, |payoff history| ≤ bound) :
    |old.infoValue fallback fuel payoff opponents oldType -
      fresh.infoValue fallback fuel payoff opponents newType| ≤
      bound * FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law := by
  obtain ⟨left, leftAttains⟩ :=
    (old.infoValue_isGreatest hrecall fallback fuel payoff opponents oldType).1
  obtain ⟨right, rightAttains⟩ :=
    (fresh.infoValue_isGreatest hrecall fallback fuel payoff opponents newType).1
  have first := abs_le.mp (old.conditionalPayoff_abs_sub_le_kernelVariation fresh
    opponents fuel payoff left oldType newType bound bounded)
  have second := abs_le.mp (old.conditionalPayoff_abs_sub_le_kernelVariation fresh
    opponents fuel payoff right oldType newType bound bounded)
  have leftBound := fresh.conditionalPayoff_le_infoValue hrecall fallback fuel payoff
    opponents newType left
  have rightBound := old.conditionalPayoff_le_infoValue hrecall fallback fuel payoff
    opponents oldType right
  rw [leftAttains] at first
  rw [rightAttains] at second
  exact abs_le.mpr ⟨by linarith only [second.1, rightBound],
    by linarith only [first.2, leftBound]⟩

/-- Two kernel perturbations are charged: one for the conditional optimum,
one for the fixed policy payoff. This bounds the signed change in either
direction without replacing it by a certificate assumed from the caller. -/
theorem conditionalGap_abs_sub_le_kernelVariation
    (fresh : TypeBeliefSlice M nextObservations who U) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (opponents : Profile M.behavioralSignature) (replacement : M.BehavioralPolicy who)
    (oldType : T) (newType : U) (bound : ℝ)
    (bounded : ∀ history, |payoff history| ≤ bound) :
    |(fresh.infoValue fallback fuel payoff opponents newType -
        fresh.conditionalPayoff opponents fuel payoff replacement newType) -
      (old.infoValue fallback fuel payoff opponents oldType -
        old.conditionalPayoff opponents fuel payoff replacement oldType)| ≤
      2 * bound * FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law := by
  have values := abs_le.mp (old.infoValue_abs_sub_le_kernelVariation fresh hrecall
    fallback fuel payoff opponents oldType newType bound bounded)
  have policies := abs_le.mp (old.conditionalPayoff_abs_sub_le_kernelVariation fresh
    opponents fuel payoff replacement oldType newType bound bounded)
  apply abs_le.mpr
  constructor <;> linarith only [values.1, values.2, policies.1, policies.2]

/-- The changed-kernel absolute gap is bounded by the old gap plus the exact
kernel charge. The type domains may differ; the two queried types are explicit. -/
theorem conditionalGap_abs_le_old_add_kernelVariation
    (fresh : TypeBeliefSlice M nextObservations who U) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (opponents : Profile M.behavioralSignature) (replacement : M.BehavioralPolicy who)
    (oldType : T) (newType : U) (bound : ℝ)
    (bounded : ∀ history, |payoff history| ≤ bound) :
    |fresh.infoValue fallback fuel payoff opponents newType -
      fresh.conditionalPayoff opponents fuel payoff replacement newType| ≤
      |old.infoValue fallback fuel payoff opponents oldType -
        old.conditionalPayoff opponents fuel payoff replacement oldType| +
      2 * bound * FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law := by
  let oldGap := old.infoValue fallback fuel payoff opponents oldType -
    old.conditionalPayoff opponents fuel payoff replacement oldType
  let freshGap := fresh.infoValue fallback fuel payoff opponents newType -
    fresh.conditionalPayoff opponents fuel payoff replacement newType
  calc
    _ = |(freshGap - oldGap) + oldGap| := by congr 1; dsimp only [freshGap]; ring
    _ ≤ |freshGap - oldGap| + |oldGap| := abs_add _ _
    _ ≤ 2 * bound * FinDist.atomVariation (old.kernel oldType).law
        (fresh.kernel newType).law + |oldGap| :=
      add_le_add_right (old.conditionalGap_abs_sub_le_kernelVariation fresh hrecall
        fallback fuel payoff opponents replacement oldType newType bound bounded) _
    _ = _ := add_comm _ _

end GameTheory.ReBeL.TypeBeliefSlice
