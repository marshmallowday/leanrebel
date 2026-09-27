/-
# Fixed-opponent values under changed compatible conditional kernels

Both slices use the canonical continuation runner and the same horizon,
observable and opposing policies. Their complete joint history laws may differ.
The exact L1 kernel discrepancy controls every legal response uniformly, hence
also the attained conditional optimum and the gap of a fixed own policy.
No equality of marginals, on-path premise or small-discrepancy certificate is used.
The final section also transports values across changed opposing profiles,
charging canonical execution at both attained responses and the retained policy.
-/

import GameTheory.Analysis.ReBeL.PBSOpponentModelTransport
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


omit [Fintype E.History] in
/-- The value-comparison kernel comes from the supplied joint PBS, rather than
an independently chosen type slice. Supported types use certified conditioning;
absent types remain the caller's explicit compatible completion. -/
theorem conditionalPayoff_ofJointBelief
    (memory : RootTypeMemory M observations who T)
    (belief : PublicBelief M.toInfoSignals observations)
    (offPath : T → PublicBelief M.toInfoSignals observations)
    (compatible : ∀ type history, history ∈ (offPath type).law.support →
      memory.typeAt (M.infoOf who history.trace) = type)
    (type : T)
    (reached : type ∈ (belief.law.map
      (fun history => memory.typeAt (M.infoOf who history.trace))).support)
    (opponents : Profile M.behavioralSignature) (fuel : Nat)
    (payoff : E.History → ℝ) (replacement : M.BehavioralPolicy who) :
    (ofJointBelief memory belief offPath compatible).conditionalPayoff
        opponents fuel payoff replacement type =
      ((belief.law.condOnFibre
        (fun history => memory.typeAt (M.infoOf who history.trace)) type).bind
        (M.runBehavioralFrom (Profile.update opponents who replacement) fuel)).expect payoff := by
  unfold conditionalPayoff PublicBelief.continuationLaw
  rw [ofJointBelief_kernel_law memory belief offPath compatible type reached]

omit [Fintype E.History] in
/-- Reconstructing the current PBS before evaluating its continuation gives
the weighted conditional values at precisely that PBS's type kernels. -/
theorem conditionalPayoff_ofJointBelief_mean
    (memory : RootTypeMemory M observations who T)
    (belief : PublicBelief M.toInfoSignals observations)
    (offPath : T → PublicBelief M.toInfoSignals observations)
    (compatible : ∀ type history, history ∈ (offPath type).law.support →
      memory.typeAt (M.infoOf who history.trace) = type)
    (opponents : Profile M.behavioralSignature) (fuel : Nat)
    (payoff : E.History → ℝ) (replacement : M.BehavioralPolicy who) :
    (belief.law.map (fun history => memory.typeAt (M.infoOf who history.trace))).expect
        (fun type => (ofJointBelief memory belief offPath compatible).conditionalPayoff
          opponents fuel payoff replacement type) =
      (PublicBelief.continuationLaw M (Profile.update opponents who replacement)
        fuel belief).expect payoff := by
  have decomposed := (ofJointBelief memory belief offPath compatible).mixture_payoff
    (belief.law.map (fun history => memory.typeAt (M.infoOf who history.trace)))
    (Profile.update opponents who replacement) fuel payoff
  unfold PublicBelief.continuationLaw at decomposed
  rw [ofJointBelief_reconstruct memory belief offPath compatible] at decomposed
  exact decomposed.symm

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
  dsimp only at leftAttains rightAttains
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
    _ ≤ |freshGap - oldGap| + |oldGap| := abs_add_le _ _
    _ ≤ 2 * bound * FinDist.atomVariation (old.kernel oldType).law
        (fresh.kernel newType).law + |oldGap| :=
      add_le_add (old.conditionalGap_abs_sub_le_kernelVariation fresh hrecall
        fallback fuel payoff opponents replacement oldType newType bound bounded) le_rfl
    _ = _ := add_comm _ _

end GameTheory.ReBeL.TypeBeliefSlice

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut uv
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable {M : InformationModel.{0, us, ua, up, uq, uk} E}
variable [Fintype E.History]
variable {observations nextObservations : List M.PublicSignal} {who : Fin 2}
variable {T : Type ut} {U : Type uv}
variable (old : TypeBeliefSlice M observations who T)

/-- The canonical one-step execution charge with the SAME own response on both
sides. Prefix weights come from the old kernel and first opponent, including
histories absent from the second model. No value stability premise is supplied. -/
def responseExecutionCharge (first second : Profile M.behavioralSignature)
    (fuel : Nat) (replacement : M.BehavioralPolicy who) (type : T) : ℝ :=
  executionKernelCharge M (Profile.update first who replacement)
    (Profile.update second who replacement) fuel (old.kernel type).law

/-- Keeping the opposing profile unchanged makes its execution charge vanish. -/
theorem responseExecutionCharge_self (profile : Profile M.behavioralSignature)
    (fuel : Nat) (replacement : M.BehavioralPolicy who) (type : T) :
    old.responseExecutionCharge profile profile fuel replacement type = 0 :=
  executionKernelCharge_self M _ fuel (old.kernel type).law

/-- Root-kernel and opponent changes have separate, derived costs. The latter
is accumulated along actual first-profile visits, not second-model weights. -/
theorem conditionalPayoff_abs_sub_le_executionCharge
    (fresh : TypeBeliefSlice M nextObservations who U)
    (first second : Profile M.behavioralSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (replacement : M.BehavioralPolicy who) (oldType : T) (newType : U)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ history, |payoff history| ≤ bound) :
    |old.conditionalPayoff first fuel payoff replacement oldType -
      fresh.conditionalPayoff second fuel payoff replacement newType| ≤
      bound * (FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law +
        old.responseExecutionCharge first second fuel replacement oldType) := by
  unfold conditionalPayoff PublicBelief.continuationLaw
  exact (FinDist.abs_expect_sub_le_atomVariation _ _ payoff bound bounded).trans
    (mul_le_mul_of_nonneg_left
      (runBehavioralFrom_atomVariation_le M _ _ fuel _ _) nonneg)

variable [∀ player, Fintype (E.Action player)]

/-- Only two explicitly constructed best responses are needed to compare
attained optima. Their execution charges are computed, not postulated bounds
over all policies. Ties use the existing canonical simultaneous responses. -/
def optimalResponseExecutionCharge (fresh : TypeBeliefSlice M nextObservations who U)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (first second : Profile M.behavioralSignature) (type : T) : ℝ :=
  max (old.responseExecutionCharge first second fuel
      (old.simultaneousResponse fallback fuel payoff first).toBehavioral type)
    (old.responseExecutionCharge first second fuel
      (fresh.simultaneousResponse fallback fuel payoff second).toBehavioral type)

/-- The optimal-response charge vanishes for identical opposing profiles,
even if the new slice has different type domains and off-path completions. -/
theorem optimalResponseExecutionCharge_self
    (fresh : TypeBeliefSlice M nextObservations who U)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (profile : Profile M.behavioralSignature) (type : T) :
    old.optimalResponseExecutionCharge fresh fallback fuel payoff profile profile type = 0 := by
  simp only [optimalResponseExecutionCharge, responseExecutionCharge_self, max_self]

/-- Changing opponents is charged at both actual maximizing legal responses.
Neither equality of opponents nor an assumed optimal-value bound is required. -/
theorem infoValue_abs_sub_le_executionCharge
    (fresh : TypeBeliefSlice M nextObservations who U) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (first second : Profile M.behavioralSignature) (oldType : T) (newType : U)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ history, |payoff history| ≤ bound) :
    |old.infoValue fallback fuel payoff first oldType -
      fresh.infoValue fallback fuel payoff second newType| ≤
      bound * (FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law +
        old.optimalResponseExecutionCharge fresh fallback fuel payoff first second oldType) := by
  let left := (old.simultaneousResponse fallback fuel payoff first).toBehavioral
  let right := (fresh.simultaneousResponse fallback fuel payoff second).toBehavioral
  have leftCost : old.responseExecutionCharge first second fuel left oldType ≤
      old.optimalResponseExecutionCharge fresh fallback fuel payoff first second oldType :=
    le_max_left _ _
  have rightCost : old.responseExecutionCharge first second fuel right oldType ≤
      old.optimalResponseExecutionCharge fresh fallback fuel payoff first second oldType :=
    le_max_right _ _
  have firstBound := abs_le.mp ((old.conditionalPayoff_abs_sub_le_executionCharge fresh
    first second fuel payoff left oldType newType bound nonneg bounded).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl leftCost) nonneg))
  have secondBound := abs_le.mp ((old.conditionalPayoff_abs_sub_le_executionCharge fresh
    first second fuel payoff right oldType newType bound nonneg bounded).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl rightCost) nonneg))
  have leftAttains : old.conditionalPayoff first fuel payoff left oldType =
      old.infoValue fallback fuel payoff first oldType :=
    old.simultaneousResponse_attains fallback fuel payoff first oldType
  have rightAttains : fresh.conditionalPayoff second fuel payoff right newType =
      fresh.infoValue fallback fuel payoff second newType :=
    fresh.simultaneousResponse_attains fallback fuel payoff second newType
  have leftBound := fresh.conditionalPayoff_le_infoValue hrecall fallback fuel payoff
    second newType left
  have rightBound := old.conditionalPayoff_le_infoValue hrecall fallback fuel payoff
    first oldType right
  rw [leftAttains] at firstBound
  rw [rightAttains] at secondBound
  exact abs_le.mpr ⟨by linarith only [secondBound.1, rightBound],
    by linarith only [firstBound.2, leftBound]⟩

/-- Signed gap drift pays for the optimum AND the retained own response.
The root discrepancy has coefficient two; opposing-policy costs are separate. -/
theorem conditionalGap_abs_sub_le_executionCharge
    (fresh : TypeBeliefSlice M nextObservations who U) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (first second : Profile M.behavioralSignature) (replacement : M.BehavioralPolicy who)
    (oldType : T) (newType : U) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound) :
    |(fresh.infoValue fallback fuel payoff second newType -
        fresh.conditionalPayoff second fuel payoff replacement newType) -
      (old.infoValue fallback fuel payoff first oldType -
        old.conditionalPayoff first fuel payoff replacement oldType)| ≤
      2 * bound * FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law +
      bound * (old.optimalResponseExecutionCharge fresh fallback fuel payoff first second oldType +
        old.responseExecutionCharge first second fuel replacement oldType) := by
  have values := abs_le.mp (old.infoValue_abs_sub_le_executionCharge fresh hrecall
    fallback fuel payoff first second oldType newType bound nonneg bounded)
  have policies := abs_le.mp (old.conditionalPayoff_abs_sub_le_executionCharge fresh
    first second fuel payoff replacement oldType newType bound nonneg bounded)
  apply abs_le.mpr
  constructor <;> linarith only [values.1, values.2, policies.1, policies.2]

/-- The old absolute gap remains usable after both kernels and opponents
change, with no new optimizer, regret, or small-variation certificate. -/
theorem conditionalGap_abs_le_old_add_executionCharge
    (fresh : TypeBeliefSlice M nextObservations who U) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (first second : Profile M.behavioralSignature) (replacement : M.BehavioralPolicy who)
    (oldType : T) (newType : U) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound) :
    |fresh.infoValue fallback fuel payoff second newType -
      fresh.conditionalPayoff second fuel payoff replacement newType| ≤
      |old.infoValue fallback fuel payoff first oldType -
        old.conditionalPayoff first fuel payoff replacement oldType| +
      (2 * bound * FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law +
        bound * (old.optimalResponseExecutionCharge fresh fallback fuel payoff
          first second oldType +
          old.responseExecutionCharge first second fuel replacement oldType)) := by
  let oldGap := old.infoValue fallback fuel payoff first oldType -
    old.conditionalPayoff first fuel payoff replacement oldType
  let freshGap := fresh.infoValue fallback fuel payoff second newType -
    fresh.conditionalPayoff second fuel payoff replacement newType
  calc
    _ = |(freshGap - oldGap) + oldGap| := by congr 1; dsimp only [freshGap]; ring
    _ ≤ |freshGap - oldGap| + |oldGap| := abs_add_le _ _
    _ ≤ _ := (add_le_add
      (old.conditionalGap_abs_sub_le_executionCharge fresh hrecall fallback fuel payoff
        first second replacement oldType newType bound nonneg bounded) le_rfl).trans_eq
          (add_comm _ _)

/-- Primitive one-step bounds for legal responses turn the measured
changed-opponent gap cost into a horizon rate. The root discrepancy remains
separate. Solver Nash accuracy alone does not supply the primitive premise. -/
theorem conditionalGap_abs_sub_le_executionRate
    (fresh : TypeBeliefSlice M nextObservations who U) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (first second : Profile M.behavioralSignature) (replacement : M.BehavioralPolicy who)
    (oldType : T) (newType : U) (bound rate : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound)
    (steps : ∀ (response : M.BehavioralPolicy who) history, FinDist.atomVariation
      (M.runBehavioralFrom (Profile.update first who response) 1 history)
      (M.runBehavioralFrom (Profile.update second who response) 1 history) ≤ rate) :
    |(fresh.infoValue fallback fuel payoff second newType -
        fresh.conditionalPayoff second fuel payoff replacement newType) -
      (old.infoValue fallback fuel payoff first oldType -
        old.conditionalPayoff first fuel payoff replacement oldType)| ≤
      2 * bound * FinDist.atomVariation (old.kernel oldType).law (fresh.kernel newType).law +
        2 * bound * (fuel : ℝ) * rate := by
  have responseBound (response : M.BehavioralPolicy who) :
      old.responseExecutionCharge first second fuel response oldType ≤ (fuel : ℝ) * rate :=
    executionKernelCharge_le_mul M _ _ rate (steps response) fuel (old.kernel oldType).law
  have optimumBound : old.optimalResponseExecutionCharge fresh fallback fuel payoff
      first second oldType ≤ (fuel : ℝ) * rate :=
    max_le (responseBound _) (responseBound _)
  have costs := mul_le_mul_of_nonneg_left
    (add_le_add optimumBound (responseBound replacement)) nonneg
  have gap := old.conditionalGap_abs_sub_le_executionCharge fresh hrecall fallback
    fuel payoff first second replacement oldType newType bound nonneg bounded
  nlinarith only [costs, gap]

end GameTheory.ReBeL.TypeBeliefSlice


namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut uv
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ player, Fintype (E.Action player)]

/-- Compare a prior joint-PBS slice with the actual next state's stored-model
slice. Both supported kernels are replaced by their concrete conditionals.
Different type domains and changed comparison opponents remain explicit;
neither posterior equality to the factual opponent nor small drift is assumed. -/
theorem resolvedNextState_conditionalGap_le {K : Type*} {T : Type ut} {U : Type uv}
    (state : PrivateIterationState M K)
    (belief : PublicBelief M.toInfoSignals (publicTrace M.toInfoSignals state.history.trace))
    (stored : state.belief = some belief)
    (chosen : Profile M.behavioralSignature) (steps : Nat) (history : E.History)
    (positive : publicTrace M.toInfoSignals history.trace ∈
      (PublicBelief.publicLaw (S := M.toInfoSignals)
        (PublicBelief.continuationLaw M chosen steps belief)).support)
    (who : Fin 2)
    (oldMemory : RootTypeMemory M (publicTrace M.toInfoSignals state.history.trace) who T)
    (oldOff : T → PublicBelief M.toInfoSignals
      (publicTrace M.toInfoSignals state.history.trace))
    (oldCompatible : ∀ type h, h ∈ (oldOff type).law.support →
      oldMemory.typeAt (M.infoOf who h.trace) = type)
    (newMemory : RootTypeMemory M (publicTrace M.toInfoSignals history.trace) who U)
    (newOff : U → PublicBelief M.toInfoSignals (publicTrace M.toInfoSignals history.trace))
    (newCompatible : ∀ type h, h ∈ (newOff type).law.support →
      newMemory.typeAt (M.infoOf who h.trace) = type)
    (oldType : T) (newType : U)
    (oldReached : oldType ∈
      (belief.law.map (fun h => oldMemory.typeAt (M.infoOf who h.trace))).support)
    (hrecall : M.PerfectRecall) (fallback : Profile M.strategicSignature)
    (fuel : Nat) (payoff : E.History → ℝ)
    (first second : Profile M.behavioralSignature) (replacement : M.BehavioralPolicy who)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h, |payoff h| ≤ bound) :
    let modelLaw := PublicBelief.continuationLaw M chosen steps belief
    let posterior := PublicBelief.atObservation modelLaw
      (publicTrace M.toInfoSignals history.trace) positive
    let old := TypeBeliefSlice.ofJointBelief oldMemory belief oldOff oldCompatible
    let fresh := TypeBeliefSlice.ofJointBelief newMemory posterior newOff newCompatible
    (resolvedNextState M state chosen steps history).belief = some posterior ∧
      (newType ∈ (posterior.law.map
        (fun h => newMemory.typeAt (M.infoOf who h.trace))).support →
        |fresh.infoValue fallback fuel payoff second newType -
          fresh.conditionalPayoff second fuel payoff replacement newType| ≤
        |old.infoValue fallback fuel payoff first oldType -
          old.conditionalPayoff first fuel payoff replacement oldType| +
        (2 * bound * FinDist.atomVariation
          (belief.law.condOnFibre (fun h => oldMemory.typeAt (M.infoOf who h.trace)) oldType)
          ((modelLaw.condOnFibre (fun h => publicTrace M.toInfoSignals h.trace)
            (publicTrace M.toInfoSignals history.trace)).condOnFibre
              (fun h => newMemory.typeAt (M.infoOf who h.trace)) newType) +
          bound * (old.optimalResponseExecutionCharge fresh fallback fuel payoff
            first second oldType +
            old.responseExecutionCharge first second fuel replacement oldType))) := by
  intro modelLaw posterior old fresh
  have identified := resolvedNextState_typeKernel_law M state belief stored chosen steps
    history positive who newMemory newOff newCompatible newType
  constructor
  · exact identified.1
  · intro newReached
    have oldKernel : (old.kernel oldType).law =
        belief.law.condOnFibre (fun h => oldMemory.typeAt (M.infoOf who h.trace)) oldType :=
      TypeBeliefSlice.ofJointBelief_kernel_law oldMemory belief oldOff oldCompatible
        oldType oldReached
    have newKernel := identified.2 newReached
    have estimate := old.conditionalGap_abs_le_old_add_executionCharge fresh hrecall
      fallback fuel payoff first second replacement oldType newType bound nonneg bounded
    rw [oldKernel, newKernel] at estimate
    exact estimate

end GameTheory.ReBeL
