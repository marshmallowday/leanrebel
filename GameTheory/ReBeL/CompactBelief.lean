/-
# Compatibility-aware compact public beliefs

Local reaches are not marginal probabilities. A fixed joint chance and
compatibility factor is retained. The bridge to a public posterior is derived
from canonical execution, not postulated in a representation certificate.
The finite history enumeration is supplied only at normalization operations.
-/

import GameTheory.ReBeL.ReachWeights
import GameTheory.ReBeL.ReachFactorization
import GameTheory.ReBeL.Belief

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability
open scoped BigOperators

universe uι uh ui us ua up uq uk

@[ext]
theorem ReachWeights.ext {H : Type uh} {first second : ReachWeights H}
    (same : ∀ h, first.weight h = second.weight h) : first = second := by
  cases first
  cases second
  congr 1
  exact funext same

namespace ReachEncoding

variable {ι : Type uι} [Fintype ι] {H : Type uh} {Info : ι → Type ui}

/-- Fixed joint chance/compatibility multiplied by information-local reach factors. -/
def joint (chance : ReachWeights H) (observe : (i : ι) → H → Info i)
    (factors : (i : ι) → ReachWeights (Info i)) : ReachWeights H where
  weight h := chance.weight h * ∏ i, (factors i).weight (observe i h)
  nonneg h := mul_nonneg (chance.nonneg h)
    (Finset.prod_nonneg fun i _ => (factors i).nonneg (observe i h))

/-- An impossible joint chance state remains impossible for every choice of reaches. -/
theorem incompatible_zero (chance : ReachWeights H) (observe : (i : ι) → H → Info i)
    (factors : (i : ι) → ReachWeights (Info i)) (h : H) (zero : chance.weight h = 0) :
    (joint chance observe factors).weight h = 0 := by
  simp only [joint, zero, zero_mul]

/-- Public restriction changes the joint chance support, not its correlation structure. -/
theorem restrict_joint (chance : ReachWeights H) (observe : (i : ι) → H → Info i)
    (factors : (i : ι) → ReachWeights (Info i)) (event : Set H) :
    (joint chance observe factors).restrict event =
      joint (chance.restrict event) observe factors := by
  classical
  apply ReachWeights.ext
  intro h
  by_cases inside : h ∈ event <;> simp [ReachWeights.restrict, joint, inside]

/-- The probability of a forbidden pair is zero after normalization too. -/
theorem incompatible_prob_zero [Fintype H] (chance : ReachWeights H)
    (observe : (i : ι) → H → Info i) (factors : (i : ι) → ReachWeights (Info i))
    (positive : 0 < (joint chance observe factors).mass) (h : H)
    (zero : chance.weight h = 0) :
    ((joint chance observe factors).normalize positive).prob h = 0 := by
  rw [ReachWeights.prob_normalize, incompatible_zero chance observe factors h zero, zero_div]

/-- The number of variable entries is a sum of local carrier sizes. The fixed joint
chance table is separate data; this is not a universal total-memory complexity claim. -/
theorem variable_slots [∀ i, Fintype (Info i)] :
    Fintype.card ((i : ι) × Info i) = ∑ i, Fintype.card (Info i) :=
  Fintype.card_sigma

/-- Two players with D labelled F-sided dice need two local F^D reach vectors. -/
theorem dice_variable_slots (faces dice : Nat) :
    Fintype.card ((Fin dice → Fin faces) ⊕ (Fin dice → Fin faces)) = 2 * faces ^ dice := by
  simp only [Fintype.card_sum, Fintype.card_fun, Fintype.card_fin]
  omega

/-- A joint table has the product size, even when some entries are incompatible. -/
theorem dice_joint_slots (faces dice : Nat) :
    Fintype.card ((Fin dice → Fin faces) × (Fin dice → Fin faces)) = (faces ^ dice) ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_two]

/-- The paper's one-card-per-player variable-vector count; compatibility is still required. -/
theorem card_variable_slots : Fintype.card (Fin 52 ⊕ Fin 52) = 104 := by
  norm_num

end ReachEncoding

namespace PublicBelief

variable {ι : Type uι} [Fintype ι] {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel E)

/-- Fixed chance weights on the stated public fiber, independent of the policy profile. -/
def publicChance (observations : List M.PublicSignal) : ReachWeights E.History :=
  (⟨fun h => chanceReach h.trace, fun h => (chanceReach_pos h.trace).le⟩ :
    ReachWeights E.History).restrict {h | publicTrace M.toInfoSignals h.trace = observations}

/-- One private-AOH reach vector per player; no other player's state is an argument. -/
def localFactors (profile : Profile (fullInformation M).behavioralSignature)
    (i : ι) : ReachWeights (AOH (E.Action i) (M.PrivateSignal i) M.PublicSignal) :=
  ⟨ownReach M i (profile i), ownReach_nonneg M i (profile i)⟩

/-- The reference-compatible unnormalized compact decoding. -/
def compactWeights (profile : Profile (fullInformation M).behavioralSignature)
    (observations : List M.PublicSignal) : ReachWeights E.History :=
  ReachEncoding.joint (publicChance M observations)
    (fun i h => (fullInformation M).infoOf i h.trace) (localFactors M profile)

/-- Exact equality to the public restriction of the canonical finite-depth execution law.
The depth condition prevents silently equating a truncated run with an eventual outcome. -/
theorem compactWeights_eq_reference [Fintype E.History]
    (profile : Profile (fullInformation M).behavioralSignature) (depth : Nat)
    (observations : List M.PublicSignal) (length : observations.length = depth + 1) :
    compactWeights M profile observations =
      (ReachWeights.ofLaw ((fullInformation M).runBehavioral profile depth)).restrict
        {h | publicTrace M.toInfoSignals h.trace = observations} := by
  classical
  apply ReachWeights.ext
  intro h
  by_cases inside : publicTrace M.toInfoSignals h.trace = observations
  · have hdepth : h.trace.length = depth := by
      have hlength := publicTrace_length M.toInfoSignals h.trace
      rw [inside, length] at hlength
      omega
    have factor := historyReach_eq_chance_mul_own M profile h.trace
    simp only [InformationModel.historyReachProbability, hdepth] at factor
    simpa only [compactWeights, ReachEncoding.joint, publicChance, ReachWeights.restrict,
      Set.mem_ofPred_eq, inside, if_true, localFactors, ReachWeights.ofLaw] using factor.symm
  · simp [compactWeights, ReachEncoding.joint, publicChance, ReachWeights.restrict,
      inside]

/-- The compact decoder has positive mass exactly when the public observation is possible. -/
theorem compactWeights_mass [Fintype E.History]
    (profile : Profile (fullInformation M).behavioralSignature) (depth : Nat)
    (observations : List M.PublicSignal) (length : observations.length = depth + 1) :
    (compactWeights M profile observations).mass =
      ((fullInformation M).runBehavioral profile depth).probOf
        {h | publicTrace M.toInfoSignals h.trace = observations} := by
  rw [compactWeights_eq_reference M profile depth observations length,
    ReachWeights.mass_restrict_ofLaw]

/-- Positive compact decoding is exactly the supported joint PBS, not a product of marginals. -/
theorem compact_normalize_eq_condition [Fintype E.History]
    (profile : Profile (fullInformation M).behavioralSignature) (depth : Nat)
    (observations : List M.PublicSignal) (length : observations.length = depth + 1)
    (possible : Possible (S := M.toInfoSignals)
      ((fullInformation M).runBehavioral profile depth) observations) :
    (compactWeights M profile observations).normalize
      (by rw [compactWeights_mass M profile depth observations length]
          exact FinDist.probOf_pos possible) =
      (condition ((fullInformation M).runBehavioral profile depth) observations possible).law := by
  simpa only [compactWeights_eq_reference M profile depth observations length, condition] using
    ReachWeights.normalize_restrict_ofLaw ((fullInformation M).runBehavioral profile depth)
      {h | publicTrace M.toInfoSignals h.trace = observations} possible

end PublicBelief

end GameTheory.ReBeL
