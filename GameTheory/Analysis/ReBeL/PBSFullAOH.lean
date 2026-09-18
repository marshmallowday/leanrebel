/-
# Constructing the finite infostate domain from a joint public belief

The infostates are exactly the full AOH values attained by legal histories in
the public fiber, not merely the states having positive probability today.
The off-path completion uses physically compatible history witnesses. Thus
zero-own-probability types remain in the domain. No payoff or best-response
property is supplied as a certificate in this construction.
-/

import GameTheory.Analysis.ReBeL.PBSGeometry
import GameTheory.Analysis.ReBeL.PBSOptimality

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E) [Fintype E.History]

/-- All physically attained root AOH values, including currently off-path ones. -/
def publicRootInfos (observations : List M.PublicSignal) (who : ι) :
    Finset ((fullInformation M).InfoState who) := by
  classical
  exact (Finset.univ.filter fun history : E.History =>
    publicTrace M.toInfoSignals history.trace = observations).image fun history =>
      (fullInformation M).infoOf who history.trace

/-- Membership supplies a legal history, not merely a syntactic AOH. -/
theorem mem_publicRootInfos (observations : List M.PublicSignal) (who : ι)
    (info : (fullInformation M).InfoState who) :
    info ∈ publicRootInfos M observations who ↔ ∃ history : E.History,
      publicTrace M.toInfoSignals history.trace = observations ∧
        (fullInformation M).infoOf who history.trace = info := by
  classical
  simp [publicRootInfos]

/-- A finite, lossless encoding of the actual root information states. -/
abbrev PublicRootType (observations : List M.PublicSignal) (who : ι) :=
  { info // info ∈ publicRootInfos M observations who }

noncomputable instance publicRootTypeFintype (observations : List M.PublicSignal) (who : ι) :
    Fintype (PublicRootType M observations who) := by
  classical
  unfold PublicRootType
  infer_instance

/-- Any probability law in the public fiber witnesses a nonempty type domain. -/
def publicRootFallback {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) (who : ι) :
    PublicRootType M observations who := by
  let history := belief.law.support_nonempty.choose
  exact ⟨(fullInformation M).infoOf who history.trace,
    (mem_publicRootInfos M observations who _).mpr
      ⟨history, belief.supported history belief.law.support_nonempty.choose_spec, rfl⟩⟩

/-- A total encoding on syntactic information. Only unattained prefixes use
this fallback; every legal root prefix is represented by itself. -/
def encodePublicRootType {observations : List M.PublicSignal} {who : ι}
    (fallback : PublicRootType M observations who) (info : (fullInformation M).InfoState who) :
    PublicRootType M observations who := by
  classical
  exact if member : info ∈ publicRootInfos M observations who then ⟨info, member⟩ else fallback

/-- The original full AOH prefix is remembered through every continuation. -/
def publicRootMemory {observations : List M.PublicSignal} {who : ι}
    (fallback : PublicRootType M observations who) :
    RootTypeMemory (fullInformation M) observations who (PublicRootType M observations who) :=
  fullRootTypeMemory M observations who (encodePublicRootType M fallback)

/-- At every legal root, decoding the type recovers the complete AOH. There
is no information coarsening or access to hidden state in the encoded type. -/
theorem publicRootMemory_read {observations : List M.PublicSignal} {who : ι}
    (fallback : PublicRootType M observations who) (history : E.History)
    (hpublic : publicTrace M.toInfoSignals history.trace = observations) :
    ((publicRootMemory M fallback).typeAt
      ((fullInformation M).infoOf who history.trace)).val =
        (fullInformation M).infoOf who history.trace := by
  classical
  have depth := AOH.publicHistory_length
    ((fullSignals M.toInfoSignals).infoOf who history.trace)
  rw [publicHistory_infoOf, length_infoOf, hpublic] at depth
  have before : ((fullInformation M).infoOf who history.trace).length ≤
      observations.length - 1 := by
    rw [length_infoOf]
    omega
  have member := (mem_publicRootInfos M observations who _).mpr ⟨history, hpublic, rfl⟩
  simp only [publicRootMemory, fullRootTypeMemory, encodePublicRootType,
    AOH.prefixAt_eq_of_length_le _ _ before, dif_pos member]

/-- Select one physically compatible root history for each attained type. -/
def publicRootWitness {observations : List M.PublicSignal} {who : ι}
    (type : PublicRootType M observations who) : E.History :=
  Classical.choose ((mem_publicRootInfos M observations who type.val).mp type.property)

/-- The selected history belongs to the right public and private fibers. -/
theorem publicRootWitness_spec {observations : List M.PublicSignal} {who : ι}
    (type : PublicRootType M observations who) :
    publicTrace M.toInfoSignals (publicRootWitness M type).trace = observations ∧
      (fullInformation M).infoOf who (publicRootWitness M type).trace = type.val :=
  Classical.choose_spec ((mem_publicRootInfos M observations who type.val).mp type.property)

/-- A compatible off-path completion. Positive-probability fibers will instead
use Bayes conditioning of the supplied joint law. -/
def publicRootOffPath {observations : List M.PublicSignal} {who : ι}
    (type : PublicRootType M observations who) :
    PublicBelief (fullInformation M).toInfoSignals observations where
  law := FinDist.pure (publicRootWitness M type)
  supported history supported := by
    have equal : history = publicRootWitness M type := by
      simpa only [FinDist.support_pure, Set.mem_singleton_iff] using supported
    subst history
    exact (publicRootWitness_spec M type).1

/-- The off-path completion has the named full infostate, even when that
infostate has zero probability in the current joint belief. -/
theorem publicRootOffPath_typed {observations : List M.PublicSignal} {who : ι}
    (fallback type : PublicRootType M observations who) (history : E.History)
    (supported : history ∈ (publicRootOffPath M type).law.support) :
    (publicRootMemory M fallback).typeAt ((fullInformation M).infoOf who history.trace) =
      type := by
  have equal : history = publicRootWitness M type := by
    simpa only [publicRootOffPath, FinDist.support_pure, Set.mem_singleton_iff] using supported
  subst history
  apply Subtype.ext
  exact (publicRootMemory_read M fallback _ (publicRootWitness_spec M type).1).trans
    (publicRootWitness_spec M type).2

/-- Every finite joint PBS gives a full-infostate slice. The supplied data is
only the game and belief; memory and compatible kernels are constructed. -/
def fullAOHBeliefSlice {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) (who : ι) :
    TypeBeliefSlice (fullInformation M) observations who (PublicRootType M observations who) :=
  TypeBeliefSlice.ofJointBelief (publicRootMemory M (publicRootFallback M belief who))
    belief (publicRootOffPath M) (publicRootOffPath_typed M (publicRootFallback M belief who))

/-- The type law uses the complete root information readout. -/
def fullAOHOwnLaw {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) (who : ι) :
    FinDist (PublicRootType M observations who) :=
  belief.law.map fun history => (fullAOHBeliefSlice M belief who).memory.typeAt
    ((fullInformation M).infoOf who history.trace)

/-- The construction preserves the entire initial joint law, so all subsequent
runner, payoff and unilateral-deviation results refer to that same PBS. -/
theorem fullAOHBeliefSlice_reconstruct {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) (who : ι) :
    ((fullAOHBeliefSlice M belief who).mixture (fullAOHOwnLaw M belief who)).law = belief.law :=
  TypeBeliefSlice.ofJointBelief_reconstruct
    (publicRootMemory M (publicRootFallback M belief who)) belief
    (publicRootOffPath M) (publicRootOffPath_typed M (publicRootFallback M belief who))

/-- Equality as public beliefs, including their existing canonical index. -/
theorem fullAOHBeliefSlice_eq {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) (who : ι) :
    (fullAOHBeliefSlice M belief who).mixture (fullAOHOwnLaw M belief who) = belief := by
  have equal := fullAOHBeliefSlice_reconstruct M belief who
  generalize (fullAOHBeliefSlice M belief who).mixture (fullAOHOwnLaw M belief who) = first at *
  cases first
  cases belief
  cases equal
  rfl

end GameTheory.ReBeL
