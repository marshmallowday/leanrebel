/-
# Information-local public prescriptions

A prescription is a law for each realizable private action-observation history
at one public history. Selecting the whole prescription uses public history;
sampling the component for the actual private history is the referee's job.
The strategy domain here consists of public-history-indexed prescriptions, not
unrestricted reactions to additional announcements of opponents' plans.
-/

import GameTheory.ReBeL.PolicyDomain

noncomputable section

namespace GameTheory.ReBeL.Prescription

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel E)

/-- A realizable private AOH compatible with the stated public history. -/
abbrev Info (public : List M.PublicSignal) (i : ι) :=
  {info : PolicyDomain.Info (fullInformation M) i // info.1.publicHistory = public}

/-- A legal prescription at each public history. Private information indexes
components of a prescription; it is not supplied to the public selector. -/
abbrev Policy (i : ι) :=
  (public : List M.PublicSignal) → (info : Info M public i) →
    FinDist ((fullInformation M).Choice i info.1.1)

/-- Public prescriptions and the canonical history outcome carrier. -/
def signature : GameSignature ι where
  Strategy := Policy M
  Outcome := E.History

/-- Group an information-local policy into public prescriptions. -/
def ofRealized (i : ι) (policy : PolicyDomain.Policy (fullInformation M) i) : Policy M i :=
  fun _ info => policy info.1

/-- The referee uses the component at the player's own private AOH. -/
def toRealized (i : ι) (policy : Policy M i) : PolicyDomain.Policy (fullInformation M) i :=
  fun info => policy info.1.publicHistory ⟨info, rfl⟩

@[simp]
theorem toRealized_ofRealized (i : ι)
    (policy : PolicyDomain.Policy (fullInformation M) i) :
    toRealized M i (ofRealized M i policy) = policy := rfl

@[simp]
theorem ofRealized_toRealized (i : ι) (policy : Policy M i) :
    ofRealized M i (toRealized M i policy) = policy := by
  funext public info
  obtain ⟨info, hpublic⟩ := info
  subst public
  rfl

/-- An actual equivalence of legal local strategy carriers, not an assumed play equality. -/
def policyEquiv (i : ι) : PolicyDomain.Policy (fullInformation M) i ≃ Policy M i where
  toFun := ofRealized M i
  invFun := toRealized M i
  left_inv := toRealized_ofRealized M i
  right_inv := ofRealized_toRealized M i

/-- Full behavioral policy to legal public prescriptions. -/
def encode (i : ι) (policy : (fullInformation M).BehavioralPolicy i) : Policy M i :=
  ofRealized M i (PolicyDomain.restrict (fullInformation M) i policy)

/-- A legal fallback is needed only outside all realizable AOHs. -/
def decode (i : ι) (fallback : (fullInformation M).BehavioralPolicy i)
    (policy : Policy M i) : (fullInformation M).BehavioralPolicy i :=
  PolicyDomain.extend (fullInformation M) i fallback (toRealized M i policy)

@[simp]
theorem encode_decode (i : ι) (fallback : (fullInformation M).BehavioralPolicy i)
    (policy : Policy M i) : encode M i (decode M i fallback policy) = policy := by
  simp only [encode, decode, PolicyDomain.restrict_extend, ofRealized_toRealized]

/-- The round trip is exact at every real history, including every legal deviation path. -/
@[simp]
theorem decode_encode_at_history (i : ι)
    (fallback policy : (fullInformation M).BehavioralPolicy i) (h : E.History) :
    decode M i fallback (encode M i policy) ((fullInformation M).infoOf i h.trace) =
      policy ((fullInformation M).infoOf i h.trace) :=
  PolicyDomain.extend_restrict_at_history (fullInformation M) i fallback policy h

/-- A coordinatewise map: another player's strategy is never used. -/
def encodeProfile (profile : Profile (fullInformation M).behavioralSignature) :
    Profile (signature M) := fun i => encode M i (profile i)

/-- Coordinatewise decoding with an explicit legal fallback profile. -/
def decodeProfile (fallback : Profile (fullInformation M).behavioralSignature)
    (profile : Profile (signature M)) : Profile (fullInformation M).behavioralSignature :=
  fun i => decode M i (fallback i) (profile i)

@[simp]
theorem encodeProfile_decodeProfile (fallback : Profile (fullInformation M).behavioralSignature)
    (profile : Profile (signature M)) :
    encodeProfile M (decodeProfile M fallback profile) = profile := by
  funext i
  exact encode_decode M i (fallback i) (profile i)

/-- Encoding commutes with replacing exactly one player's entire policy. -/
theorem encodeProfile_update [DecidableEq ι]
    (profile : Profile (fullInformation M).behavioralSignature) (i : ι)
    (replacement : (fullInformation M).BehavioralPolicy i) :
    encodeProfile M (Profile.update profile i replacement) =
      Profile.update (encodeProfile M profile) i (encode M i replacement) := by
  funext j
  by_cases hj : j = i
  · subst j
    exact (congrArg (encode M i)
      (Profile.update_same (sig := (fullInformation M).behavioralSignature)
        profile i replacement)).trans
      (Profile.update_same (sig := signature M) (encodeProfile M profile)
        i (encode M i replacement)).symm
  · exact (congrArg (encode M j)
      (Profile.update_of_ne (sig := (fullInformation M).behavioralSignature)
        profile replacement hj)).trans
      (Profile.update_of_ne (sig := signature M) (encodeProfile M profile)
        (encode M i replacement) hj).symm

/-- Decoding fixes every opponent coordinate during a unilateral deviation. -/
theorem decodeProfile_update [DecidableEq ι]
    (fallback : Profile (fullInformation M).behavioralSignature)
    (profile : Profile (signature M)) (i : ι) (replacement : Policy M i) :
    decodeProfile M fallback (Profile.update profile i replacement) =
      Profile.update (decodeProfile M fallback profile) i (decode M i (fallback i) replacement) := by
  funext j
  by_cases hj : j = i
  · subst j
    exact (congrArg (decode M i (fallback i))
      (Profile.update_same (sig := signature M) profile i replacement)).trans
      (Profile.update_same (sig := (fullInformation M).behavioralSignature)
        (decodeProfile M fallback profile) i (decode M i (fallback i) replacement)).symm
  · exact (congrArg (decode M j (fallback j))
      (Profile.update_of_ne (sig := signature M) profile replacement hj)).trans
      (Profile.update_of_ne (sig := (fullInformation M).behavioralSignature)
        (decodeProfile M fallback profile) (decode M i (fallback i) replacement) hj).symm

/-- Decoding an encoded strategy preserves the full canonical execution law. -/
theorem run_decode_encode [Fintype ι]
    (fallback profile : Profile (fullInformation M).behavioralSignature)
    (fuel : Nat) (root : E.History) :
    (fullInformation M).runBehavioralFrom
        (decodeProfile M fallback (encodeProfile M profile)) fuel root =
      (fullInformation M).runBehavioralFrom profile fuel root :=
  PolicyDomain.run_extend_restrict (fullInformation M) fallback profile fuel root

end GameTheory.ReBeL.Prescription
