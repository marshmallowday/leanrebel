/-
# Executable full-game CFR over rational evaluation tables

This is a numerical frontend, not a second game semantics. Its rows encode
legal histories, information-local choices and rational chance transitions.
Analysis must prove each table's correspondence with canonical Protocol data.
No regret values, root decomposition or equilibrium oracle are inputs.
-/

import GameTheory.ReBeL.Rational.Algorithm

namespace GameTheory.ReBeL.Rational

universe ui uh uq ua

variable {ι : Type ui} {H : Type uh} {Info : ι → Type uq}
variable {Choice : (who : ι) → Info who → Type ua}

/-- Numerical strategies retain the same information-local dependent shape.
A physical history is never an argument of a player's strategy. -/
abbrev tableSignature (H : Type uh) (Info : ι → Type uq)
    (Choice : (who : ι) → Info who → Type ua) : GameSignature ι where
  Strategy who := (info : Info who) → Choice who info → ℚ
  Outcome := H

/-- The local signature lets policy commitments reuse the shared update API. -/
abbrev localTableSignature {Q : Type*} (Choice : Q → Type*) : GameSignature Q where
  Strategy info := Choice info → ℚ
  Outcome := Unit

/-- Proof-free finite evaluation data. The list contains every legal history,
including off-policy rows; transition lists can be sparse. Interpretation is
checked downstream, not asserted by this raw data structure. -/
structure HistoryTable (H : Type uh) (Info : ι → Type uq)
    (Choice : (who : ι) → Info who → Type ua) where
  /-- The full canonical-history enumeration in a chosen runtime representation. -/
  histories : List H
  /-- The initial history row. -/
  initial : H
  /-- Information supplied to each player's policy at a row. -/
  info : (who : ι) → H → Info who
  /-- The actual terminal flag, not an iteration stopping criterion. -/
  terminal : H → Bool
  /-- Exact rational successors for one selected legal joint choice. -/
  children : (history : H) → ((who : ι) → Choice who (info who history)) → List (H × ℚ)
  /-- The cumulative payoff of a history, including a partial cut. -/
  payoff : H → ι → ℚ
  /-- Own information/choice occurrences in each complete legal prefix. -/
  ownPath : (who : ι) → H → List (Sigma (Choice who))
  /-- Chance factors along that prefix, before any strategic probabilities. -/
  chanceFactors : H → List ℚ
  /-- Precisely the realized nonterminal decision information states. -/
  decision : (who : ι) → Info who → Bool
  /-- Information-local trace depth, used for a common absolute horizon. -/
  depth : (who : ι) → Info who → ℕ

namespace HistoryTable

variable (G : HistoryTable H Info Choice)

/-- A numerical profile is normalized independently at every local menu. -/
def ValidPolicy [∀ who info, Fintype (Choice who info)]
    (policy : Profile (tableSignature H Info Choice)) : Prop :=
  ∀ who info, (∀ a, 0 ≤ policy who info a) ∧ ∑ a, policy who info a = 1

/-- The product of only this player's own action probabilities. -/
def ownReach (policy : Profile (tableSignature H Info Choice)) (who : ι) (history : H) : ℚ :=
  ((G.ownPath who history).map fun entry => policy who entry.1 entry.2).prod

/-- All opponents and chance contribute to counterfactual reach; the focal
player's own earlier action probabilities are deliberately omitted. -/
def counterfactualReach [Fintype ι] [DecidableEq ι]
    (policy : Profile (tableSignature H Info Choice)) (who : ι) (history : H) : ℚ :=
  (G.chanceFactors history).prod * ∏ other ∈ Finset.univ.erase who,
    G.ownReach policy other history

variable [Fintype ι] [DecidableEq ι]
variable [∀ who info, Fintype (Choice who info)]
variable [∀ who, DecidableEq (Info who)]
variable [∀ who info, DecidableEq (Choice who info)]

/-- Independent simultaneous local choices, not a shared random action tuple. -/
def jointWeight (policy : Profile (tableSignature H Info Choice)) (history : H)
    (draw : (who : ι) → Choice who (G.info who history)) : ℚ :=
  ∏ who, policy who (G.info who history) (draw who)

/-- Exact bounded continuation evaluation on a sparse transition table.
Zero-weight branches are not evaluated, but remain part of the mathematical sum. -/
def value (policy : Profile (tableSignature H Info Choice)) : ℕ → H → ι → ℚ
  | 0, history, who => G.payoff history who
  | fuel + 1, history, who =>
      if G.terminal history then G.payoff history who
      else ∑ draw : (player : ι) → Choice player (G.info player history),
        let probability := G.jointWeight policy history draw
        if probability = 0 then 0 else probability *
          ((G.children history draw).map fun next =>
            if next.2 = 0 then 0 else next.2 * value policy fuel next.1 who).sum

/-- Commit one local law, leaving all other information states and players unchanged. -/
def commit (policy : Profile (tableSignature H Info Choice)) (who : ι)
    (info : Info who) (law : Choice who info → ℚ) :
    Profile (tableSignature H Info Choice) :=
  Profile.update policy who
    (Profile.update (sig := localTableSignature (Choice who)) (policy who) info law)

/-- Counterfactual utility from an information fiber is the sum of actual
continuation values, with reach taken from the common current profile. -/
def counterfactualValue (reachPolicy continuationPolicy : Profile (tableSignature H Info Choice))
    (who : ι) (info : Info who) (horizon : ℕ) : ℚ :=
  (G.histories.map fun history =>
    if G.info who history = info then
      G.counterfactualReach reachPolicy who history *
        G.value continuationPolicy (horizon - G.depth who info) history who
    else 0).sum

/-- The instantaneous regret of an actual local pure commitment. The baseline
is evaluated by the same full-game continuation function, not a supplied oracle. -/
def instantaneousRegret (policy : Profile (tableSignature H Info Choice))
    (who : ι) (info : Info who) (horizon : ℕ) (a : Choice who info) : ℚ :=
  G.counterfactualValue policy (commit policy who info (pointMass a)) who info horizon -
    G.counterfactualValue policy policy who info horizon

/-- Assemble the one shared profile from all local tables. Outside genuine
decision sites, use the specified total legal fallback without consulting regret. -/
def profile (fallback : (who : ι) → (info : Info who) → Choice who info)
    (state : Profile (tableSignature H Info Choice)) :
    Profile (tableSignature H Info Choice) :=
  fun who info => if G.decision who info then matchProb (fallback who info) (state who info)
    else pointMass (fallback who info)

/-- Simultaneous vanilla CFR in exact average-regret coordinates. Each local
update reads the identical previous-round snapshot; no updates leak within a round. -/
def state (fallback : (who : ι) → (info : Info who) → Choice who info)
    (horizon : ℕ) : ℕ → Profile (tableSignature H Info Choice)
  | 0 => fun _ _ _ => 0
  | round + 1 =>
      let previous := state fallback horizon round
      let current := G.profile fallback previous
      fun who info a => if G.decision who info then
        averageRegretUpdate round (previous who info a)
          (G.instantaneousRegret current who info horizon a)
      else 0

/-- The unique generated full-game play sequence. -/
def play (fallback : (who : ι) → (info : Info who) → Choice who info)
    (horizon round : ℕ) : Profile (tableSignature H Info Choice) :=
  G.profile fallback (G.state fallback horizon round)

/-- Deterministically select the first enumerated representative of this
information state. Perfect recall, proved downstream, makes the reach independent
of that representative; impossible observations have weight zero. -/
def informationReach (policy : Profile (tableSignature H Info Choice))
    (who : ι) (info : Info who) : ℚ :=
  match G.histories.find? (fun history => decide (G.info who history = info)) with
  | none => 0
  | some history => G.ownReach policy who history

/-- The output uses exactly completed rounds 0 through T-1 and each player's
own reach. At T=0 or zero accumulated own reach, the total fallback is returned. -/
def average (fallback : (who : ι) → (info : Info who) → Choice who info)
    (horizon rounds : ℕ) : Profile (tableSignature H Info Choice) :=
  fun who info => weightedPolicy (fallback who info)
    (fun round : Fin rounds => G.informationReach (G.play fallback horizon round.val) who info)
    (fun round : Fin rounds => G.play fallback horizon round.val who info)

/-- Evaluate the generated output at the root with the same absolute horizon. -/
def outputValue (fallback : (who : ι) → (info : Info who) → Choice who info)
    (horizon rounds : ℕ) (who : ι) : ℚ :=
  G.value (G.average fallback horizon rounds) horizon G.initial who

end HistoryTable

end GameTheory.ReBeL.Rational
