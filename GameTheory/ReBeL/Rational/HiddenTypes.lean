/-
# Executable encoding of the two-stage hidden-type regression

Rows retain both simultaneous action tuples even when the physical state
merges. Decision keys retain the player's own type and own first action but
never the opponent's private type. This is a runtime table fixture; its
canonical-history decoding/refinement is a separate proof obligation.
-/

import GameTheory.ReBeL.Rational.FullGame
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype

namespace GameTheory.ReBeL.Rational.HiddenTypes

/-- The two strategic players; chance is in transition rows, not a player. -/
abbrev Player := Fin 2

/-- Full legal-history codes, including all simultaneous choices. -/
inductive Row
  | initial
  | drawn (firstType secondType : Bool)
  | second (firstType secondType firstAction secondAction : Bool)
  | finished (firstType secondType firstAction secondAction finalFirst finalSecond : Bool)
  deriving DecidableEq, Fintype

/-- Active information keys retain own-action memory. Inactive observations
are collapsed only in the runtime table, where their sole action is Unit. -/
inductive Site
  | idle
  | first (ownType : Bool)
  | second (ownType ownFirst result : Bool)
  deriving DecidableEq, Fintype

/-- Exactly one no-op at inactive rows, and two Boolean choices at active rows. -/
abbrev Choice : Site → Type
  | .idle => Unit
  | .first _ => Bool
  | .second _ _ _ => Bool

/-- The executable finite enumeration is selected by the actual local menu. -/
@[reducible]
instance choiceFintype (site : Site) : Fintype (Choice site) :=
  match site with
  | .idle => inferInstance
  | .first _ => inferInstance
  | .second _ _ _ => inferInstance

/-- Equality does not consult a physical history or another player's type. -/
@[reducible]
instance choiceDecidableEq (site : Site) : DecidableEq (Choice site) :=
  match site with
  | .idle => inferInstance
  | .first _ => inferInstance
  | .second _ _ _ => inferInstance

/-- The selected coordinate of a public code, used only while encoding observations. -/
def own (who : Player) (first second : Bool) : Bool := if who = 0 then first else second

/-- Encode precisely the observations relevant to an active local policy. -/
def information (who : Player) : Row → Site
  | .initial => .idle
  | .drawn x y => .first (own who x y)
  | .second x y a b => .second (own who x y) (own who a b) (a == b)
  | .finished _ _ _ _ _ _ => .idle

/-- The fixed explicit Boolean enumeration does not require a choice principle. -/
def bits : List Bool := [false, true]

/-- Ordered tuples used to enumerate every history, not only on-policy histories. -/
def pairs : List (Bool × Bool) := bits.flatMap fun x => bits.map fun y => (x, y)

/-- Exactly the 85 legal prefixes of chance followed by two simultaneous stages. -/
def rows : List Row :=
  [.initial] ++
  pairs.map (fun t => .drawn t.1 t.2) ++
  pairs.flatMap (fun t => pairs.map fun a => .second t.1 t.2 a.1 a.2) ++
  pairs.flatMap (fun t => pairs.flatMap fun a =>
    pairs.map fun b => .finished t.1 t.2 a.1 a.2 b.1 b.2)

/-- All ten active local decisions; own memory gives eight second-stage sites. -/
def sites : List Site :=
  bits.map Site.first ++
  bits.flatMap (fun t => bits.flatMap fun a => bits.map fun result => .second t a result)

/-- Initial chance draws four equally likely private pairs; strategic steps
are deterministic after their independently chosen joint action. -/
def children : (history : Row) → ((who : Player) → Choice (information who history)) →
    List (Row × ℚ)
  | .initial, _ => pairs.map fun t => (.drawn t.1 t.2, 1 / 4)
  | .drawn x y, draw => [(.second x y (draw 0) (draw 1), 1)]
  | .second x y a b, draw => [(.finished x y a b (draw 0) (draw 1), 1)]
  | .finished _ _ _ _ _ _, _ => []

/-- Only the completed second strategic stage is terminal. -/
def isTerminal : Row → Bool
  | .finished _ _ _ _ _ _ => true
  | _ => false

/-- A win contributes +1 and a loss -1 to player zero. -/
def winValue (won : Bool) : ℚ := if won then 1 else -1

/-- Cumulative payoff, not merely the last stage's reward. -/
def payoff (history : Row) (who : Player) : ℚ :=
  let firstPayoff := match history with
    | .initial | .drawn _ _ => 0
    | .second _ _ a b => winValue (a == b)
    | .finished _ y a b c d => winValue (a == b) + winValue ((c == y) == d)
  if who = 0 then firstPayoff else -firstPayoff

/-- A player's actual selected first-stage local coordinate. -/
def firstEntry (who : Player) (x y a b : Bool) : Sigma Choice :=
  ⟨.first (own who x y), own who a b⟩

/-- A player's actual selected second-stage coordinate, retaining its first move. -/
def secondEntry (who : Player) (x y a b c d : Bool) : Sigma Choice :=
  ⟨.second (own who x y) (own who a b) (a == b), own who c d⟩

/-- Only own strategic factors; omitted inactive factors are the unique no-op's one. -/
def ownPath (who : Player) : Row → List (Sigma Choice)
  | .initial | .drawn _ _ => []
  | .second x y a b => [firstEntry who x y a b]
  | .finished x y a b c d => [secondEntry who x y a b c d, firstEntry who x y a b]

/-- All noninitial histories have exactly one uniform private chance draw. -/
def chanceFactors : Row → List ℚ
  | .initial => []
  | _ => [1 / 4]

/-- The exact table consumed by the generic rational full-game implementation. -/
def table : HistoryTable Row (fun _ : Player => Site) (fun _ => Choice) where
  histories := rows
  initial := .initial
  info := information
  terminal := isTerminal
  children := children
  payoff := payoff
  ownPath := ownPath
  chanceFactors := chanceFactors
  decision _ site := match site with | .idle => false | _ => true
  depth _ site := match site with | .idle => 0 | .first _ => 1 | .second _ _ _ => 2

/-- The same baseline fallback as the canonical hidden-type example. -/
def fallback (who : Player) : (site : Site) → Choice site
  | .idle => ()
  | .first _ => false
  | .second ownType _ _ => if who = 0 then ownType else true

/-- Complete-round output of the generic solver on this runtime encoding. -/
def solve (rounds : ℕ) : Profile (tableSignature Row (fun _ : Player => Site) (fun _ => Choice)) :=
  table.average fallback 3 rounds

/-- Print exact integer numerator/denominator pairs at every active coordinate.
The external checker compares these against an independently written Fraction solver. -/
def printProfile (rounds : ℕ) : IO Unit := do
  let profile := solve rounds
  for who in ([0, 1] : List Player) do
    for site in sites do
      match site with
      | .idle => pure ()
      | .first ownType =>
          let zero := profile who (.first ownType) false
          let one := profile who (.first ownType) true
          IO.println s!"{rounds},{who.val},0,{ownType.toNat},0,0,{zero.num},{zero.den},{one.num},{one.den}"
      | .second ownType ownAction result =>
          let zero := profile who (.second ownType ownAction result) false
          let one := profile who (.second ownType ownAction result) true
          IO.println s!"{rounds},{who.val},1,{ownType.toNat},{ownAction.toNat},{result.toNat},{zero.num},{zero.den},{one.num},{one.den}"

end GameTheory.ReBeL.Rational.HiddenTypes
