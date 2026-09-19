/-
# ReBeL finite-game, information, and public-belief semantics

Opt-in public root. M03 adds the scoped PBS correspondence; it does not complete CFR, learning, or
implementation refinement. Milestone evidence and remaining obligations live
in docs/rebel. The basic GameTheory root intentionally does not import this.
-/

import GameTheory.ReBeL.Information
import GameTheory.ReBeL.Knowledge
import GameTheory.ReBeL.Finite
import GameTheory.ReBeL.Adapter
import GameTheory.ReBeL.Payoff
import GameTheory.ReBeL.Response
import GameTheory.ReBeL.FiniteSites
import GameTheory.ReBeL.Examples.FiniteSites
import GameTheory.ReBeL.Examples.HiddenTypes
import GameTheory.ReBeL.Examples.HiddenTypesHistories
import GameTheory.ReBeL.Examples.HiddenTypesPayoff
import GameTheory.ReBeL.Examples.LiarsDice
import GameTheory.ReBeL.Examples.LiarsDiceInformation
import GameTheory.ReBeL.Examples.LiarsDicePayoff
import GameTheory.ReBeL.Examples.ModifiedRPS
import GameTheory.ReBeL.Examples.ObservedDice
import GameTheory.ReBeL.Examples.CommonKnowledge

import GameTheory.ReBeL.ReachWeights
import GameTheory.ReBeL.Belief
import GameTheory.ReBeL.BeliefExecution
import GameTheory.ReBeL.PolicyDomain
import GameTheory.ReBeL.Prescription
import GameTheory.ReBeL.StrategicEquivalence
import GameTheory.ReBeL.ReachFactorization
import GameTheory.ReBeL.CompactBelief
import GameTheory.ReBeL.BeliefStatistic
import GameTheory.ReBeL.PublicSubgame
import GameTheory.ReBeL.Examples.PublicBelief
import GameTheory.ReBeL.Examples.CompactCards
import GameTheory.ReBeL.Examples.BeliefSearch
import GameTheory.ReBeL.Examples.BayesObservation

import GameTheory.ReBeL.Schedule
import GameTheory.ReBeL.Examples.Schedule
import GameTheory.ReBeL.Rational.Algorithm
import GameTheory.ReBeL.Rational.FullGame
import GameTheory.ReBeL.Rational.HiddenTypes
import GameTheory.ReBeL.Frontier
