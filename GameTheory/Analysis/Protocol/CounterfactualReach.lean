/-
# Counterfactual reach for protocol analyses

The canonical behavioral reach definitions and their probability proofs live
at the Protocol layer, where they can also serve public-belief semantics
without importing Analysis. This analysis entry point re-exports that single
implementation; no duplicate definitions, aliases, or proof assumptions are
introduced. Counterfactual regret and equilibrium analyses remain downstream.
-/

import GameTheory.Protocol.BehavioralReach
