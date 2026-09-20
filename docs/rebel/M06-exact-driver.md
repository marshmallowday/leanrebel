# M06 constructed exact driver: implementation and coverage boundary

Source modules: CFRDClamp and CFRDExactDriver. Parent source:
7166f79de7f14ade853d5d7f96a6e2adf7e07018. This checkpoint is not accepted
until its exact-source compiler, lint, architecture and axiom outputs are read.

The driver restores the current CFR-D trunk before executing a continuation.
Joint zero-own-reach completion can alter unreachable decisions before that
cut, so equality of whole profiles is not an appropriate identification.
CFRDClamp derives equality of every conditional deviation law at cut roots,
and preserves the unchanged loss allowance under an equal unilateral prefix
reference. Actual supported live roots have the exact cut depth; stopped
histories are excluded by the live flag, not by assuming away early termination.

CFRDExactDriver constructs its response from the queried trunk's factual child
Nash games and compatible counterfactual completion. It computes numerical
conditional values from that same continuation. Its accuracy theorem and
leaf-optimality theorem apply to every round of the actual cfrDState recurrence.
They have no caller-supplied Nash, posterior equality, response policy or
continuation-quality inequality. The child construction still uses exact
noncomputable finite Nash existence, not a finite-T approximate child algorithm.

Coverage journal (no acceptance promotion):
- SEARCH-FRONTIER: cut-depth/early-terminal distinction used by clamp; pending.
- SEARCH-CFRD: constructed continuation connected to actual driver; pending.
- SEARCH-ERROR: no extra loss from trunk restoration; pending.
- SAFE-THEOREM3: exact-driver end-to-end security and approximate recursive
  child execution still require their own proofs and source review; pending.

The original source identities and all earlier evidence are unchanged. No
placeholder, new axiom, suppressed warning, removed test or weakened gate is
introduced. This is incremental source review, not a new claim that every
historical inventory file has been reread in this session.
