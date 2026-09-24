# M06 bounded reference transport, including disappearing queries

## Source boundary

Continue SEARCH-ERROR and SAFE-THEOREM3 (main section 5.1, main Theorem 3,
supplement G pp.21-22) without assuming arbitrary fresh solvers preserve
reference conditionals. The printed/corrected theorem distinction remains in
M06-fresh-chain.md. This is an intermediate envelope, not full M06 acceptance.

## Computed conditional cost

FinDist.conditionalTransportDefect uses the existing finite-support laws.
For an OLD-supported query it is the L1 distance of OLD/NEW conditional atom
probabilities when NEW also supports the query, and one when NEW loses it.
OLD-unsupported queries cost zero because the contract never queries them.
No NEW fallback conditional is consulted on a disappearing query.
The cost is derived in [0,2], needs no fixed positive atom-mass floor and is
zero under supported conditional equality. For bounded |v| <= B and
nonnegative NEW quality allowance e, the proof transfers NEW quality to OLD:

    E_OLD[v | q] <= e + B * conditionalTransportDefect(OLD,NEW,q).

This is a deterministic real-valued law calculation, not an executable
floating-point distance routine or a neural approximation guarantee.

## Actual resolver consumer

cfrDReferenceTransportDefect maximizes the query cost over the existing finite
parent family and all legal-history representatives, including counterfactual
queries. cfrDFreshCoherentResolver_envelope_with_transport proves the envelope

    childLoss + measuredValueDrift + 2 * payoffBound * referenceTransport.

It requires bounded payoffs, perfect recall and the NEW child's ordinary
local-quality contract. It requires neither full reference equality, an
information density, support inclusion nor equality with the unknown
opponent's actual posterior. The original coherent private-plan execution
and the arbitrary fixed unknown behavioral opponent are unchanged.
Information-local reweighting is proved to make the transport term zero;
it does not make continuation-value drift zero.

The canonical actual two-solve hidden-type chain supplies NEW local quality
and reference preservation from its solver theorems; its instantiated envelope
is not fed a desired final safety certificate. General later carried-PBS
solves must still supply their actual quality and control the computed defect.

## Hostile controls and validation

Controls retain the correlated unequal-law exact case, then add hidden flips
(cost two), disappearing queries (cost one), OLD-absent queries (cost zero),
a negative test against discarding transport, a bounded-observable transfer,
and the actual two-solve chain. No previous positive or negative control is removed.
The three edited modules are already in all registered build/lint/axiom consumers;
all 126 M06 targets and 88 supplemental modules remain. No audit is weakened.
This source checkpoint is PENDING exact-SHA compiler, lint and axiom validation.
Its predecessor 44a98bb4395db046e1ed602d8dc8fcb8f80df00d is retained separately
on rebel/m06-reference-reweight-20260924 to preserve its ongoing CI.

## Remaining work

The uniform maximum can be large. This proof is not a useful vanishing-rate
bound by itself. State-law-weighted transport, source-level drift/first-exit
rates and CarriedResolveStepBounds for repeated independent solves remain.
The finite-T term and positive numerical error remain in existing parent bounds.
All four M06 parent rows stay pending; every accepted M05 result is preserved.
