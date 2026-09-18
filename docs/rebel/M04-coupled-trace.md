# M04 coupled-trace development checkpoint

## Inspected root-decomposition validation

Source commit 1a8e5b6e5e8db19cd87b2779604c4384ee10feec passed ReBeL run
35307099820, job 105481483330. The actual log was read: 39 proof modules,
1442 declarations in the transitive axiom audit (only propext, Classical.choice,
Quot.sound), 1443 declarations in complete normal/slow lint, 37 Python tests,
static architecture and tracked-file cleanliness all passed. Build completed
1549 jobs. This includes scheduled_root_gain and fullGame_root_decomposition,
which derive actual whole-policy root gain rather than taking it as input.
Validation artifact 10532249587 has ZIP SHA-256
 e6499244277d5735f9a8d3a9b44bfe409c6a1d05d9a61e3d8bc7e07aacfe345.
The separate full-CI run 35307099839 must still be inspected.

## Current unaccepted source slice

RegretMatching supplies a real positive-regret rule with an explicit legal
fallback at zero positive mass. CFRTrace builds one simultaneous whole-game
profile sequence: all local tables read the same previous-round snapshot.
Round zero has no observations and uses the specified fallback, not a warm
start. Local realization, average-vector equality and cumulative-regret
identities are tied to that actual shared play sequence.

This source needs its own compiler, lint and axiom results. Its conditional
norm-bound theorem is not the final finite-game CFR guarantee: derive uniform
canonical payoff bounds from game payoffs and finite information fibers, then
connect all deviations through scheduled_root_gain. Own-reach averages,
independent private seeds, canonical Nash, executable rational refinement and
independent best-response tests also remain open. No coverage row is promoted.
All remote operations use the GitHub plugin. Every new module is imported by
the analytic root and included in the recursive proof consumer.
