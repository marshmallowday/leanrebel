# M06 actual child-iteration sampling construction

Inherited checkpoint: af6f600727b0c50906155c54f23a26e7529426fd.
The first source slice is c4fee1dbb01520be898fce5a888c6edcf6a43228.
This document describes compiler candidates until exact-source CI is recorded.

## Source correspondence and scope

ROADMAP M06 requires random-iteration play, carried beliefs, a fixed unknown
opponent and values consistent with the continuation policy. The inherited
information-set child computes an own-reach averaged behavioral policy.
The new slice exposes the ACTUAL information-set CFR iterates underlying
that average, rather than pre-drawn deterministic plans or an independently
selected equilibrium. This directly advances the child policy/value family
and delayed-sampling bridge; it is not complete recursive re-solving safety.

PBSInformationSampling constructs pbsRootCFRIterate and its original full-AOH
decoder. Its native and original unilateral law theorems hold against any
fixed behavioral opponents and retain full original histories. The root law
is the supplied joint public belief. One administrative chance step is kept
separate from both the training horizon and the executed continuation fuel.
The private uniform index ranges over completed rounds 0 through T-1.
It is retained for the whole continuation, not reselected at each action.

CFRDInformationSampling selects the same positive posterior-dependent count
used by pbsInformationConditionalProfile. It connects that private iteration
draw to cfrDInformationChildTable and to the actual public-prefix-spliced
cfrDInformationChildProfile. All history observables then have equal values.
The seven controls in Examples/PBSInformationSampling cover uniform T=2,
nonempty posterior-dependent counts, a live posterior, randomized opponents,
zero fuel, the actual parent splice at positive child loss and value equality.

## Boundaries retained

These law identities do not assert an individual-iterate Nash guarantee,
shared-index two-player equivalence, per-action resampling equivalence or
lossless replacement by an arbitrary new equilibrium. A single player's draw
must stay private, with its opponents outside that random index.

The posterior in the law is the supplied MODEL joint posterior. The result
does not yet extend sampling to an arbitrary reweighted/off-model root law or
to all counterfactual type-conditioned roots. Existing zero-own-reach response
completion remains essential. The finite child count is posterior-dependent,
not a common fixed T across all possible beliefs, and the real-valued solver
is not an executable numerical refinement.

The remaining bridge must transport this actual iteration family through the
parent's counterfactual/type-conditioned values and independent recursive
carried-PBS execution, without assuming the desired law or no-loss property.
Original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending. No old coverage hash, theorem statement, dependency or audit gate
is changed. The umbrella, target list and supplemental lint/axiom consumer
only gain the three new modules.
