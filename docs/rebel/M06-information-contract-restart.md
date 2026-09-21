# M06 information-set backend contract restart

The actual remote source at restart is
30f7dfd33c05a78a70e1a29cb2734cde1af90a02, present on both
rebel/m06-information-child-20260921 and rebel/m06-information-repair-20260921.
The new working branch rebel/m06-information-contract-20260921 starts at that
exact commit. It inherits the reverse local-history decoder and original-PBS
CFR transfer; do not replay earlier chat patches or reset to b0564668.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. No force updates,
history rewriting or main integration are performed at this restart.

## Observed source and validation

Full ReBeL run 35557803196/job 106204753163 failed the line-width gate before
compilation. The exact source archive is artifact 10620459195, SHA256
1b85e369b451932027780df8ac279fb49ce849bf643bff6012cc8e8f03ae6074.
Its source marker is 30f7dfd33c05a78a70e1a29cb2734cde1af90a02.
Inspection finds one 101-column line in PBSRootLocalHistory.lean at line 151.
Repair authored source rather than weakening this or any other existing gate.
The full CI failure and uninspected supplemental result are not accepted.

## Next dependency-closed work

First restore the inherited backend's validation. Then connect the computed
information-set CFR output to the parent's type-conditioned child contracts,
deriving a finite budget from the actual PBS type masses when needed. Keep
its error separate from prediction and outer finite-T errors. Preserve
independently re-solved recursive play and source correspondence as explicit
obligations until actually constructed; neither a one-PBS Nash theorem nor
coherent redraw from a fixed family alone proves them.

All GitHub reads and writes use the connector. Offline processing of its
source artifacts is permitted, without local Git or remote repository access.
This record is a restart checkpoint, not M06 or proof acceptance.
