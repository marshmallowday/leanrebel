# M06 first-exit controls checkpoint

Parent theory source: `6be7364c11f49cb194f75af44e3e9e31bb06487e`.
Branch: `rebel/m06-first-exit-20260924`.

The existing Examples/PBSCarriedDepthSampling module now checks:

- the pre-existing hidden-type executeCarriedResolves runner inherits the computed
  first-exit charge for two distinct finite iteration counts, with positive child
  tolerance and prediction noise unchanged;
- a late event retains the correct native state and the suffix including the
  exceptional stage, excluding the already executed safe prefix;
- native/comparison kernels have the same complete witness law even though their
  complete two-stage executions differ;
- repeated stage labels retain the first occurrence and its full suffix;
- an absent event returns none, not a fabricated stopping state;
- the signed suffix discrepancy is -2 in the hostile Boolean control;
- a future that erases the discrepancy has zero refined charge despite hit
  probability one, strictly improving the old uniform allowance;
- a 1/4-3/4 initial mixture gives hit probability 1/4 and computed charge 1/2.

All prior controls are preserved. These tests supplement, not replace, the source
requirements. The Boolean controls concern probability accounting and do not
refute or establish the paper's game-theoretic safety theorem. No learning or
convergence-rate assumption is inferred from the new computed charge.

This commit is a validation candidate. Inspect its exact-SHA M06 target,
normal/slow lint, transitive axiom, full CI, inventory and ReBeL jobs before
accepting it. No heartbeat, dependency pin, gate or theorem premise was weakened.
