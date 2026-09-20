# M06 exact-driver finite-time safety and controls

Implementation checkpoint on rebel/m06-exact-driver-20260920, following
c09549c9dc9d98cf933da0798d035701a72f5af3. Exact-source validation is pending.

CFRDExactSafety instantiates the constructed continuation's accuracy and
leaf-optimality in the actual outer CFR-D Nash and carried-security theorems.
No child Nash or continuation-quality certificate is an argument. The finite
outer iteration term B/sqrt(T) remains when both numerical and child loss are
zero. A comparison equilibrium only names the original game's value; it is
not a supplied child solve. The construction is still exact, noncomputable
child Nash and not finite-T recursive child CFR or arbitrary re-solving.

Six Examples/CFRDExactDriver controls instantiate a genuine live second round:
actual-driver accuracy, all-round leaf optimality, finite-T Nash, off-path
unilateral continuation equality, zero remaining fuel, and a negative proof
that restoring a trunk does not generally preserve whole-profile equality.

The inherited exact-child audit failed at 7166f79d AFTER all declared targets
compiled: unannotated counters were inferred as MessageData. Annotating both
counters as Nat fixes the audit generator without relaxing any allowed axiom,
lint or nonempty-module check. The supplemental audited slice is extended
from five to nine modules. Full repository and full ReBeL gates remain.
At c09549c9 the new clamp module used the reserved identifier prefix; rename
that binder to prefixLaw without changing its type or any theorem conclusion.

Original coverage parents remain pending. Compile and inspect the new exact
source and adversarial controls before promoting even this restricted slice.
