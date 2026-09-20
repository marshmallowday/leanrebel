# M06 finite-child integration and variant scope

Work branch: rebel/m06-finite-child-20260920. This is an implementation
checkpoint until exact-source compiler, normal/slow lint and axiom outputs
are inspected. Existing global workflow gates are retained without relaxation.

The finite-plan recurrence selects no Nash witness. For one factual joint
posterior with minimum positive atom m and requested child loss L>0, it computes
a finite positive horizon meeting root error epsilon=m*L. The full joint solve
uses one common horizon, not incompatible per-type policies. Supported type
mass p satisfies m<=p. Thus the proved approximate-Nash gap gives conditional
loss <=epsilon/p<=L. No positive floor is assumed uniformly over all learned PBSs.

CFRDFiniteChild computes those finite children at the actual trunk's live
public posteriors, then uses the existing legal public-prefix splice and trunk
clamp. Full outcome and all unilateral-deviation laws, not just played means,
transfer the finite solver's approximate Nash. CFRDFiniteContinuation uses
the actual reconstructed reference type mixture and derives the factual
probability budget. The existing finite conditional best-response construction
handles omitted types at zero own reach. No exact equilibrium is chosen for
any child and no leaf-value inequality is supplied as data.

CFRDFiniteDriver consumes this finite continuation in its own coupled outer
recurrence. Numerical noise may change subsequent trunks. Its proved target
is carried selected-policy security with A*error+B/sqrt(T)+2*L. A network error
bound remains an explicit numerical premise; finite child quality does not.
The comparison equilibrium names only the original-game reference value.
Seven HiddenTypes controls use a live cut and positive child tolerance, and
include a prediction bias 1/8 distinct from child tolerance 1/4.

This adaptive NORMAL-FORM reference is not the paper's information-set child
CFR, and real arithmetic makes it a mathematical algorithm rather than an
executable rational or floating-point refinement. Tiny posterior atoms can
require enormous horizons. Zero child loss is outside the finite positive-
budget guarantee. Fresh recursive re-solving at later carried PBSs is not
certified by preserving a single complete policy or by arbitrary Nash selection.

Coverage journal: SEARCH-CFRD gains constructed finite factual children and
all-query off-path completion in the actual outer driver. SEARCH-ERROR gains
a derived finite-child loss distinct from numerical and outer regret terms.
SAFE-THEOREM3 gains this explicitly named adaptive reference variant only.
All four original M06 parent rows remain pending; no original source claim,
negative control, dependency pin or verification gate is removed or weakened.
