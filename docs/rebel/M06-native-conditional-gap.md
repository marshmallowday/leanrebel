# M06 native conditional-gap slice

## Checkpoint and source boundary

Branch: `rebel/m06-native-conditional-gap-20260925`.
Parent evidence checkpoint: `e80f65d731b6beff1caa0f1d67cee9b4e41d87a8`.
Parent proof: `5cf1369cf1e886650a90a4e027347dacf589d50b`.
Preserve the query-gap review and validation records. Parent targeted success
is not a compiler result for these new declarations. Main is not advanced.

This is a project-level M06 refinement of random-iteration continuation and
conditional-error interfaces. It does not close the original paper rows
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR or SAFE-THEOREM3.

## Mathematical statement

Fix one canonical TypeBeliefSlice, its own-type law, and the actual finite
information-set CFR recurrence at that joint PBS. Let average be its computed
own-reach averaged profile and draw a uniform private index n from the SAME
pre-update iterations. Hold every opposing coordinate at average throughout
the comparison. For type x define

    g_n(x) = Eq1(average_opponents, x) - payoff(iterate_n_own, average_opponents, x).

Every g_n(x) is nonnegative because Eq1 optimizes over every legal behavioral
own policy. On a supported type, the actual complete-history sampling theorem
and preservation of the root prefix imply E_n[payoff_n(x)] = payoff_average(x).
The compatible slice kernel at x is supported inside the model mixture; that
support inclusion is proved from the FinDist bind, not assumed of every root.
It follows that

    E_n[|g_n(x)|] = |Eq1(average_opponents, x) - payoff_average(x)|.

This is an equality of mean ABSOLUTE gaps, not an unjustified exchange of
absolute value and expectation. The proof uses the sign of every gap.
The preliminary conditional-payoff identity permits arbitrary fixed opponents
and arbitrary execution fuel, independently of the training horizon.

Actual CFR Nash then gives E_own E_n[|g_n|] <= pbsRootCFRBound at the real
positive iteration count. A query law exactly dominated by own with density
at most C has E_query E_n[|g_n|] <= C * pbsRootCFRBound. The existing budget
round computation gives the requested positive root-error bound without an
input Nash certificate or a minimum own-type mass.

## Quantifiers and limitations

The draw is private, uniform, made once and retained through continuation.
It is NOT a last iterate, a coordinate average, a shared own/opponent index,
a freshly selected index at each move, or a new independent solve. The
opponent in g_n is the fixed computed average, not the n-th opposing iterate.
The root conditional kernels and correlated joint PBS do not change.

No per-iterate small-gap claim, uniform-in-type error, off-support sampling
identity or equality of actual and model posterior is inferred. The mean
bound weights absent types by zero; their compatible kernels are retained.
The optional query-density cap remains an explicit source-law condition.
No hidden history or private seed is passed to an opposing policy.
The finite-T residual is not multiplied by a zero oracle error or discarded.

## Compiled controls required for acceptance

The live HiddenTypes child uses the actual full-AOH slice and legal-history
carrier. At T=2 it instantiates conditional payoff preservation against
arbitrary fixed opponents for every supported own type. The budget-1/8
example instantiates the mean absolute gap of actual native iteration draws,
with the exact budget-computed positive count.

The adversarial canonical finite zero-sum type game has exact root Nash for
every sampled opposing action. Its centered conditional value has signed
mean zero but mean absolute value 1/2. This refutes extending the argument by
mere signed cancellation when opponents change. That negative family uses
the uniform index law but is NOT claimed to be solver-generated CFR iterates.
Earlier rare/absent-type, independent/shared-seed and finite-T controls remain
unchanged in the imported proof surface.

## Validation and next work

The new proof and control module are appended to the analytic umbrella and
existing M06 target list. The unchanged global ReBeL auditor discovers both
for compilation, configured lint and transitive axiom collection. The existing
100-module exact-leaf auditor is left unchanged and therefore does NOT by itself
certify the new modules. Their global audit results must be inspected separately.
No old target, negative control, axiom allowance, dependency pin or verification
option is removed.
Lean compilation, configured normal/slow lint and transitive axiom output are
PENDING this source's GitHub Actions at the implementation checkpoint.

Remaining: native/late independently changing-opponent or changing-PBS value
rates, actual carried-PBS support/first-exit control, quantitative query-density
conditions for those changing laws, independent recursive re-solving safety
and CarriedResolveStepBounds. M06 and Theorem 3 remain incomplete. This slice
uses no learner-convergence premise to substitute for test-time safety.
