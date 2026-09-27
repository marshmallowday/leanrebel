# Recursive root training output: integration batch

Parent 107bbaa5d7017e0dc92a85acfab73b90ac81618d on
rebel/m06-kernel-value-repair-20260927 was re-read and passed all four Actions.
Its root-memory repair loop is closed. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098; the chat baseline is
9457c198126f3c8b7cb1045bbed2e0053788636f. The existing branch retains the complete
M06 solver and evidence history, so this batch continues it without replacing
other work or committing to main.

## Coherent implementation boundary

The previous target implementation used the finite-child parent directly.
The arbitrary-depth solver instead uses cfrDComposedOracle and a recursively
computed child at every shorter cut schedule. Installing only the old target
would evaluate a different learning trace.

PBSComposedValueTarget now uses that composed oracle in the backup, exact
cut comparator, decoded original-game comparator and support theorem. It
retains the actual same-round child and prediction. Its uniform mean theorem
does not require child Nash as an input: numerical propagation compares the
same continuation that was actually used.

PBSRecursiveValueTarget supplies the computed finite round count, allocated
node error, actual target trace and proof-only original trace for every finite
schedule. A nonempty schedule uses the same recursive tail solver, actual PBS,
noise allowance, child tolerance and count as pbsRecursiveDepth. The empty
schedule returns the current conditional payoff without a child query.
pbsRecursiveTrainingOutput pairs the existing average policy with the backed-up
root information-value vector. pbsRecursiveTrainingOutput_correct establishes
both the all-deviation finite-budget policy guarantee and numerical accuracy
of that vector using the existing structural induction and the new bridge.
It does not alter pbsRecursiveDepth or execute the proof-side comparator.

Three dependency stages are committed together: composed root semantics,
arbitrary-depth algorithm integration, then actual hidden-type examples and
four exact-rational controls. This avoids a workflow wait between each stage.
Separating the remaining fresh re-solving security problem is justified by its
different proof obligation: old/new signed comparison under an unknown opponent,
rather than the same modeled continuation used for training.

## Review and tests

The same-root correlated PBS is conditioned on own AOH. Absent coordinates
remain total fallback values, not observed samples; composed support matches
the incoming own-type law. The training consumer must use that support.
The administrative draw contributes one extra rooted step, while original
cut and remaining fuel both remain in the comparator. Different child budgets
do not reweight the uniform parent mean. Neither latest-root substitution,
last-child reuse nor independent joint-policy averaging is valid.

The hidden-type Lean controls instantiate three recursive levels, positive
allocated noise, a zero-width initial cut, policy identity and empty schedule.
Four Fraction tests cover nine rare-root/schedule combinations at all three
nodes and three rounds, wrong child-round/tail omissions, unequal child
iteration counts, and absorbing terminal/empty schedules.

Expected new validation: 163 build targets, 125 targeted and 267 global audit
modules, 185 Python tests. The previous 160/122/264/181 surface is preserved.
All three new Lean modules are imported and included in build and full targeted
lint/axiom audit. Workflows and audit criteria are unchanged. These expected
counts are not claimed as executed results; new source awaits exact-SHA Actions.

## Source acceptance and remaining M06

Unchanged 107bbaa source supports P-CFRD-TARGET in the append-only root-target
journal. Its review and complete validation are separate from this new source.
P-CFRD-AVERAGE, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
A finite-budget average-policy guarantee and vector arithmetic alone are not
treated as acceptance of the fixed-trace asymptotic source claim.

This batch does not derive small signed costs for independent recursive
re-solving, equate model and factual unknown-opponent posteriors, or infer
kernel/policy closeness from Nash accuracy. Original R5 and corrected/restricted
statements remain separate; finite-T, child tolerance and noise are retained.
No network convergence or Nash information-value-vector convergence is assumed.
