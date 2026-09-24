# M06 same-reference drift composition — accepted checkpoint

Proof source: `639e3962a2db297fb3f767459d7269769a7ea0d5`, preserved on
`rebel/m06-fresh-drift-20260924`. Initial evidence commit:
`7cffdd88fcc0f925fd29a46ca465023899c2abd2`. These descend from review
`a5e0700f18ddd19e768c0967d29f1802276ecb55`. Main is unchanged.

## Exact-source evidence

M06 run 35962837942 / job 107514893323: SUCCESS, including all declared
targets and the entire supplemental proof-slice audit. Artifact 10793590654
was retrieved through the GitHub plugin and its full m06-targeted.log inspected.
The log identifies this exact SHA and Lean 4.33.1 and records:

    EXACT_LEAF_MODULE_AXIOM_PASS ...CFRDFreshValueDrift: declarations=17
    EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1251
    EXACT_LEAF_VALIDATION_PASS modules=84

Each module's configured Batteries linter run passed. The axiom auditor covers
public, private and generated declarations transitively, allowing only propext,
Classical.choice and Quot.sound. No skipped audit or build step is counted.
The pinned runner selects slow checks through getChecks(slow := true); there
was no separately invoked defLemma command. The earlier prose's count92 and
separate-defLemma-run claims are not the actual 84-entry source or invocation.

Full CI 35962837872 / job 107515074899: SUCCESS, including the complete public
build/lint, architecture audits, inventory/reuse signatures and tracked cleanliness.
Independent ReBeL 35962837863 / job 107514896065: NOW CONFIRMED SUCCESS,
including all-ReBeL compilation/lint/transitive axioms, rational runtime and
independent pure-response checks, static gates and tracked-file cleanliness.
Inventory 35962837864 / job 107514892300 and source snapshot job107514896183
also succeeded. Earlier pending entries describe earlier inspections only.

## Accepted declarations and boundary

CFRDFreshValueDrift now includes:

- cfrDFreshValueChange_add_of_referenceLaw;
- cfrDFreshValueDrift_le_add_of_referenceLaw;
- cfrDFreshUniformDrift_le_add_of_referenceLaw.

These are the previously unapplied composition draft, now source-validated.
All use equality of the full old reference law, not merely observed marginals.
They preserve live-query support and zero-factual-reach cases. They do not
infer small type-wise drift from scalar Nash accuracy.

The successor CFRDFreshChain derives reference preservation from an actual
finite recomputed child sequence and connects it to a noisy-parent root bound.
Its separate source, compiler loop and CI are recorded in
M06-fresh-chain-validation.md; do not transfer this SHA's success to a successor.

## Preserved recursive predecessor

Recursive source a42467929bbedb0f26bd100e5915d5743ec9025d remains preserved.
Independent ReBeL 35954274920 / job107489146886 succeeded at
2026-09-24T04:46:13Z. The separately downloaded all-ReBeL log ends with
REBEL_VALIDATION_PASS modules=231. This is a DIFFERENT consumer from the
84-module supplemental audit, not a competing expected module count.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
A common-reference composition lemma alone does not derive useful fresh-solve,
support or first-exit rates, or later independent carried-PBS safety. Preserve
all accepted M05 evidence and the printed/corrected Theorem3 distinction.
