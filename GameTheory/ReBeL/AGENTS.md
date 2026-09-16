# ReBeL implementation rules

This directory is reserved for the full ReBeL formalization in the fork
`marshmallowday/GameTheory`. Read root AGENTS.md, docs/rebel/README.md,
docs/rebel/STATUS.md, docs/rebel/ROADMAP.md, and docs/rebel/coverage.json first.
This file does not establish a Lean library or any proved ReBeL declaration.

## Scope and continuity

- Write, push, create PRs, and update issues only in marshmallowday/GameTheory.
  Read upstream sources without mutating them. Never open an upstream PR.
- Preserve unrelated changes. Use fork-local `rebel/<task-id>` branches for
  implementation. Do not force-push, rewrite history, or upgrade dependencies
  as an incidental repair. Re-read branch heads before integration.
- Implement one dependency-closed, testable slice. Update coverage and STATUS
  with the change. The next chat must be able to resume from repository state,
  not from an assertion in a previous assistant answer.
- The final scope includes all paper theorems, appendices, algorithm variants,
  learning networks and updates, numerical execution, and game/evaluation
  definitions. An oracle-only result is an intermediate result.

## Semantics

Reuse canonical Protocol execution, histories, information-local policies,
FinDist, utilities, deviations, and Nash predicates. Namespace new declarations
under GameTheory.ReBeL. Use narrow imports and preserve upstream dependency
boundaries. Do not add a parallel game/probability/equilibrium stack.

Do not identify an arbitrary InfoState with a full action-observation history,
a private Bayes posterior with a public belief state, or a tuple of marginals
with a general joint law. Make support, compatibility, recall, positive mass,
termination, and finiteness premises explicit where they are used. Preserve
zero-probability and off-path cases instead of dividing by zero silently.

A supplied root-regret decomposition is a proof obligation, not a completed
CFR implementation. An example-level learner is not a generic solver. Distinguish
reach-weighted averaging from coordinate averaging and private iteration seeds
from shared randomization. Maintain separate definitions for algorithm variants.

## Proof and implementation trust

- No sorry/admit/custom axioms in committed ReBeL Lean modules, including tests.
  Do not conceal them using warning options, generated declarations, unchecked
  imports, `implemented_by`, or a conclusion assumed in a structure field.
- Open obligations belong in the ledger or a draft specification, not in fake
  completed theorems. Conditional results are allowed only with clearly named
  premises and an explicit remaining obligation to discharge them.
- Audit transitive axiom dependencies. For the strict proof surface allow only
  `propext`, `Classical.choice`, and `Quot.sound`. Native evaluation or compiler-
  trust axioms are not silently accepted as kernel-only evidence. Inspect the
  actual pinned Lean version; a grep check is not an axiom audit.
- Do not weaken a theorem, remove an adversarial test, hide a module from the
  build, or change expected audit counts merely to make CI green.
- Preserve original statements separately from corrected or restricted ones.
  Record an actual counterexample as a counterexample, not an eternal TODO.
- Keep abstract real-valued specifications and executable finite/numeric
  implementations distinct, connected by refinement theorems. Differential
  testing is useful evidence but does not prove program equivalence.
- A formal optimizer update is not a proof that a neural network meets an
  approximation contract. GPU/runtime/FFI assumptions must remain visible.

## Validation and reporting

Every accepted slice needs source locators, exact declarations and assumptions,
a nontrivial positive example, an appropriate negative/boundary example, a
successful target-SHA build, transitive axiom output, and semantic review.
Run the narrowest real Lake target first. At dependency or milestone gates,
run the full build, lint, and applicable architecture audits. Include new
modules in lint and axiom-audit consumers; do not change the upstream basic
root into a heavyweight ReBeL import.

Use available local Lean tools or fork GitHub Actions. GitHub file editing is
not compilation. If execution, workflow enablement, or permissions are missing,
state the precise blocker; do not claim tests passed and do not accumulate a
large unverified implementation on main. For a pending CI run record its SHA,
run/job ID, and next check. No background monitoring is implied.

The coverage checker validates ledger structure only. Mark an item `verified`
only after compiler and semantic evidence have actually been inspected.
