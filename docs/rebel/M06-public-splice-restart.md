# M06 public-splice restart

Work branch: `rebel/m06-public-splice-20260920`.
Parent: `8ab23b4bb20349df616736d9b5c6d980f3e7eb41`.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`, accepted through M05.
No old branch is reset and no existing proof is replayed.

## Inherited exact-source validation now inspected

At 8ab23b4bb20349df616736d9b5c6d980f3e7eb41:

- Full build/lint/architecture CI: run 35483264757, job 106004834984, success.
- ReBeL compiler, normal/slow lint and transitive axioms: run 35483264754,
  job 106004831910, success. The actual artifact log ends with
  `REBEL_VALIDATION_PASS modules=148` and contains
  `REBEL_AXIOM_AUDIT_PASS declarations=3262`.
- Inventory: run 35483264769, job 106004796170, success.

The old proof-source run 35482474752 at 482ebe19 ultimately reports cancelled;
it must not be relabeled successful. The later documentation source above has
its own complete successful validation and the inherited Lean implementations.

Downloaded through the GitHub connector:

- Source artifact 10596311843, ZIP SHA-256
  02512809798552d2a355d603ac383c9a43433bba1f312d1eb2a0d3773fd0ce6d.
- Validation artifact 10596208591, ZIP SHA-256
  a582441aff812d78e5aad575a022a3bd594b1a01db8750a6ae33e2f49ab59532.

## Next dependency-closed construction

Construct a legal public-state-indexed continuation using full AOH prefixes,
prove that all legal descendants select the original cut's public state, and
use this construction to discharge the local-response agreement premise in
CFRDCompletedContract. Do not use the latest public observation as a substitute
for the public history at the cut. Test different public roots, later signals,
and private histories that share a public root.

This closes a splicing obligation, not the entire recursive query-game or
finite-T child-quality construction. Those remain M06 work. Existing source
identities, negative tests, dependency pins and audit gates remain unchanged.
