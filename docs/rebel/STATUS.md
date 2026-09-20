# ReBeL status — M06 in progress; M05 accepted

## Active M06 restart point

Continue on `rebel/m06-recovery`, not the older `rebel/m06` head. The new proof
source is `ef5b781639ffa7180d87805061c0781eb725c6ac`; read the actual remote ref
because the target-registration/evidence commits and later repairs may follow.
Main was last checked at `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`, retaining
accepted M00-M05 work. No M06 integration or milestone acceptance is claimed.

The inherited equilibrium-replacement control at `883f3329` passed its target,
full repository CI, inventory and ReBeL compiler/lint/axiom job. The subsequent
`75e37c12` delayed-child-sampling source had real compiler errors. The repair
`b717496c` passed targeted run `35476164384`, job `105985660828`.

## New saved M06 progress and observed validation

- `50953465ef67233f96217bfca353e8074bff0d06`: the constructed child resolver and
  same-iteration value-oracle adapter passed target run `35476596169`, job
  `105986817394`. Parent backup and actual private child draws now share one
  table from the actual learned trunk, with no extra local replacement loss.
- `538c0866` added carried-model-belief projection and live two-child controls.
  Its target compiler step passed; its full architecture gate correctly
  rejected a `change` tactic. `dfd2d861` repaired this by definitional
  simplification without changing any frozen audit count.
- `78107e72819214d73d81238c09d4423d922dad76`: all preceding modules plus generic
  zero-own-reach completion passed target run `35477330791`, job `105988756019`.
  Completion preserves actual play against arbitrary fixed opponents, all
  unilateral deviation laws, and the ordinary Nash predicate.
- `0414e326` adds canonical zero-own versus zero-joint reach controls, and
  `ef5b7816` constructs an optimal focal completion from finite conditional
  best-response plans. Their newest exact-source target and full checks must
  still be read. Earlier target success is not validation of these additions.

Read [M06-child-oracle.md](M06-child-oracle.md),
[M06-child-controls.md](M06-child-controls.md),
[M06-zero-reach-completion.md](M06-zero-reach-completion.md),
[M06-zero-reach-controls.md](M06-zero-reach-controls.md), and
[M06-zero-reach-optimality.md](M06-zero-reach-optimality.md).
Existing full document-review records are preserved; incremental recovery
review is not mislabeled as a new complete rereading of every source file.

## Remaining M06 proof boundary

The child table is constructed from the parent query and sampled consistently;
this is not yet a fresh recursive solve at every realized carried PBS. The
zero-own-reach best-response construction is focal against fixed opponents.
Connect supported-type Nash optimality, joint off-path completion, recursively
computed child tables, and the resulting child continuation bounds. Do not
infer any of these merely from on-policy law equality or ordinary Nash.

`CFRDResolverLocal` remains an explicit sufficient premise for arbitrary
replacement, not a consequence of arbitrary equilibrium selection. The new
constructed-table adapter does not need it. Numerical oracle error, child
continuation loss, optional generic replacement loss and finite-T error remain
distinct. Keep the printed and corrected Theorem 3 statements separate. M06
coverage is not promoted by these intermediate proofs; complete exact-source
compiler/lint/architecture/runtime/axiom checks remain mandatory.

## Accepted M05 proof source and historical integration gate

M05's finite-game ROADMAP deliverable is complete with the explicit source
qualifications and refutations in [M05.md](M05.md). The accepted proof source is
`b1b557b7e3c9471e5f774c7fc400c1665742a614`. Its unchanged Lean proof is also
validated in the documentation/test checkpoint
`20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b`.

| Exact source | Gate | Run | Result |
|---|---|---|---|
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | ReBeL compiler/lint/axioms | 35411381522 | success |
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | Full repository CI | 35411381563 | success |
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | Source inventory | 35411652870 | success |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | ReBeL compiler/lint/axioms | 35412423210 | success |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | Full repository CI | 35412423211 | success |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | Source inventory | 35412423259 | success |

The historical acceptance/evidence commit was required to pass the same three
workflows before main was advanced. Main now contains that accepted M05 work.
Read actual `main` and work-branch refs and exact-SHA CI after an interruption.
Do not replay accepted proofs, force-update branches, or resume from the old
failed `18d11b3` source.

## What M05 establishes

The canonical public-belief game has a behavioral Nash equilibrium, and every
equilibrium has the same scalar value. Infostate values are attained best
responses over all legal behavioral own deviations. Root-type memory pastes
all conditional optimizers into one legal information-local policy, proving
the fixed-opponent linear branch identity, including own-zero-probability types.

The value equals the attained minimum over all legal behavioral opponents;
exactly the minimizing opponents occur in equilibria. This yields concavity
on the own-belief simplex. The canonical full-AOH theorem constructs its PBS
slice and equilibrium from the original protocol and the entire joint law,
not from a separately assumed payoff matrix or an assumed value theorem.
The two-stage hidden-type example preserves arbitrary joint laws and exposes
correlation that equal marginals cannot distinguish.

Theorem 1's adopted existential-extension reading is proved using
`F_p(w) = H(w) + H(p) * (1 - sum w)`. This concave extension agrees with the
value on the entire simplex and has the centered infostate vector as a global
supporting vector at p for every equilibrium opponent there. It depends on
base p; no single universal extension independent of p is claimed. Actual
canonical conditional values are also connected to the normalization Jacobian
and fixed-branch Frechet derivative, without differentiating a nonsmooth value.

## Source qualifications that must remain visible

The domain is finite legal histories/actions, finite remaining fuel, perfect
recall/clock (constructed by full AOH), two players and real zero-sum utilities.
The focal player is labelled zero. Own beliefs vary with compatible conditional
joint-history kernels fixed; this is not arbitrary independent marginal
reweighting. Zero-mass conditional laws use explicit compatible completions
and are not uniquely inferred from the present PBS.

The supplement's degree-zero radial extension is not the corrected F_p.
Canonical game examples refute its global support, concavity and the claim
that radial constancy implies constancy normal to the simplex. Footnote 8's
arbitrary linear-combination assertion is also refuted; convex combinations
are proved instead. Boundary, nonsmooth and nonunique-equilibrium controls
remain in the compiled proof surface. These qualifications close source
obligations honestly; they are not silent replacements of the original claims.

## Evidence and ledger

[M05-validation.md](M05-validation.md) gives exact runs, artifacts, log hashes,
105 compiled and normal/slow-linted modules, and 2,543 transitive declaration
axiom checks. Only `propext`, `Classical.choice`, `Quot.sound` are permitted.
[M05-accepted-axioms.txt](M05-accepted-axioms.txt) retains every journal anchor's
complete axiom list as an explicit excerpt of the actual successful run.
No proof, dependency, axiom allowance or verification gate was weakened.

The active `coverage-updates/M05.json` accounts for all 43 original M05 rows:
8 verified, 30 qualified and 5 refuted; no M05 row remains pending. Original
source identities and M00-M04 evidence are preserved. The expanded ledger has
3,054 rows: 64 verified, 41 qualified, 5 refuted, 406 context indexed,
one empirical runtime record and 2,537 pending. These row counts are not a
percentage-complete measure of the entire mathematical formalization.

M04's accepted implementation `ee8fdf1d63af8c592d1d2ee4949df385a6341a4f`
and integrated main checkpoint `8c7e273aae25e3bec21028c9bda6c8c3fcf680c1`
remain ancestors, with their evidence in [M04.md](M04.md). The independent
rational solver control still reports NashConv 2, 2, 1 for T=0, 1, 2 after
checking all 1,024 pure policies per player; it is not an exact T=2 equilibrium.

## Remaining milestones

M06 continues from the accepted canonical PBS/value/infostate interfaces and
M04 CFR solver, with its current work and limitations recorded above. Theorems
2/3, unrestricted learned-leaf search safety, solver variants, neural training
and C++/floating-point correspondence are not established by M05 or by the
conditional M06 resolver checkpoints. The complete framework remains M06-M11
work. Do not mark inherited official C++ occurrences or other downstream
obligations verified merely because the finite-game value theorems are accepted.
