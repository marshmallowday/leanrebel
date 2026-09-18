# M04 concrete solver-to-Nash checkpoint

At `25c99c8106b138459f1c5a9a3643bb27128caed7`, ReBeL run `35362826282`,
job `105658013295` compiled the complete concrete history, information, menu,
chance, payoff, continuation, reach, information-fiber, local-commitment and
instantaneous-regret correspondence. Both generic menu-reindexing lemmas also
compiled. All 46 Python tests and the actual Lean rational-runtime cross-check
passed. The concrete iteration module stopped on three definition-reduction
goals at inactive/zero coordinates. This checkpoint repairs those goals using
explicit coordinate identities, without weakening any statement or audit.

The new concrete averaged-output module connects the generated trace to the
canonical private own-reach average, including its zero-mass fallback. Its
`solve_isNash` has only a positive iteration count as an input: the full-AOH
game, legal history enumeration, local menus, chance transitions, payoffs,
perfect recall and all intermediate correspondences are supplied by the case.
The conclusion uses the original canonical Nash predicate, quantifying over
all complete behavioral deviations, and `solve_value_correct` connects the
numeric root evaluator to that same semantic strategy. `solve_zero` states the
empty-average fallback separately, without a fictitious probability law on Fin 0.

These final additions require compiler, transitive-axiom and normal/slow-lint
validation on their own source SHA. M04 is NOT accepted by this checkpoint.
The last fully passing ReBeL source remains `89a816b1b0c178f77bd939e4d1c4364f65093c4a`
until a newer complete audit succeeds. Its separate full-library CI was later
cancelled by a newer push, so that result must not be described as full CI success.
No main update, original-ledger promotion or change to accepted M03 evidence
has been made. The final remaining work is exact-SHA validation, semantic
acceptance review, evidence/coverage updates and verified integration.
