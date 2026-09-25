# M06 conditional-value stability checkpoint

## Pinned starting point (2026-09-25)

This work continues `rebel/m06-scalar-checkpoint-20260925` at
`d2cb889b5538bc9429eb47a7a7e32309d0e31bb7`, not the older M05 default branch.
GitHub Actions run `36113477739` at that exact SHA completed successfully:
`build` (`108001998661`), `rebel` (`108001998664`), and
`whitespace-lint` (`108001998651`). The ReBeL job includes the compile,
regression, coverage, and required transitive axiom-audit gates.

## Dependency-closed slice

The existing same-PBS scalar comparison does not control conditional value
vectors. The next slice will compare conditional payoffs at one fixed
`TypeBeliefSlice`, under the explicit condition that the two behavioral
profiles agree on all opposing coordinates. It will use the existing
remembered-type best-response attainment and approximate Nash bounds.

The planned interfaces retain the probability-weighted bound at every type,
and divide only at supported types. An absent type's fixed kernel is NOT a
zero payoff: zero own probability only masks its contribution to the root
inequality. Solver-facing specializations must obtain approximate Nash from
actual information-set CFR output, not a caller-supplied value inequality.

## Remaining obligations

M06 remains incomplete. This restricted comparison neither proves opposing
profiles agree for independently recomputed solves nor supplies general
native/late conditional calibration, value-vector convergence, or the final
carried-prefix safety/equilibrium theorem. These obligations must not be
replaced with scalar root-value convergence. This first checkpoint contains
only scope and verified parent evidence; new Lean declarations have not yet
been committed or validated.
