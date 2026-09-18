# M05 checkpoint — values, existence and geometry

## Preserved starting point

M05 starts from main and rebel/m04 at
`8c7e273aae25e3bec21028c9bda6c8c3fcf680c1`.
The exact main-source full CI run `35383025159` and ReBeL run
`35383025100` succeeded. Work continues on `rebel/m05`; main is not an
unvalidated development branch. GitHub reads and writes use the GitHub
plugin, with non-force ref updates and unchanged dependency pins.

All 50 files recursively under `docs/rebel` at that source have been read,
including the complete decoded `inventory/official.json.gz`, all paper rows,
coverage items and overrides, historical compiler logs and recovery notes.
The source snapshot came from existing artifact `10563178018` of run
`35383025100`, through the GitHub plugin. ZIP SHA-256:
`96d23309273bd84c00b08a4d87e9d1c9429a07422e693e8a53eff659aa04902d`.
Source tar SHA-256:
`6c0c81357d0a335722777e90aca0104a0adc5d44a2083ac80db89471919e01e9`.
Offline inspection of this snapshot is not a direct GitHub connection.

The repository is public and Actions may be used for validation. Historical
private-repository Actions restrictions do not apply to M05. Do not put
personal information, credentials or conversation transcripts in this repo.

## Required dependency-closed slices

1. Construct finite PBS-rooted equilibrium existence using canonical game
   forms, legal strategies, finite plans, mixed realization and unilateral
   deviation preservation. M04 value uniqueness for two supplied equilibria
   is not an existence theorem.
2. Define Eq. (1) type best-response values with fixed compatible conditional
   history laws. Prove legal simultaneous pasting of typewise responses,
   including own-zero-probability types; derive Lemma 1 rather than assuming
   its desired linearity in a certificate.
3. Connect minimax/attainment, the characterization of optimal opponents and
   concavity on the admissible own-belief simplex (Lemma 2). Do not replace a
   correlated joint PBS with an arbitrary product of marginals.
4. Prove simplex support and the centered value-vector identity. Separate a
   corrected concave extension from Appendix F's radial normalization, which
   does not in general preserve concavity or global supporting inequalities.
   Finish a real game-level counterexample and positive/boundary/nonsmooth
   controls. Convex combinations of supergradients need nonnegative weights
   summing to one; arbitrary linear combinations are not justified.
5. Inspect exact-SHA compilation, normal/slow lint, architecture, transitive
   axioms and source-inventory results. Update coverage/status with the
   original/corrected/refuted statements kept distinct, then integrate only
   validated source. No M05 obligation is promoted at this checkpoint.

## Source interpretation under review

Main p5 Eq. (1), Eq. (2), Theorem 1 and footnote 8; supplement F pp19–20,
Lemmas 1–2, Figure 3 and Eq. (3)–(12), are the controlling locators.
The existing rational R3 diagnostic is retained, not relabeled as a complete
counterexample to every interpretation of the original main theorem.

A candidate repair extends the homogeneous minimum of affine opponent
branches by an affine mass correction anchored at the base value. Its
centered support may agree with Eq. (2) on the simplex without asserting
that the normalized extension in Appendix F is globally concave. Actual
Lean proofs, canonical game connections and semantic review are still required.

After interruption, read the actual branch head and its CI results before
continuing; do not infer completion from this plan. This checkpoint does not
establish browser monitoring, automatic resubmission, or M05 completion.
