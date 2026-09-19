# M06 checkpoint: source review and implementation start

## Exact restart point

- Base/main: `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.
- Work branch: `rebel/m06`, created from that exact commit.
- Inspected successful base runs: full CI `35429754886`, ReBeL compiler/lint/
  transitive axioms `35429754725`, source inventory `35429754744`.
- The source snapshot was obtained through the GitHub connector, artifact
  `10579997566` from run `35429754725`, not a local GitHub connection.
  ZIP SHA256: `aa3ac0227aa200f904400426f2f48ae488778278c73ffd5e3cc0170250a477f9`.
  Tracked-source TAR SHA256:
  `bfbea9f7d24f82dc1b6282406887137b8db5d8edb2c6747be8eb823e8bfe63a2`.

## Complete baseline document review

All 63 files recursively under `docs/rebel` at the base commit were read.
This includes every historical M01-M05 checkpoint, compiler log, acceptance
and recovery record; README, ROADMAP and STATUS; the complete coverage JSON;
the coverage-updates README and M05 journal; sources/reuse JSON; all paper TSV
rows; NOTICE, the complete official license and tree manifest; and the entire
DECOMPRESSED official JSON inventory. Large structured files were rendered
losslessly in chunks, retaining every key, value and row. Reading that index
does not assert that every original C++/Python body has been newly reviewed.
Root and ReBeL AGENTS rules were also read. Historical private-repository
Actions restrictions do not apply to this public-repository task.

## Required proof chain

M06 depends on M03 and M04. It must not assume Theorem 2, successful training,
or the final root-regret/safety result in an oracle structure field.

1. Publicly observable stopping frontiers, terminal versus cut leaves,
   canonical runner factorization and continuation values.
2. Iteration-specific joint PBS queries, an information-local continuation
   policy and its value vector, including counterfactual/off-path consistency.
3. A genuinely coupled depth-limited CFR-D update and a proved transfer of
   approximate leaf error into the full-game regret bound, with explicit
   finite-game constants and a retained finite-iteration term.
4. Private random-iteration execution and carried model beliefs; unilateral
   safety against arbitrary opponents must be distinguished from mutual
   approximate Nash and from shared-seed correlation.
5. Nontrivial canonical examples, adversarial seed/averaging controls, and an
   actual finite-T control for the printed Theorem 3 formula.
6. Full exact-source build, lint, architecture, runtime and transitive axiom
   gates; only then source-mapped coverage/STATUS acceptance and integration.

The original printed `delta*C1 + delta*C2/sqrt(T)` and the candidate corrected
`A_d*delta + B_d/sqrt(T)` remain distinct. The M01 recurrence diagnostic is not
already a solver proof. Ordinary on-path Nash values alone are not a substitute
for the required counterfactual continuation contract.

## Compiler feedback

The read-only M06 compiler-export workflow supplies the pinned compiler,
package artifacts and compiled existing ReBeL dependencies through GitHub
Actions artifacts for offline proof iteration. Its export is deliberately
restricted to compiler/package/build paths, excludes Git directories, and
contains no credentials or home-directory snapshot. The existing complete
acceptance workflows remain authoritative and unchanged.

This checkpoint completes the document review, NOT M06. No coverage row is
promoted here. Continue implementation on `rebel/m06`; inspect that branch's
latest commit and CI before resuming. All repository writes and ref updates
must use the GitHub connector and must not force-push.
