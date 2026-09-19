# M05 validation checkpoints

## Validated repaired implementation

Source: `44cd2d674b5b94713407c450a8bfd0d6f6a0e191`.

- ReBeL run [35410325950](https://github.com/marshmallowday/leanrebel/actions/runs/35410325950),
  diagnostic job `105808567589`: all required steps **success**, tracked files clean.
- Full CI run [35410325967](https://github.com/marshmallowday/leanrebel/actions/runs/35410325967),
  job `105808562997`: build, compiler-resolved inventory, Phase 1/2/3 architecture
  checks, deep reachability probes, complete public-library lint and cleanliness
  **success**.
- Saved ReBeL log SHA-256:
  `013fce26d9aaa47454ceb1fde339ff9a966f45e3cd9007a0f8bf64017127797a`.
- Compiler emitted `REBEL_AXIOM_AUDIT_PASS declarations=2541` and
  `REBEL_VALIDATION_PASS modules=105`. Build and explicit normal/slow lint
  surfaces each contain the same 105 modules.
- The permitted transitive kernel axioms remain exactly `propext`,
  `Classical.choice`, `Quot.sound`. No `sorryAx` or new allowance was added.

The original failed `18d11b3` run stopped on the missing documentation string
for the local `valueHistoryFintype` instance. The correction does not change
its type, any proof, any theorem statement or any dependency.

`M05-compiler-log.txt` preserves selected complete lines of the successful
44cd2d6 log. It is explicitly an excerpt, not a replacement for the full log.
The read-only transport run
[35411825818](https://github.com/marshmallowday/leanrebel/actions/runs/35411825818)
read the already-saved artifact and exposed audit text in job metadata. Its
success is NOT compiler evidence; the original source run above is authoritative.
Some longer audit entries wrap across physical lines and are not included in
the selected excerpt unless their entire dependency list was read.

## Accepted proof source

PROOF_SOURCE_ACCEPTED=b1b557b7e3c9471e5f774c7fc400c1665742a614

The additional radial-versus-normal counterexample source has now passed:

| Source | Gate | Run | Job | Observed result |
|---|---|---|---|---|
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | ReBeL compiler, normal/slow lint, axioms, runtime | 35411381522 | 105811587627 | success |
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | Full CI, architecture and library lint | 35411381563 | 105811589367 | success |
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | Source inventory | 35411652870 | see run | success |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | ReBeL compiler, normal/slow lint, axioms, runtime | 35412423210 | see run | success |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | Full repository CI | 35412423211 | see run | success |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | Source inventory | 35412423259 | see run | success |

The four commits from b1b557b to 20cbe32 modify documentation and metadata
regressions only. The proof source is identical. Cancelled duplicate runs on
another checkpoint branch are not substituted for the successful runs above.

The original b1b557b validation artifact is `10575215089`. Its complete
`rebel-validation.log` SHA-256 is
`39a814432300e9b86ae589329d23ca1c6dfe7662eac03c76115e6a8d79c533f8`.
The log identifies the exact source on its first line and contains 2,543
unique, fully read declaration axiom records. Every dependency belongs to
`propext`, `Classical.choice`, `Quot.sound`; no allowance changed. The 105
module entries match the 105 normal/slow lint starts and successful finishes.
The final markers are `REBEL_AXIOM_AUDIT_PASS declarations=2543` and
`REBEL_VALIDATION_PASS modules=105`.

[M05-accepted-axioms.txt](M05-accepted-axioms.txt) preserves the complete axiom
lists for all 31 distinct declaration anchors used by the 43 source rows.
It is explicitly an excerpt. Its regression checks detect missing anchors,
wrong source identifiers, duplicate records and forbidden dependencies;
they do not independently authenticate CI or replace kernel verification.

The 20cbe32 validation artifact is `10574842255`, with full log SHA-256
`beb526e7be4cc605149abb677ace2531955717009befcbc5487628978d31f5b0`.
Its source artifact `10573958456` contains a source tar with SHA-256
`5d6c94a43140d65206928c1f969ac902be3b34944367a5dccccb1c0a3a3f4dde`.
Both were obtained through the GitHub plugin and inspected offline. There
was no local Git or HTTP connection to GitHub. The source and compiler counts
were verified directly from these artifacts, not inferred from a green label.

## Accepted source-row dispositions and integration

`coverage-updates/M05.json` activates all 43 reviewed M05 dispositions:
8 verified, 30 qualified and 5 refuted. Every record retains the original
source identity and earlier evidence and pins the actual unchanged Lean blob.
The inactive `.candidate` file is removed in the same commit as activation,
this accepted-source marker and STATUS. The frozen `coverage.json` and the
original inventory remain byte-for-byte unchanged.

[M05.md](M05.md) supplies the semantic review and limitations. Acceptance
uses finite games and fixed compatible conditional joint-history laws,
explicit zero-mass completions and the base-dependent concave extension.
It does not promote the false radial-support/concavity assertions or arbitrary
linear combinations to verified. The official implementation obligations and
M06-M11 remain outstanding.

The accepted 20cbe32 snapshot passed all 72 offline metadata regression tests.
The acceptance commit adds four axiom-excerpt integrity tests. Offline tests
remain metadata evidence only; the Lean results above come from Actions.
The independent rational check enumerates 1,024 pure policies per player and
reports NashConv 2, 2, 1 for T=0, 1, 2. These are empirical controls, not exact
finite-T equilibrium assertions.

This document intentionally names an already validated proof source, rather
than an impossible self-referential acceptance commit SHA. Before advancing
main, verify the acceptance commit's own three normal workflows and re-read
the actual refs. Integrate only by a non-force fast-forward. The recovery
checkpoint is recorded separately in M05-final-recovery.md; old pending
statements there and in earlier logs refer to their historical source.
