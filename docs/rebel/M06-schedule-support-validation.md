# Finite-schedule support compiler loop

## Original candidate: failed, not accepted

Source `370384f660a3c57e8f08e98bcf40e3f7528020bb`, target run 36283825513,
job 108520661241. The complete job log and downloaded artifact 10920246119
show compilation FAILURE, completed at 2026-09-27T00:58:34Z. Earlier job-summary
queries still displayed in-progress; those observations do not override the
finished compiler output. Normal/slow lint and axiom validation did not run.

Artifact ZIP SHA-256:
`51cb9bc1455d21cc66188c7758f8afed5d49f0955f51f902ea5acb4b2564a739`.
Complete `m06-targeted.log` SHA-256:
`2a97144f47583661b7d71b84f833cdc168f621c19e6d5acdf0b64504fdea98d5`.
The log identifies exactly 370384 and Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

There is one source diagnostic: PBSCarriedSupport.lean:90:10, an additive
monotonicity proof term has the wrong summand nesting. No other source
compiler errors are reported, but this does not accept the failed module.
The failed core blob is `8cb33a008f87e6a357ba8520cf66d0fcf4123275`.

## Focused repair

The repair changes ONLY that proof term to
`add_le_add le_rfl (add_le_add nextBound le_rfl)`. This matches the actual
nested sums directly, with the initial mass and tail charge unchanged.
No definition, theorem statement, assumption, control, import, audit target,
dependency pin, workflow or gate is weakened. The repaired core blob is
`18ed758848b0bd84933f50c4fae2e6be85bd5902`; source SHA-256 is
`cfff3e862b894634652640ebe4cde89376e6a9f957b8febf8a0c4418ea5edddb`.

The repair continues the latest checkpoint b0e1cb58a4f4371c977c9a38e5b786666cda24f7
on `rebel/m06-schedule-support-review-20260927`, retaining its seven arithmetic
fixtures and completed inherited 3dfa global evidence. The failed original
source branch remains preserved. The repaired source needs its OWN target
compiler, normal/slow lint and complete transitive-axiom inspection. At this
repair commit all those gates are pending; no baseline pass validates it.
M06 remains incomplete and the four original paper obligations stay pending.
