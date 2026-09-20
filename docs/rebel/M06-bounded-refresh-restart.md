# M06 bounded-refresh restart

Work branch: `rebel/m06-bounded-refresh-20260921`.
Base: `a39599e3b47b1e50ca78d5a6385aa24035d25738`, which contains proof source
`f4671e429e7a221999e661f862e15f38d2ade700`. The old d6db5e46 inference error
has already been repaired. Do not replay that patch or any older recovery.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

The base's full repository CI `35518435920` / `106098224758`, ReBeL
compiler/lint/axiom run `35518435948` / `106098224868`, and source inventory
`35518435989` / `106098225132` all completed successfully. The downloaded
ReBeL log ends `REBEL_VALIDATION_PASS modules=173`.
Source ZIP SHA256: `602b707694ec4d70c79824a6f4661710d02cf80b4a292d1851fd629540e8e058`.
Validation ZIP SHA256: `089162ce171f8e6d11e07ee657d255c0192dcefdd752943cde9c51bd2ef7a492`.
These results validate the inherited base, not subsequent changes.

## Next dependency-closed construction

Connect fresh finite-budget solves at the actual carried model PBS to the
existing recursive execution. Use an explicitly named bounded-refresh variant:
a private mixture switches to the freshly solved profile with probability r
and otherwise retains the current complete profile. Prove the step law through
retained memory and Bayesian state updates, then derive replacement loss at
most 2*B*r from bounded terminal utility. Sum those derived allowances through
the finite schedule; do not assume CarriedResolveStepBounds or any final
recursive safety inequality. Missing model beliefs retain the old profile;
terminal and zero-fuel stages retain the existing no-query rule.

This deliberately permits an explicit replacement penalty and does NOT claim
that arbitrary independent equilibrium replacement is lossless. Preserve the
existing counterexamples. The normal-form finite child remains a distinct
adaptive real-arithmetic reference, not the paper's information-set CFR.
The paper-specific recursive bound and M06 original source obligations remain
open until their actual constructions and source correspondence are verified.

Coverage journal: this work targets the remaining recursive-execution part of
SEARCH-CFRD and explicit replacement-loss accounting in SEARCH-ERROR and
SAFE-THEOREM3. No original coverage row is promoted by this restart record.
All proof changes require exact-SHA compilation, normal/slow lint and transitive
axiom inspection, with unchanged dependency pins, trust allowlist and gates.
