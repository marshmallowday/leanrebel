# Schedule support: preserve the finite-law representation boundary

Source e1e5a37e26a6d01d2c1cb209d28ca583cfc42054 repaired the original additive
proof-term error, but its GLOBAL run 36284378049 / job 108522217037 failed the
static architecture step before Lean setup. The complete downloaded artifact
10920495339 records TRANSPORT_ANALYSIS_SOURCE=1 and
REPRESENTATION_TOKENS_OUTSIDE_OWNERS=1. Both frozen expected values are zero.
ZIP SHA-256: `0d52410298a0a0d5210ae8be166eb4343942970a8a9518b73f6da043db485577`.
Library line-width checks passed; compiler/lint/axiom/runtime steps were skipped.
The independent e1 target 36284378051 / job 108522217075 had no inspected final
result at this correction, and cannot establish a global pass in any case.

The nil branch of the new visit-count proof used `change` and reached into
`ENNReal.toReal_nonneg`. The first violates the analysis transport budget and
the second crosses the public FinDist representation boundary. The repair uses
only `sequenceEventMass`, the new charge definition, and the existing public
`expect_indicator_eq_probOf`, `expect_const` and `expect_mono` API. Nonnegativity
is proved by pointwise nonnegativity of the indicator, with no representation
unfolding. This is a substantive abstraction repair, not a token rename or a
relaxation of the static gate.

New core blob: `ff5bf151d7e8bb146c02a5eeb1749972a77e42a9`.
New source SHA-256: `4a5dc6324a9436f5e8e5a73cbbb17be7b4dbfd0d46883af99d6a4c5532b88aa0`.
The focused additive repair remains intact. Every definition, theorem statement,
parameter, assumption, control, fixture, import and audit target is unchanged.
No workflow, gate script, expected count, allowlist or dependency pin is edited.
Local lexical checks of the revised module find no transport or representation
tokens and no overlong lines; the actual unchanged global gate must still run.

This correction descends from e1 on rebel/m06-schedule-support-review-20260927,
preserving b0e's controls and all inherited accepted evidence. Its own exact
source target compilation, normal/slow lint and transitive-axiom review are
pending. M06 remains incomplete; the original four paper obligations remain
pending. See M06-schedule-support-validation.md for the first compiler failure.
