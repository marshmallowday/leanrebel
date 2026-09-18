# M04 schedule audit repair

## Observed failure and exact correction

The already-completed ReBeL run 35297361329 at source
8602bb10305da4163370b2258b9a579d05e9f715 failed before Lean at
TRANSPORT_REBEL_SOURCE: expected 58, got 61. The source-level metric and
its fixed budget are preserved. No audit configuration is changed.

The three additional occurrences were unnecessary goal-presentation steps:

1. Schedule.scheduledSites_covers now applies lt_of_eq_of_lt directly to
   clock.correct and the strict horizon bound.
2. Examples/Schedule.drawSite discharges the definitionally false terminal
   premise directly. HiddenTypes.terminal at State.first is False.
3. Examples/Schedule.drawSite_depth is the clock.correct theorem itself:
   the selected history has definitionally one transition.

No theorem statement, premise, schedule, game rule, numerical bound, public
import, linter selection or axiom allowlist changes. The replacements do not
move an equality cast to a different module or substitute a new transport
primitive. They directly reuse existing facts and definitional reduction.
Source comparison removes exactly three counted tokens and adds none, so the
previously observed metric predicts 58 again. This prediction is not an
executed Phase 2 or compiler result for the new commit.

## Validation boundary

Before the local runtime failed, all 37 existing Python regressions passed
on the retrieved 8602bb1 source. They do not validate this later proof edit.
Subsequent container and Python calls, including a plain echo with no network
or Git operation, returned TransportTimeoutError. GitHub plugin read/write
calls still succeed. No new Lean compilation, lint, or axiom audit is claimed.
The existing pinned compiler/dependency artifacts were retrieved through the
plugin but have not been assembled into a working compiler in this execution.

GitHub Actions execution remains prohibited by the user. All checkpoint
messages include [skip ci]. The new source must undergo the non-Actions
compiler and complete audit when an executable environment is available;
M04 and all of its currently pending coverage obligations remain open.
