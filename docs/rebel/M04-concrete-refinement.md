# M04 concrete runtime refinement checkpoint

## Verified recovery anchor

`89a816b1b0c178f77bd939e4d1c4364f65093c4a` passed the complete ReBeL
validation workflow `35357180618` (diagnostics job `105639276386`).
This includes the unchanged static architecture gate, all 46 Python regressions,
actual Lean rational solver execution/independent exhaustive-response checks,
all ReBeL builds, transitive axiom audit and normal/slow lint, and tracked-file
cleanliness. Separate full-library CI is not asserted successful by this result.

The verified proof surface includes the general rational solver refinement,
its canonical approximate-Nash theorem under primitive table certificates,
and the concrete legal-history and active-information/menu codecs.
The executable raw Row/Site instance still requires its own commuting diagram;
this document does not conflate the general theorem with a discharged concrete
instance of all its premises.

## New slice under validation

The source `fb04e70bf76c9d46c3c768d8a97094a5d872132e` exposed errors in
record syntax, a proof-local instance style and payoff conversion, not a failure
of the game assumptions. This checkpoint repairs those errors without changing
any theorem statement or weakening an audit. It also adds:

- `Examples/RationalChance`: exact primitive sparse chance-row correspondence,
  including the private uniform draw and both simultaneous strategic stages.
- `Examples/RationalExecution`: equality of the actual numeric continuation
  evaluator with the original behavioral runner at every legal history/fuel.

Both modules use the existing history and local-menu codecs. They do not assume
a continuation value, regret bound, CFR trace or equilibrium result. Their own
compiler/lint/axiom results must be inspected before marking this slice verified.
Remaining work includes concrete reach and information-fiber summation,
local commitments and regret matching across the menu equivalence, iteration
and own-reach average correspondence, and final source-pinned acceptance.

M04 remains open. Original ledger obligations and accepted M03 evidence are kept.
