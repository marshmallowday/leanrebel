# Native query costs and payoff-diameter safety

Parent: f51ac5a306943bcaf4203a2b5e564b3f3f307d76.
This is a dependency candidate pending new-SHA Actions, not Theorem3 completion.
The accepted grouped batch is recorded in M06-grouped-security-f51ac5a-accepted.md.

## Remaining-work ordering and batch boundary

Repository STATUS, ROADMAP M06/R5 and the owner ledger leave three related
implementation groups: actual recursive cost/rate analysis; internal
chance-rooted versus fresh-original computation correspondence (including
posterior, protocol-indexed noise, fallback, allocation and clock); and
integration/source acceptance of SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3.
Do cost analysis first where it does not need an unproved solver identity,
then discharge representation/coherence conditions before attempting the
global small-rate induction and source acceptance. This is dependency order,
not a commitment to one commit per short lemma or per file.

The current batch implements interval mathematics, exact native no-query
behavior, actual query visits, full-chain signed safety, finite noisy parent
integration, cap selection, concrete consumers and independent tests together.
The boundary is mathematical: rare query mass gives a useful small cost,
but query rarity does not follow from larger search T, nor establish
representation equivalence or unknown-opponent conditional calibration.

## Derivation

FinDistRangeError proves a signed event bound of
(upper-lower)*actual-event-probability, first for scalar values and then
kernel expectations. A common payoff translation cancels. A separate
lower<=upper premise is unnecessary when both endpoints bound the payoff
on a probability law; no symmetric absolute bound is substituted for width.

pbsRecursiveQueryEvent is precisely live execution fuel AND a present saved
PBS. It includes actual hidden histories outside that PBS's support.
For missing PBSs the actual resolver returns the carried incumbent; for
stopped stages cfrDCutValue_stopped equates the old stage+late value to the
retained late value. pbsRecursiveReplacement_inactive therefore proves
zero exact native signed replacement loss, without a Nash or support premise.

pbsRecursiveReplacement_le_queryMass applies the interval bound to OLD
selected-tail versus NEW actual replacement outcome. Their values are equal
off the query event. It directly covers every active query, including the
sampling exception. It does not discard the old support penalty from a
different estimate or assume that off-support mass is small.

pbsRecursiveQueryVisits uses existing FinDist.sequenceEventMass with
carriedMemoryStep and pbsRecursiveConfigStage. It is an expected count,
possibly greater than one, not a union/first-hit probability. No average
comparison kernel advances the future law. The exact retained profile and
its saved MODEL posterior remain correlated throughout stage and late tail.

List induction bounds carriedSignedSequenceLoss by payoff width times this
actual query count. Initial-security inheritance feeds cfrDRecursiveQuery_security,
where the actual sampled finite noisy parent supplies the initial guarantee.
No positive stage tolerance, alignment or stage-noise contract is needed for
this diameter bound: it uses legality and interval bounds, not solver quality.
The finite parent retains its existing contracts and its independent
Cerror*error+Cfinite/sqrt(t)+2*loss.

cfrDRecursiveQuery_capped_security takes the smaller COMPLETE-CHAIN charge
from this new bound and the existing aligned grouped guarantee. Both concern
the identical native runner, private Fin t seed and parent trace. The grouped
branch keeps root/opponent/support terms. The diameter branch covers all
actual queries independently; it is not an identification of those terms
with zero. This is a min of whole-chain bounds, not an unproved sum of local
minima.

## Concrete consumers and tests

Hidden-type examples use the actual bias1/8 finite parent, childloss1/4,
bound2 and payoff interval[-2,2]. One consumes the capped result with
parentcut1/fresh[1,1]/stage1/late1. The other consumes the query result with
parentcut2/fresh[1]/stage1/late0. Both total horizons are3. A zero-fuel
example has arbitrary actual saved state and positive late2; an empty
schedule has zero query count.

Five new Fraction controls cover27 rare/asymmetric/translated interval
cases, missing/stopped/zero-fuel with positive late values, unsupported
queries that cannot be deleted,9 native joint forward schedules with
history/private-draw correlation, and both branches of the global min cap.
They retain independent parent finite-T and child-loss terms. Counterchecks
show visits can exceed1, a late redraw changes value, and more search
iterations alone need not reduce query mass. These controls are independent
finite mathematics, not executions of the Lean CFR implementation.

## Precommit static type review

Exact dependency signatures were read for FinDist expect_sub/expect_mono/
expect_smul/expect_bind, interval-event expectation, native selected-late
expectation, cfrDCutValue_stopped, runBehavioralFrom_add, the actual recursive
resolver's none branch and config stage, native signed loss/sequence and
initial-security inheritance, and finite-parent/grouped security.

- The interval kernel lemma initially grouped A/B under one Type* binder.
  Before committing, this was replaced by explicit independent universes u/v
  so native memory states need not share the history carrier's universe.
  This precommit correction avoids relying on universe unification.
- Generic fullInformation uses all6 explicit universes. Memory K retains an
  independent universe. No PublicBelief.condition or changed publicTrace
  signal carrier is introduced.
- The query event reads the existing history-indexed Option PBS. Its
  presence is checked without constructing a PBS or equating differently
  indexed beliefs. The same M/E/fallback/config are used in every consumer.
- StageLive/stageStopped refer to the unexpanded stage.fuel before the
  selected-late if is consumed. No partial reduction of the Decidable
  witness is used to rewrite the branch.
- Missing belief resolves to carriedMemoryProfile at the actual memory.
  The stopped proof explicitly uses fullInformation M to combine
  stage+remaining via runBehavioralFrom_add; it does not reset the late draw.
- Signed comparisons are OLD minus NEW throughout; lower/upper argument
  order was checked against sub_le_sub and the two kernel expectation bounds.
- Native sequence induction keeps the complete bound state law and recomputes
  late suffix fuel. The payoff interval constrains final history values, not
  individual actions or rewards at unrelated horizons.
- Initial security uses the same Fin t plays and remaining=config total fuel,
  including finalFuel. Concrete consumers retain full History/Choice/InfoState
  instances and both total-horizon3 computations. The zero-fuel consumer
  explicitly supplies the model, config, state and payoff to avoid reverse
  model inference.
- All14 new public names were checked against the complete accepted axiom
  inventories. Public declarations and local instances have documentation.
  New Lean lines fit100 columns and existing source transport patterns have
  no match after comment removal. Existing targets are retained.

These are static checks, not Lean compilation, Python execution or an audit
run. Actual verification occurs only in GitHub Actions. The new surface is
190 build targets,152 targeted/292 global modules and230 Python tests.
All new math declarations receive targeted lint/axiom audit; the global
ReBeL surface also reaches them transitively.

Existing solver definitions, accepted source pins, workflow triggers,
heartbeat limits and audit standards are unchanged. The audit registration
only adds modules. Historical coverage.json retains blob
2fc8cc9ad6607d61bfe397707fb96ac322fbb800. The previous owner ledger is copied
by its exact original blob to M06-kernel-value-transport-coverage-at-f51ac5a.json.

## Completion limits

This is a payoff-diameter/actual-query bound, not a proof of a vanishing
solver-specific rate in T. It gives zero extra cost for inactive calls and
a small allowance when actual query visits are rare. Actual queries may
occur at every stage even at exact Nash. Rooted/original solver identity,
useful conditional calibration/opponent/support rates, and the full source
obligations remain open. No new paper obligation is promoted.
