# Canonical conditional grouping and native-chain security

## Accepted starting point and dependency order

5a4710d92c4a39c5eed565650cd96c068ee8ae21 passed all four workflows and
complete log/axiom/lint/semantic review. See
M06-recursive-security-5a4710d-accepted.md. The unused-instance repair loop
is closed. This next batch is pending its own exact-SHA verification.

The remaining work is organized by mathematical dependencies:
1. Preserve the native joint law while grouping replacement comparisons,
   so a calibrated conditional history law is compared once with its model.
2. Derive useful actual conditional-root/opponent/support rates; identify
   required internal chance-rooted and original fresh computations including
   posterior, protocol-dependent noise, fallback, budget and clock.
3. Complete recursive small-rate safety and source acceptance.

This batch implements all of group1 through the finite-parent consumer, not
just an isolated expectation lemma. The boundary with group2 is mathematical:
neither calibration under an arbitrary unknown opponent nor computational
equivalence between different protocol wrappers has been established.

## Implemented chain

PBSRecursiveGroupedValue records a group's public observation index, joint
saved PBS and full carried incumbent. The reference policy is the actual
pbsRecursiveDepth computation for the same configuration. A live cell's
compatibility consists only of data/computation identities: live status,
common incumbent, and equality of the computed fresh profile. It does not
assume a safety inequality or a child Nash certificate.

pbsRecursiveNativeGroupKey constructs these groups directly from the native
state. pbsRecursiveNativeGroupKey_compatible proves their compatibility using
supported conditional fibers. Thus the schedule does not require the caller
to supply a grouping certificate. Same incumbent/PBS computations coalesce
even if private seed identities differ, but the complete original joint
state law is retained for the subsequent native update.

pbsRecursiveGroup_loss_eq averages the actual old-minus-fresh values over
the group's history marginal before applying the actual recursive Nash
bound. Its charge is tolerance plus bound times
2*conditionalRootVariation + oldOpponentCharge + freshOpponentCharge.
pbsRecursiveGroup_calibrated_loss_le derives tolerance alone when the
conditional history marginal is the model PBS and the opponent is the
computed opposing profile. These are explicit specialization premises, not
claims about all native chains. No Nash-to-own-policy-closeness step is used.

The global charge disintegrates the actual joint state distribution with
FinDist.eq_bind_condOnFibre, retaining the actual label frequencies and the
full conditional history correlation. Absent labels are unused; their total
fallback is not an observed posterior. Uncertified cells keep their exact
signed recomputed loss. In particular, a missing query does not mean zero
cost. The all-uncertified identity is proved explicitly.

PBSRecursiveGroupedSecurity sums these derived charges plus the unchanged
2*bound*actualUnsupportedMass term. Future laws use carriedMemoryStep with
the native private draw and saved-MODEL update. They never use the comparison
average or an independently sampled posterior. The same private draw is
retained for stage plus late continuation. Aligned cuts/noise/tolerance
remain mandatory. The final theorem cfrDRecursiveGrouped_security connects
the actual sampled noisy finite-child parent, whose initial guarantee is
already derived, to this budget without additional grouping assumptions.
Cerror*error, Cfinite/sqrt(t), 2*loss and the native budget remain separate.

## Consumers and independent controls

The hidden-type examples reuse the actual noisy finite parent with bias1/8,
childloss1/4, bound2: parentcut1 plus fresh[1,1]/tol1/8/stage1/late1, and
parentcut2 plus fresh[1]/tol1/8/stage1/late0. Both original horizons are3.
They now consume the canonical grouped budget. Other examples prove automatic
key compatibility for arbitrary native laws, exact uncertified-cell accounting
and an empty schedule with positive late fuel.

Five Fraction tests independently cover:
- 27 rare/correlated calibrated groups where conditional root discrepancy is
  zero although the averaged singleton discrepancy is strictly positive;
- the failure of deleting private incumbent/history or saved-MODEL correlation;
- nonuniform actual label weights, absent labels, missing/stopped cells and a
  tight actual unsupported-mass correction;
- 81 root/model/old/unknown-opponent combinations of independent matching-pennies
  controls, retaining both opponent charges even at exact Nash;
- 9 native joint forward schedules, stopped states, empty/zero-fuel identities
  and the changed value from independent late redrawing.

These are independent finite rational controls, not actual CFR executions.
They do not supply a proof that all conditional-model or opponent rates vanish.

## Commit-before type review

Read the exact signatures of FinDist.expect_congr/expect_map/expect_bind,
eq_bind_condOnFibre/support_map/support_condOn, recursivePolicyValueChange,
pbsRecursiveDepth_replacement_le/model_replacement_le, recomputed loss identity,
recomputed budget, native signed telescope and finite parent security.
The following checks cover the dependency-to-consumer path:

- All generic fullInformation uses explicitly fix all six universes
  .{0,u,u,u,u,u}; group labels and private memory have independent universes.
  No implicit PublicBelief.condition or original/full public-index conversion
  is introduced. The group record's belief has its stored public index.
- Canonical keys take state.belief at exactly state.history's full signal
  index. Option.map computes a nondependent profile, avoiding a cast between
  observation-indexed PBS types. Its actual config fixes noise/cuts/tolerance.
  The tagged record equality is eliminated only after obtaining supported
  fiber membership; absent-fiber fallback never proves compatibility.
- Common old/fresh profiles give the expectation identity via expect_map,
  expect_pure and the accepted live-state loss equality. The finite solver
  theorem supplies Nash, with the exact history marginal and same total fuel.
- Complete native future state distributions are bound unchanged in the
  recursive budget induction. Tail alignment is generalized before induction.
  Parent Fin t trace, original fallback, full AOH choices, sampled oracle,
  entry memory and reference horizon are identical to the accepted consumer.
- Concrete instances and constructor fields were reviewed through both
  hidden-type parents and empty/uncertified consumers. The record has all
  field docstrings. Private finite-conditioning helper has no game instances.
- Public names were checked against complete prior targeted/global axiom
  inventories. All library lines fit100 columns and the existing transport
  source patterns have no match after comment removal. No target is removed.

This is static source/type review, not Lean elaboration or Python execution.
Only new-SHA Actions can establish compiler, configured normal/slow lint,
full transitive axioms, architecture and all225 tests. Expected surface:
186 build targets, 148 targeted modules, 289 global modules.
Workflows, audits, heartbeat cap, solver definitions and accepted source pins
are unchanged; audit edits only add the three new modules.

## Meaning and completion boundary

Canonical grouping removes the artificial need to compare every singleton
root to a PBS before averaging. It does not assert every grouped charge is
smaller than every previous envelope under all choices, nor make unknown
opponents equal to computed average opponents. Saved MODEL is not the
unknown opponent's factual posterior. The group classifier is proof-side
and reveals no private state to the solver or opponent.

Conditional calibration/opponent/support rates and rooted-original solver
equivalence remain open. The new candidate must pass its own Actions.
No original-source row is promoted. M06 remains incomplete with
SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 pending. Existing independent error/T
interpretation and explicit child loss remain; source details are in
M06-theorem3-interpretation.md rather than repeated in scheduled prompts.
