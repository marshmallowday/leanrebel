# Rooted-child decode: fee60dd failure and dependent-index repair

Candidate: fee60ddcd8e871df6dbd5a9647457c6860ffce9d.
Accepted baseline remains c1edc995d1a9790ae569c3edbdd23c2a7e99199b.
All four runs completed on the candidate SHA before this repair.

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36515895487](https://github.com/marshmallowday/leanrebel/actions/runs/36515895487) | 109237959230 | failure |
| ReBeL checks | [36515895505](https://github.com/marshmallowday/leanrebel/actions/runs/36515895505) | 109237959322 | failure |
| Targeted | [36515895531](https://github.com/marshmallowday/leanrebel/actions/runs/36515895531) | 109237959485 | failure |
| Inventory | [36515895504](https://github.com/marshmallowday/leanrebel/actions/runs/36515895504) | 109237959266 | success |

The source snapshot job 109237959465 also succeeded. Complete decoded job logs,
rather than abbreviated annotations, are the evidence. All three compiler logs
contain the same two diagnostics below; each has zero axiom records. The new
downstream recursive module, examples, complete build, full lint and axiom gates
are not accepted. PBSRootChildDecode failed in 3.6/3.5/3.5 seconds respectively.

Checks passed LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 245 Python tests in 9.163 seconds. Inventory passed
245 tests in 10.847 seconds. Those checks do not establish Lean acceptance.

## Complete common compiler diagnostic

```text
error: GameTheory/Analysis/ReBeL/PBSRootChildDecode.lean:47:12: Unknown identifier `target`
error: GameTheory/Analysis/ReBeL/PBSRootChildDecode.lean:47:6: Tactic `cases` failed: major premise type is not an inductive type
  ?m.142

Explanation: the `cases` tactic is for constructor-based reasoning as well as for applying custom cases principles with a 'using' clause or a registered '@[cases_eliminator]' theorem. The above type neither is an inductive type nor has a registered theorem.

case extend
E : ExecutionProtocol (Fin 2)
M : InformationModel E
roots : FinDist E.History
observations : List M.PublicSignal
past : List (Option (List M.PublicSignal))
state source : (pbsRootProtocol roots).State
prior : (pbsRootProtocol roots).Trace source
joint : (i : Fin 2) → Option ((pbsRootProtocol roots).Action i)
legal : (pbsRootProtocol roots).Legal source joint
realized : state ∈ ((pbsRootProtocol roots).step source ⟨joint, legal⟩).support
observed :
  publicTrace (pbsRootFullInformation M roots).toInfoSignals
      { state := state, trace := prior.extend joint legal realized }.trace =
    some observations :: past
x✝ : ?m.142
⊢ { state := state, trace := prior.extend joint legal realized }.state =
      some (pbsRootChildRead roots { state := state, trace := prior.extend joint legal realized }) ∧
    publicTrace (fullInformation M).toInfoSignals
        (pbsRootChildRead roots { state := state, trace := prior.extend joint legal realized }).trace =
      observations
```

## Repair and type review before commit

In dependent elimination of `trace : Trace state`, the endpoint index is already
the existing `state`. The branch did not introduce a local identifier `target`.
Replace `@extend source target prior joint legal realized` with
`@extend source _ prior joint legal realized`, and `cases target` with
`cases state`. This is the accepted pattern in
`PBSRootBehavioral.pbsRoot_behavioralChooser`. The Trace constructor signature
in Execution.lean and the actual error context were checked together.

The previous static review checked the constructor but missed that its endpoint
index is retained under this dependent cases operation. This was a review error,
not evidence of a mathematical problem. Reversing these two textual changes
restores the parent Lean file byte for byte. Definitions, theorem signatures,
all other proofs, instances, solver behavior and mathematical assumptions stay
unchanged.

Re-read History/Trace, pbsRootSignals.publicSignal and accepted root behavioral
decoding. The start/none branches explicitly eliminate none=some; the some branch
reads the same original history and public index. Re-read every new decoder,
continuation/deviation/Nash consumer, recursive selected-table/public-splice law,
private full law/security, fresh scalar comparison and all five concrete examples.
No other new module uses the invalid dependent target branch pattern.

The original/rooted History/Choice/InfoState carriers, fullInformation's six
universes, history-indexed child PBS, Option.some readout and original AOH
reconstruction remain unchanged. The outer observation depth and child remaining
fuel remain separate. Actual selected tolerance is still
positiveMassFloor*loss, with positivity from positiveMassFloor_pos. Typed
PBSChildSolve/trunk, root fallback, protocol-dependent noise, seed-blind unknown
opponent, same retained draw and all concrete continuation horizons were checked.
No posterior reset, policy equality or native-chain calibration is introduced.

This is static signature/consumer review, not a Lean compilation or a local
audit/test run. Same-new-SHA Actions must validate the repair and previously
unreached downstream modules. The expected validation surface stays 199 build
targets, 161 targeted/301 global audit modules and 245 Python tests.
Workflow triggers, audit criteria, heartbeat limits, registrations and tests
are unchanged.

## Artifact metadata

ZIP contents were not read. Metadata was inspected:
- Target 11011685983: 5331 bytes,
  sha256 7e4262b8a45a1ce380b72cdb43fc9765380f7daa7e81053b9cf5b23ab5af3c88.
- Global 11011895884: 21717 bytes,
  sha256 5232cec4469ec6a1e7854d7df7670b0507a0e2172cb7b6d72fc8587f0b645ff8.
- Source 11011001688: 3026152 bytes,
  sha256 fd86fb268fbbf1610fbdc9e1cb14647bfb0bf3136a603c80683bdf364defec61.
- CI and inventory: no artifacts.

M06 remains incomplete. Exact MODEL child decoding is separate from actual
native successive-query calibration and useful small-rate bounds. Paper
obligations SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain pending.
