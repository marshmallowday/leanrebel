# M06 frontier checkpoint

This is a work-in-progress proof checkpoint, not milestone acceptance.
The initial reviewed base is `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`;
complete document-review evidence is in M06-checkpoint.md.

## Implementation

`GameTheory.ReBeL.Frontier` introduces public-observation stopping decisions,
a stopped canonical behavioral run retaining unused fuel, separate terminal
and cut equations, exact full-run factorization, leaf classification, exact
continuation backup, and its pointwise history-leaf error bound. There are no
placeholder proofs or new axioms. Compiler acceptance is pending at this
checkpoint; inspect the target-SHA `M06 targeted proof feedback` run.

The history-level backup lemma is a semantic foundation, NOT a replacement
for the source algorithm's information-state value-vector oracle. The next
proof slice must derive the information-fiber backup using perfect recall and
counterfactual reach, connect current-iteration joint PBSs, and establish the
actual coupled depth-limited CFR-D regret/safety results. Coverage is not
promoted by this checkpoint.

## Compiler transport recovery

The pinned compiler export succeeded in run `35447008145`, but downloading
its 746 MB compiler archive hit the connector's explicit 512 MiB limit.
Commit `1d3dc0b7774bdff7daf9598451d6efc587c88fa8` splits exports into 400 MB
parts. Run `35447455843` produced all split artifacts and compiler evidence.
The plugin downloaded those artifacts successfully; subsequent local runtime
calls returned transport timeouts. The small-log targeted Actions workflow
therefore provides direct compiler feedback without relying on that runtime.
It supplements, rather than replaces, the existing full acceptance gates.

## Source contract clarification

Burch et al., arXiv:1303.4441v4, Theorem 2 (page 4) and its discussion (page 5),
require counterfactual best responses in the continuations, not just on-path
best responses. The off-path contract and its consistency with the same
continuation strategy must remain explicit. ReBeL supplemental pages 21-22
retain a finite-iteration term in the proof even though the printed Theorem 3
formula incorrectly multiplies that term by the oracle error.
