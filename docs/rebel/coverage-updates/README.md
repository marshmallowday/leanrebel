# Append-only coverage acceptance updates

The authoritative live ledger is printed by:

```text
python3 scripts/rebel/check_coverage.py --expanded-json
```

It consists of the unchanged historical `../coverage.json`, its hash-pinned
paper/official child inventories and original overrides, followed by these
versioned `*.json` acceptance updates. Both standard coverage and inventory
checks consume the updates before applying their existing validators.
`coverage_inventory.expand` remains the historical/base expander for frozen
regression fixtures; `coverage_updates.expand_with_updates` is the live view.

Each update pins the exact Git blob of the historical coverage.json and its
own milestone. An entry names an existing obligation and expected old status,
changes only status, and APPENDS evidence. It cannot modify source identity,
replace old evidence, downgrade an existing verified result, touch a different
milestone, or refer to a stale Lean source blob. Duplicate JSON keys and
repeated targets are rejected. Proof and scope fields are mandatory even for
qualified/refuted rows. The data is never executed.

A future baseline rewrite requires an explicit reviewed roll-up/rebase of the
journals; a mismatching blob fails rather than silently losing accepted work.
These are metadata safeguards. Source review, exact-SHA Lean compilation,
Batteries lint and the transitive kernel-axiom audit remain separate gates.
