# M06 frontier source acceptance

Acceptance source: e123cb860ce0a56c2705a375b9ff1e403f7580be.
The exact-SHA build/lint/full transitive axiom evidence is in
M06-summary-coupling-e123cb8-accepted.md. This review concerns unchanged
frontier and rooted-decoding modules only. Newly added value-target code
requires its own Actions result.

## Source correspondence

The [main paper, sections 3 and 5.1, pp.5-6](https://papers.nips.cc/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Paper.pdf)
uses publicly determined finite search subgames, conversion between the
discrete and belief representations, and different treatment of genuine
terminals and depth cuts. The three accepted inventory rows are
SEARCH-FRONTIER, P-SEARCH-SETUP and P-SEARCH-LEAF.

| Requirement | Lean evidence | Scope review |
| --- | --- | --- |
| Publicly valid frontier | PublicFrontier; publicFrontier_info_closed | Stop decisions depend only on public trace; equal own full AOH cannot disagree. |
| Exhaustion, terminal, cut | frontierRun_zero; frontierRun_terminal; frontierRun_cut; frontierRun_support | Leaves retain remaining fuel; a public cut is not a terminal declaration. |
| Correct stopped continuation | frontierRun_bind_continuation; frontierValue_exact | Resuming the SAME profile recovers the full canonical history law and payoff. |
| Terminal utility | frontierLeafValue; frontierValue_exact | True terminals and zero remaining fuel use actual payoff, never a prediction. |
| Joint belief representation | frontierIterationQueries_bind | Splitting and reassembling actual stopped histories preserves the current joint law. |
| Discrete rooted solver back to PBS | pbsRootDecodeProfile_law; pbsRootDecodeProfile_unilateral_law | Arbitrary rooted outputs and original unilateral deviations decode to exact canonical laws. |

The rooted decoder requires a common root depth, established for actual
public beliefs by pbsRoot_publicBelief_depth. One administrative chance step
is explicit. Policies remain information-local and menus legal. The frontier
factorization is for finite fuel in the canonical stochastic protocol, with
finite player indexing; it does not assert an infinite-horizon result.
No value-accuracy, equilibrium, small transport cost, or network-training
convergence premise is concealed in frontier correctness.

The full e123cb8 global axiom log includes all declarations above with only
the three permitted axioms (or none). Source blobs:
Frontier f8cbdf8d294f8a2e3cd0d134297347f4f5036697;
ConditionalOracle ef127269fe1218804346e8dccc00a2fc1cd3eebe;
PBSRootDecode 6215b5e6896c70da67d65f7d60d4047cf5c85db0.

Append-only coverage-updates/M06-frontier.json records these three rows.
The historical coverage.json is unchanged. This acceptance does not upgrade
SEARCH-CFRD, SEARCH-ERROR or SAFE-THEOREM3; their additional algorithm, rate
and recursive safety obligations are distinct.
