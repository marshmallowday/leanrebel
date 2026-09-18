# M04 source correspondence

Reviewed on 2026-09-19 (Japan time). Existing source identities, page locators
and hashes in `inventory/sources.json` and `inventory/paper.tsv` are unchanged.
PDFs are not redistributed here. The new web readings below identify their
retrieval URLs; no unmeasured byte hash is claimed.

## Primary readings

1. Brown, Bakhtin, Lerer and Gong, ReBeL, NeurIPS 2020 publication, 13 pages:
   https://proceedings.neurips.cc/paper/2020/file/c61f571dbd2fb949d3fe5ae1608dd48b-Paper.pdf
   The publication's section 5.1 and references [28]/[61] were read. The page-5
   value discussion was also inspected as a rendered PDF page. This is an
   alternate publisher URL, not a new asserted edition of the pinned paper.
2. Zinkevich, Johanson, Bowling and Piccione, *Regret Minimization in Games with
   Incomplete Information*, author-hosted 14-page version including appendix:
   https://poker.cs.ualberta.ca/publications/NIPS07-cfr.pdf
   Rendered pages 3 and 4 were inspected, including equations (1)-(8) and
   Theorems 2-4. The filename refers to NIPS 2007; ReBeL's bibliography gives
   the proceedings publication as 2008. This is not claimed to be a byte-identical
   proceedings PDF.

The required dependency [61] is the finite perfect-recall regret decomposition
and conversion of the own-reach average to approximate Nash. The Lean chain
in `M04.md` supplies these facts. It uses unnormalized counterfactual values,
explicit zero-denominator behavior, a legal fallback rather than insisting on
the source uniform no-positive-regret rule, and conservative structural
constants. It does not claim the source's exact constants or sampled variant.

Reference [28] is Hoda, Gilpin, Pena and Sandholm, *Smoothing Techniques for
Computing Nash Equilibria of Sequential Games* (2010). Section 5.1 cites it
among alternative solvers. It is not used in the implemented regret-matching
proof. `P-DEP-28` therefore records provenance/context, not a smoothing proof.
No technical result from [28] was assumed or labeled as newly verified.

## Existing pinned source correspondence

The main-paper section-3 best-response/Nash definitions are interpreted through
canonical complete behavioral deviations. Equilibrium-value uniqueness means
two given exact zero-sum equilibria have the same value; existence is separate.
Appendix-B `P-OWN-REACH`, `P-REACH-MIX`, and `P-REACH-ZERO` use the fixed
inventory's action-reach product, weighted numerator/denominator and explicit
zero-mass interpretation. `ReachFactorization`, `WeightedAverage`,
`OwnReachAverage` and `IndependentRealization` supply their proof obligations.

Main section 5.1's depth-limited CFR-D and supplementary I's variants are not
identified with this full-game vanilla solver. Original C++ syntax inventory
entries remain visible and pending for subsequent source-to-implementation
refinement. This record does not turn a cited algorithm family into a proof of
every algorithm or line in the official implementation.
