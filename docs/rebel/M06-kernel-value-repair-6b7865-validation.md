# Exact-source 6b7865 feedback and second compiler repair

Source: 6b7865e312af3108568566187468e4df97bbd8eb on
rebel/m06-kernel-value-repair-20260927. This is a failed intermediate candidate,
not Lean acceptance. The original 3ef5 parser failure and the dac8 checkpoint
remain preserved. The branch head was re-read before the next write.

## Exact-source reconstruction and finite checks

The GitHub plugin downloaded source artifact 10922154886 from GLOBAL run
36292478764, successful source-snapshot job 108545224021. The archive's
source-commit.txt equals the source above. ZIP SHA-256:
1eb0a2844bed0473021cf51ab085e88ae76302a123d7aab5bdd08e14a563dd08.
The enclosed TAR checksum was independently verified:
8b33a0a3358f5c9e4ee6a27f53a6f3a7493a9fe55ba1045f81e0284c7aa529bc.
Extraction and local checks did not invoke git or access GitHub directly.

The core, integration, example, umbrella, target manifest, audit consumer and
Python fixture blobs all match the owning ledger. Replacing the nine hrecall
tokens in the core with recall reproduces exactly the original c968c342409328e91e572a02b813ba4c671f5c67
blob. The first repair therefore changed only those nine identifiers.

On the exact extracted source the following commands passed:

- python scripts/rebel/check_coverage.py: 3,054 ledger items; structural only.
- python scripts/rebel/check_inventory.py: 3,054 inventory items; structural only.
- python -W error -m unittest discover -s scripts/rebel/tests -v: all 149 tests,
  including eight changed-kernel fixtures and 4,050 exhaustive Fraction cases.

Local log SHA-256 values, respectively:
757e4bed6b6ef8dc9fd69d61b96bef8af8b62992e0c057676f74eef8f590ad82;
582841a04146972ffca4a9bcc2f325a2132b16efa727b508f20fe0c355f1f509;
45a02e0188b5ba01026ebf6727397d2615580acc3ec6c348d936c2f4bf2120e4.
The exact-source consumers contain 116 unique targeted and 259 unique global
modules. All three changed-kernel modules remain in both audits, the 154-entry
build target manifest and the public analysis umbrella. This is not Lean validation.

## Complete targeted compiler feedback

TARGET run 36292478763 / job 108545087124 completed with FAILURE. The plugin
downloaded its complete artifact 10923021191. ZIP SHA-256:
55aeb19589e4b356cd281a4d058e60423450ef039921ef54560228d3c869c4a9.
The 25,740-byte m06-targeted.log SHA-256 is
0944472bbf1748739f458be77ef2e929b70b4952b93f596e3c83bd6a5482f191.
The first line matches 6b7865 exactly; Lean is 4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

The reserved-token errors disappeared. Three newly exposed core diagnostics
remain: line 70 cannot rewrite the lambda-applied Set.range attainment witness;
line 115 cannot resolve abs_add; line 118 finds the additive monotonicity lemma
places the unchanged summand on the wrong side. The target's lint/axiom step
was skipped after compilation failed. No transitive axiom acceptance is claimed.

## Focused second repair

Use change to beta-normalize each actual attainment equality before rewriting;
use abs_add_le for the triangle inequality; use add_le_add with le_rfl to state
explicitly which summand is unchanged. Apply that same monotonicity repair to
the depth integration's final inequality. The latter module was blocked by the
failed import, so this is a proactive repair of the identical observed API issue,
not a claim to have observed an independent integration diagnostic.

No theorem statement, premise, coefficient, type domain, opponent, event mass,
finite-T term, example, import, build target, dependency or audit rule is changed.
The repaired core and integration blobs are recorded in the owner ledger. Their
new exact-SHA build, normal/slow lint and full axiom records remain to be checked.

## Other source-specific jobs

INVENTORY 36292478778 succeeded. GLOBAL 36292478764 / job 108545223929 and
FULL CI 36292478756 / job 108545228737 had no inspected final result at this
checkpoint; a newer source push may cancel them. These are not acceptance of
the repair. The already accepted 51d5 target/global/full-CI evidence is separate.
M06 and the four parent SEARCH/SAFE obligations remain incomplete.
