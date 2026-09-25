# M06 supported value-calibration checkpoint — 2026-09-25

Core source: 59a90791825122208247ea912a9c94833cad05b6.
Parent lint repair: c984277c2238e4dd1249ff3ace6fc5444175858a.
Continuation branch: rebel/m06-calibration-controls-20260925.

## Added source-level route

CFRDSourceRates additionally proves:

- cfrDFreshValueChange_le_calibration: OLD and NEW continuation values calibrated
  to one information-local target with errors e_old and e_new, under their own
  equal reference laws, have positive signed change at most e_old + e_new.
- cfrDWeightedTransportLoss_le_calibration: the actual correlated private
  iteration/history loss is at most childLoss + e_old + e_new. Calibration is
  needed only at OLD-supported live queries. Perfect recall supplies actual
  support inclusion for an arbitrary unknown opponent, without a density bound,
  positive minimum reach or whole-outcome-law distance premise.

The core commit adds106 Lean lines and deletes no existing source lines.
Its M06 run is36095287300/job107946171666; record the completed result separately.

## Actual execution and controls

Examples/CFRDSourceRates extends the actual biased finite-parent/two-fresh-child
consumer with freshChainControlCalibration, an explicit common-target source
contract, its budget comparison and freshChainControl_biased_calibrated_security.
Reference equality is derived from cfrDFreshInformationChain_referenceLaw, not
assumed of the unknown opponent's actual posterior. Finite outer time, positive
parent bias, both child tolerances and private seed/history correlation remain.

The tie control uses a nonconstant payoff on Bool×Bool: two pure outcome laws
have maximal L1 distance two while both are calibrated exactly to value minus
one. Value calibration is therefore not whole-law convergence in disguise.

freshChainControl_value_abs_le_two and freshChainControl_coarse_calibrated
prove an unconditional coarse source baseline for the real parent and children.
The errors two and two follow from their payoff bound, not assumed security.
They establish a usable nonempty source contract, NOT a vanishing rate.
Existing rare-query, NEW-only-atom, disappearing-query and zero-fuel controls
are retained unchanged.

## Validation boundary

Both changed modules were already M06 targets, analytic umbrella imports and
supplemental lint/axiom modules. No module, exception, dependency pin or linter
setting is removed or weakened. New exact-source CI remains mandatory.

Parent repair c984277 passed M06 target/validation run36093962253 and full CI
run36093962268; this does not establish any later source result. The full old
4b439571 log records axiom audit PASS1491 before its subsequent unused-argument
lint failure; earlier claims of an unreached axiom step have been corrected.

## Remaining mathematical obligation

Common-target calibration is not inferred from scalar Nash error. A sharper,
vanishing calibration estimate must still be derived from the intended native
oracle/solver, or replaced by a proved native actual-law argument. Later-PBS
independent re-solving and first-exit rates are still open. M06 and owning
coverage rows SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending. Do not accept the printed or corrected Theorem3 by substituting these
conditional source premises for its algorithmic proof.
