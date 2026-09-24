#!/usr/bin/env python3
"""Additional exact-source audit of the new factual-child dependency slice.

This supplements rather than replaces the repository-wide ReBeL checks. Every
new module receives normal and slow Batteries lint, and every declaration in
those modules (including private declarations) receives transitive axiom audit.
All Lean output commands live in .lake, never in a library source module.
"""
from __future__ import annotations

from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
MODULES = (
    "GameTheory.Math.Probability.FinDistConditioning",
    "GameTheory.Analysis.ReBeL.CFRDFactualChild",
    "GameTheory.Analysis.ReBeL.CFRDFactualQuery",
    "GameTheory.Analysis.ReBeL.CFRDFactualMixture",
    "GameTheory.Analysis.ReBeL.Examples.CFRDFactualChild",
    "GameTheory.Analysis.ReBeL.CFRDClamp",
    "GameTheory.Analysis.ReBeL.CFRDExactDriver",
    "GameTheory.Analysis.ReBeL.CFRDExactSafety",
    "GameTheory.Analysis.ReBeL.CFRDNoisyDriver",
    "GameTheory.Analysis.ReBeL.Examples.CFRDExactDriver",
    "GameTheory.Analysis.ReBeL.PBSApproximateOptimality",
    "GameTheory.Analysis.ReBeL.CFRDApproximateLeaf",
    "GameTheory.Analysis.ReBeL.Examples.CFRDApproximateLeaf",
    "GameTheory.Analysis.ReBeL.FinitePlanLearning",
    "GameTheory.Analysis.ReBeL.FinitePlanNash",
    "GameTheory.Analysis.ReBeL.FinitePlanBudget",
    "GameTheory.Analysis.ReBeL.PBSFinitePlanSolver",
    "GameTheory.Math.Probability.FinDistMassFloor",
    "GameTheory.Analysis.ReBeL.Examples.PBSFinitePlanSolver",
    "GameTheory.Analysis.ReBeL.CFRDFiniteChild",
    "GameTheory.Analysis.ReBeL.CFRDFiniteContinuation",
    "GameTheory.Analysis.ReBeL.CFRDFiniteDriver",
    "GameTheory.Analysis.ReBeL.Examples.CFRDFiniteChild",
    "GameTheory.Analysis.ReBeL.CFRDRefreshMix",
    "GameTheory.Analysis.ReBeL.CFRDFiniteRefresh",
    "GameTheory.Analysis.ReBeL.CFRDFiniteRefreshSafety",
    "GameTheory.Analysis.ReBeL.Examples.CFRDFiniteRefresh",
    "GameTheory.Analysis.ReBeL.CFRDResolveEnvelope",
    "GameTheory.Analysis.ReBeL.CFRDEnvelopeSafety",
    "GameTheory.Analysis.ReBeL.Examples.CFRDEnvelope",
    "GameTheory.Analysis.ReBeL.CFRDCoherentDraw",
    "GameTheory.Analysis.ReBeL.CFRDFiniteCoherent",
    "GameTheory.Analysis.ReBeL.Examples.CFRDCoherentDraw",
    "GameTheory.Analysis.ReBeL.CFRDCoherentStages",
    "GameTheory.Analysis.ReBeL.Examples.CFRDCoherentStages",
    "GameTheory.Analysis.ReBeL.PBSRootProtocol",
    "GameTheory.Analysis.ReBeL.PBSRootInformation",
    "GameTheory.Analysis.ReBeL.PBSRootCFR",
    "GameTheory.Analysis.ReBeL.PBSRootExecution",
    "GameTheory.Analysis.ReBeL.Examples.PBSRootCFR",
    "GameTheory.Analysis.ReBeL.PBSRootBehavioral",
    "GameTheory.Analysis.ReBeL.PBSRootLocalHistory",
    "GameTheory.Analysis.ReBeL.PBSRootDecode",
    "GameTheory.Analysis.ReBeL.PBSInformationCFR",
    "GameTheory.Analysis.ReBeL.Examples.PBSRootDecode",
    "GameTheory.Analysis.ReBeL.PBSInformationBudget",
    "GameTheory.Analysis.ReBeL.CFRDInformationChild",
    "GameTheory.Analysis.ReBeL.CFRDInformationContinuation",
    "GameTheory.Analysis.ReBeL.CFRDInformationDriver",
    "GameTheory.Analysis.ReBeL.Examples.CFRDInformationChild",
    "GameTheory.Analysis.ReBeL.PBSInformationSampling",
    "GameTheory.Analysis.ReBeL.CFRDInformationSampling",
    "GameTheory.Analysis.ReBeL.Examples.PBSInformationSampling",
    "GameTheory.Analysis.ReBeL.PBSSupportedSampling",
    "GameTheory.Analysis.ReBeL.Examples.PBSSupportedSampling",
    "GameTheory.Analysis.ReBeL.CFRDInformationQuerySampling",
    "GameTheory.Analysis.ReBeL.CFRDInformationSampledDriver",
    "GameTheory.Analysis.ReBeL.Examples.CFRDInformationSampledDriver",
    "GameTheory.Analysis.ReBeL.CFRDFreshValueDrift",
    "GameTheory.Analysis.ReBeL.CFRDFreshResolve",
    "GameTheory.Analysis.ReBeL.Examples.CFRDFreshResolve",
    "GameTheory.Math.Probability.FinDistEventError",
    "GameTheory.Analysis.ReBeL.PBSCarriedSampling",
    "GameTheory.Analysis.ReBeL.Examples.PBSCarriedSampling",
    "GameTheory.Math.Probability.FinDistSequentialError",
    "GameTheory.Analysis.ReBeL.PBSCarriedRecursion",
    "GameTheory.Analysis.ReBeL.Examples.PBSCarriedRecursion",
    "GameTheory.Analysis.ReBeL.PBSRootDepthCFR",
    "GameTheory.Analysis.ReBeL.PBSInformationDepthCFR",
    "GameTheory.Analysis.ReBeL.PBSCarriedDepth",
    "GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepth",
    "GameTheory.Analysis.ReBeL.PBSCarriedDepthSampling",
    "GameTheory.Math.Probability.FinDistFirstHit",
    "GameTheory.Analysis.ReBeL.PBSCarriedDepthFirstHit",
    "GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepthSampling",
    "GameTheory.Analysis.ReBeL.PBSInformationDepthBudget",
    "GameTheory.Analysis.ReBeL.Examples.PBSInformationDepthBudget",
    "GameTheory.Analysis.ReBeL.CFRDDepthChild",
    "GameTheory.Analysis.ReBeL.CFRDNestedDepthDriver",
    "GameTheory.Analysis.ReBeL.Examples.CFRDNestedDepth",
    "GameTheory.Analysis.ReBeL.CFRDComposedChild",
    "GameTheory.Analysis.ReBeL.PBSComposedDepth",
    "GameTheory.Analysis.ReBeL.PBSRecursiveDepth",
    "GameTheory.Analysis.ReBeL.Examples.PBSRecursiveDepth",
    "GameTheory.Analysis.ReBeL.CFRDFreshChain",
    "GameTheory.Analysis.ReBeL.Examples.CFRDFreshChain",
    "GameTheory.Analysis.ReBeL.CFRDReferenceReweight",
    "GameTheory.Analysis.ReBeL.Examples.CFRDReferenceReweight",
)
AUDITOR = r'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : List Name := [__MODULE_NAMES__]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let moduleNames := env.header.moduleNames
  let mut total : Nat := 0
  for target in modules do
    let mut count : Nat := 0
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        if moduleNames[idx.toNat]! == target then
          let axioms ← Lean.collectAxioms name
          logInfo m!"EXACT_LEAF_AXIOMS {name}: {axioms.toList}"
          for ax in axioms do
            unless allowed.contains ax do
              throwError m!"Forbidden transitive axiom {ax} in {name}"
          count := count + 1
    if count == 0 then
      throwError m!"No declarations audited in {target}"
    logInfo m!"EXACT_LEAF_MODULE_AXIOM_PASS {target}: declarations={count}"
    total := total + count
  logInfo m!"EXACT_LEAF_AXIOM_AUDIT_PASS declarations={total}"
'''


def main() -> None:
    """Compile, audit and lint every named new module, failing on any error."""
    for module in MODULES:
        source = ROOT / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            raise SystemExit(f"Missing exact-child proof module: {source}")
    subprocess.run(["lake", "build", *MODULES], cwd=ROOT, check=True)
    output = ROOT / ".lake/rebel/ExactLeafAxioms.lean"
    output.parent.mkdir(parents=True, exist_ok=True)
    imports = ["import Lean.Util.CollectAxioms", "import Lean.Elab.Command"]
    imports.extend(f"import {module}" for module in MODULES)
    commands = AUDITOR.replace("__MODULE_NAMES__", ", ".join(f"`{m}" for m in MODULES))
    output.write_text("\n".join(imports) + "\n" + commands, encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(output)],
                   cwd=ROOT, check=True)
    for module in MODULES:
        print(f"EXACT_LEAF_LINT_BEGIN {module}", flush=True)
        subprocess.run(["lake", "exe", "batteries/runLinter", "--no-build", "--trace", module],
                       cwd=ROOT, check=True)
        print(f"EXACT_LEAF_LINT_PASS {module}", flush=True)
    print(f"EXACT_LEAF_VALIDATION_PASS modules={len(MODULES)}", flush=True)


if __name__ == "__main__":
    main()
