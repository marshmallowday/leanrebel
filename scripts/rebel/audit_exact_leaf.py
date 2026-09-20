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
    "GameTheory.Analysis.ReBeL.Examples.CFRDExactDriver",
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
