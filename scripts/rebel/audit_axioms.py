#!/usr/bin/env python3
"""Compile the complete ReBeL proof surface and audit transitive Lean axioms.

M01's arithmetic probe lives in the existing architecture-owned Tests surface.
Basic and analytic ReBeL modules, including tests, are discovered recursively.
The canonical reach module extracted during M03 and its analysis entry point
are explicitly included in both the declaration audit and full/slow lint.
Lean.collectAxioms checks types and proof bodies, not just source spellings.
The defining module selects declarations, including private declarations and
names outside the advertised namespace. This does not replace semantic review
or an independent implementation of the Lean kernel.
"""
from __future__ import annotations

from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
AUDITOR = r'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modulePrefix : Name := `GameTheory.ReBeL
  let analysisPrefix : Name := `GameTheory.Analysis.ReBeL
  let probe : Name := `GameTheory.Tests.ReBeLSourceDiagnostics
  let reach : Name := `GameTheory.Protocol.BehavioralReach
  let reachAnalysis : Name := `GameTheory.Analysis.Protocol.CounterfactualReach
  let moduleNames := env.header.moduleNames
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := moduleNames[idx.toNat]!
      if modulePrefix.isPrefixOf modName || analysisPrefix.isPrefixOf modName ||
          modName == probe ||
          modName == reach || modName == reachAnalysis then
        let axioms ← Lean.collectAxioms name
        logInfo m!"REBEL_AXIOMS {name}: {axioms.toList}"
        for ax in axioms do
          unless allowed.contains ax do
            throwError m!"Forbidden transitive axiom {ax} in {name}"
        count := count + 1
  if count == 0 then
    throwError "ReBeL axiom audit found no declarations"
  logInfo m!"REBEL_AXIOM_AUDIT_PASS declarations={count}"
'''


def proof_modules() -> list[str]:
    """Exact module list shared by compilation, lint, axiom audit and regressions."""
    probe = ROOT / "GameTheory/Tests/ReBeLSourceDiagnostics.lean"
    paths = [probe,
             ROOT / "GameTheory/Protocol/BehavioralReach.lean",
             ROOT / "GameTheory/Analysis/Protocol/CounterfactualReach.lean"]
    for required in paths:
        if not required.is_file():
            raise SystemExit(f"Missing required proof surface: {required.relative_to(ROOT)}")
    public_root = ROOT / "GameTheory/ReBeL.lean"
    if public_root.is_file():
        paths.append(public_root)
    paths.extend(sorted((ROOT / "GameTheory/ReBeL").rglob("*.lean")))
    analysis_root = ROOT / "GameTheory/Analysis/ReBeL.lean"
    if analysis_root.is_file():
        paths.append(analysis_root)
    paths.extend(sorted((ROOT / "GameTheory/Analysis/ReBeL").rglob("*.lean")))
    modules = [path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
               for path in paths]
    return modules


def main() -> None:
    modules = proof_modules()
    for module in modules:
        print(f"REBEL_AUDIT_MODULE {module}", flush=True)
    subprocess.run(["lake", "build", *modules], cwd=ROOT, check=True)
    output = ROOT / ".lake/rebel/AxiomAudit.lean"
    output.parent.mkdir(parents=True, exist_ok=True)
    imports = ["import Lean.Util.CollectAxioms", "import Lean.Elab.Command"]
    imports.extend(f"import {module}" for module in modules)
    output.write_text("\n".join(imports) + "\n" + AUDITOR, encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(output)],
                   cwd=ROOT, check=True)
    # Each selected module, including the extracted foundation, receives the
    # complete normal and slow lint checks. No existing gate is removed.
    for module in modules:
        print(f"REBEL_LINT_BEGIN {module}", flush=True)
        subprocess.run(["lake", "exe", "batteries/runLinter", "--no-build", "--trace", module],
                       cwd=ROOT, check=True)
        print(f"REBEL_LINT_PASS {module}", flush=True)
    print(f"REBEL_VALIDATION_PASS modules={len(modules)}", flush=True)


if __name__ == "__main__":
    main()
