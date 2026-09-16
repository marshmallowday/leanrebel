#!/usr/bin/env python3
"""Build every ReBeL module and check its transitive Lean axiom dependencies.

Uses the pinned compiler's Lean.collectAxioms, not a source grep. The generated
auditor includes tests and selects declarations by their defining module, so
private declarations and declarations outside the advertised namespace are not
silently omitted. This does not replace a semantic review or an independent
implementation of the Lean kernel.
"""
from __future__ import annotations

from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
AUDITOR = r'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefix : Name := `GameTheory.ReBeL
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if prefix.isPrefixOf modName then
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


def main() -> None:
    paths = [ROOT / "GameTheory/ReBeL.lean"]
    paths.extend(sorted((ROOT / "GameTheory/ReBeL").rglob("*.lean")))
    if not all(path.is_file() for path in paths):
        raise SystemExit("Missing ReBeL root or source module")
    modules = [path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
               for path in paths]
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


if __name__ == "__main__":
    main()
