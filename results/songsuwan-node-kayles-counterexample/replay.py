"""Rebuild the proof using the pinned Mathlib lake environment."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
manifest = json.loads((root / "LeanVerification.json").read_text())
version = subprocess.check_output(["lean", "--version"], text=True)
if "0b77e12952ad39077d80d8bd6b66d601f225c321" not in version:
    raise SystemExit("Use the pinned Lean 4.37.0-rc1 toolchain.")
paths = [str(Path(p).resolve()) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
with tempfile.TemporaryDirectory() as temp:
    work = Path(temp)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([temp, *paths]), LEAN_NUM_THREADS="1",
               ELAN_TOOLCHAIN="leanprover/lean4:v4.37.0-rc1")
    def lean(*args):
        return subprocess.check_output(["lean", "-j1", "-DwarningAsError=true", *args],
                                       text=True, cwd=work, env=env)
    for mod in manifest["modules"]:
        shutil.copyfile(root / (mod + ".lean"), work / (mod + ".lean"))
        print("Checking", mod, flush=True)
        lean("-o", mod + ".olean", mod + ".lean")
    audit = ["import " + m for m in manifest["modules"]]
    for thm in manifest["theorems"]:
        audit.extend(["#check " + thm, "#print axioms " + thm])
    (work / "Audit.lean").write_text("\n".join(audit) + "\n")
    result = lean("Audit.lean")
    print(result)
    for thm in manifest["theorems"]:
        lines = [s for s in result.splitlines() if s.startswith("'" + thm + "' depends on axioms: [")]
        if len(lines) != 1 or set(lines[0].split("[")[-1].rstrip("]").split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
            raise SystemExit("Unexpected axioms for " + thm)
