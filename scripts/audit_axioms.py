#!/usr/bin/env python3
"""Audit transitive axioms of every registered declaration after lake build."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    registry = json.loads((ROOT / "catalog/results.json").read_text())
    names = [name for kind in ("complete_solutions", "direct_advances")
             for result in registry[kind] for name in result["lean_declarations"]]
    if not names:
        print("No accepted theorem declarations to audit; this is not a proof result.")
        return
    for name in names:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
            raise ValueError(f"Invalid declaration name: {name}")
    with tempfile.TemporaryDirectory(prefix="axiom-audit-", dir=ROOT / ".lake") as temp:
        source = Path(temp) / "Audit.lean"
        source.write_text("import NumberTheory\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n")
        run = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                             text=True, capture_output=True, check=True)
        print(run.stdout, end="")
        if run.stderr:
            print(run.stderr, end="")
        for name in names:
            no_axioms = re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", run.stdout)
            match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", run.stdout)
            if no_axioms:
                continue
            if not match:
                raise ValueError(f"Missing axiom output for {name}")
            axioms = {s.strip() for s in match.group(1).split(",") if s.strip()}
            if axioms - ALLOWED:
                raise ValueError(f"Unaccepted axioms for {name}: {sorted(axioms - ALLOWED)}")
    print(f"Axiom audit passed for {len(names)} declarations.")


if __name__ == "__main__":
    main()
