#!/usr/bin/env python3
"""Compile registered expositions from their committed LaTeX source."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    registry = json.loads((ROOT / "catalog/results.json").read_text())
    results = (registry["complete_solutions"] + registry["subquestion_solutions"]
               + registry["direct_advances"])
    if not results:
        print("No accepted proof manuscripts to compile.")
        return
    engine = ROOT / ".tools/tectonic/tectonic"
    if not engine.is_file():
        raise RuntimeError("Run bash scripts/setup_tex.sh first.")
    for result in results:
        source = (ROOT / result["latex_file"]).resolve()
        output = (ROOT / result["pdf_file"]).resolve()
        if not source.is_relative_to(ROOT) or not output.is_relative_to(ROOT):
            raise ValueError("Manuscript paths must remain inside the repository.")
        if output.name != source.with_suffix(".pdf").name:
            raise ValueError("PDF and LaTeX filenames must have the same stem.")
        output.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([str(engine), "--keep-logs", "--outdir", str(output.parent), str(source)],
                       cwd=source.parent, check=True)
        if not output.is_file() or not output.read_bytes().startswith(b"%PDF-"):
            raise ValueError(f"PDF not generated: {output}")
        print(f"Compiled {output.relative_to(ROOT)}; visual and mathematical review still required.")


if __name__ == "__main__":
    main()
