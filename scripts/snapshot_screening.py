#!/usr/bin/env python3
"""Freeze an initial triage snapshot after checking exact assignment coverage.

This checks record coverage, not mathematical correctness or literature novelty.
Existing snapshots are never overwritten by this command.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "catalog/initial-screening"


def main():
    if DEST.exists():
        raise SystemExit("Initial snapshot already exists; review changes explicitly.")
    inventory = json.loads((ROOT / "catalog/inventory.json").read_text())
    eligible = {r["id"]: r for r in inventory["entries"] if r["status"] != "excluded"}
    outputs, index, inputs = {}, [], []
    for batch in "abc":
        source = ROOT / f"research/batch-{batch}/screening.json"
        raw = source.read_bytes()
        data = json.loads(raw)
        rows = data if isinstance(data, list) else data["entries"]
        expected = {r["id"] for r in eligible.values() if r.get("assignment") == f"batch-{batch}"}
        ids = [r["id"] for r in rows]
        if len(ids) != len(set(ids)) or set(ids) != expected:
            raise ValueError(f"Batch {batch} coverage mismatch")
        for row in rows:
            for field in ("exact_question", "obstruction", "next_step"):
                if not row.get(field):
                    raise ValueError(f"Missing {field}: {row['id']}")
            if row["title"] != eligible[row["id"]]["title"]:
                raise ValueError(f"Title mismatch: {row['id']}")
            index.append({
                "id": row["id"], "title": row["title"], "scope": "direct",
                "review_level": "initial scope and literature screening",
                "record_file": f"batch-{batch}.json",
                "assessment": row.get("current_status", row.get("status")),
            })
        filename = f"batch-{batch}.json"
        outputs[filename] = raw
        inputs.append({"file": filename, "source": str(source.relative_to(ROOT)),
                       "sha256": hashlib.sha256(raw).hexdigest(), "records": len(rows)})

    source = ROOT / "research/parent/subcategory-screening.json"
    raw = source.read_bytes()
    rows = json.loads(raw)["entries"]
    for row in rows:
        index.append({"id": row["id"], "title": row["title"], "scope": "subcategory",
                      "review_level": row["review_level"], "record_file": "subcategory.json",
                      "assessment": row["classification"]})
    outputs["subcategory.json"] = raw
    inputs.append({"file": "subcategory.json", "source": str(source.relative_to(ROOT)),
                   "sha256": hashlib.sha256(raw).hexdigest(), "records": len(rows)})
    ids = [row["id"] for row in index]
    if len(ids) != len(set(ids)) or set(ids) != set(eligible):
        raise ValueError("Combined screen does not cover the eligible inventory exactly")
    index.sort(key=lambda row: row["title"].casefold())
    manifest = {
        "schema_version": 1, "screened_on": "2026-10-15",
        "direct_records": sum(row["scope"] == "direct" for row in index),
        "additional_scope_records": sum(row["scope"] == "subcategory" for row in index),
        "limitation": "Initial triage; evidence depth varies. No exhaustive literature, proof, or novelty certification.",
        "inputs": inputs, "entries": index,
    }
    outputs["manifest.json"] = (json.dumps(manifest, ensure_ascii=False, indent=2) + "\n").encode()
    DEST.mkdir(parents=True)
    for filename, raw in outputs.items():
        (DEST / filename).write_bytes(raw)
    print(f"Frozen {len(index)} eligible records: {manifest['direct_records']} direct and "
          f"{manifest['additional_scope_records']} additional scope reviews.")


if __name__ == "__main__":
    main()
