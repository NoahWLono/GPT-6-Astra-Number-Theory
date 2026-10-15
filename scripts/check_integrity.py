#!/usr/bin/env python3
"""Check inventory coverage and artifact completeness, not mathematical correctness."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def artifact(relative):
    path = (ROOT / relative).resolve()
    require(path.is_relative_to(ROOT) and path.is_file(), f"Missing/invalid artifact: {relative}")
    return path


def main():
    snapshot = (ROOT / "catalog/inventory.json").read_bytes()
    expected = (ROOT / "catalog/inventory.sha256").read_text().split()[0]
    require(hashlib.sha256(snapshot).hexdigest() == expected, "Inventory hash mismatch")
    inventory = json.loads(snapshot)
    rows = inventory["entries"]
    require(len({r["id"] for r in rows}) == len(rows), "Duplicate inventory IDs")
    direct = [r for r in rows if r["scope"] == "direct"]
    excluded = [r for r in rows if r["status"] == "excluded"]
    require(len(excluded) == 1 and excluded[0]["title"] == "Magic square of squares",
            "The user exclusion must remain explicit")
    require(excluded[0].get("assignment") is None, "Excluded problem assigned")
    eligible = [r for r in direct if r["status"] != "excluded"]
    require(len(direct) == inventory["direct_pages"], "Direct count mismatch")
    require(len(eligible) == inventory["eligible_direct_pages"], "Eligible count mismatch")
    require(len(rows) == inventory["unique_pages"], "Unique count mismatch")
    assigned = []
    for batch in "abc":
        assignments = json.loads((ROOT / f"research/batch-{batch}/assignment.json").read_text())
        expected_rows = [r for r in rows if r.get("assignment") == f"batch-{batch}"]
        require(assignments == expected_rows, f"Batch {batch} does not match inventory")
        assigned.extend(r["id"] for r in assignments)
    require(len(assigned) == len(set(assigned)), "Duplicate worker assignment")
    require(set(assigned) == {r["id"] for r in eligible}, "Incomplete direct coverage")

    screen_dir = ROOT / "catalog/initial-screening"
    screen = json.loads((screen_dir / "manifest.json").read_text())
    screened_ids = [r["id"] for r in screen["entries"]]
    require(len(screened_ids) == len(set(screened_ids)), "Duplicate screening ID")
    require(set(screened_ids) == {r["id"] for r in rows if r["status"] != "excluded"},
            "Initial screening coverage mismatch")
    for source in screen["inputs"]:
        path = artifact(f"catalog/initial-screening/{source['file']}")
        require(hashlib.sha256(path.read_bytes()).hexdigest() == source["sha256"],
                f"Initial screening hash mismatch: {source['file']}")

    lean_files = [ROOT / "NumberTheory.lean", *sorted((ROOT / "NumberTheory").rglob("*.lean"))]
    # This intentionally conservative source lint also catches words in comments.
    # It supplements the kernel build and transitive axiom audit; it cannot replace review.
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|implemented_by|unsafe)\b")
    for path in lean_files:
        require(not forbidden.search(path.read_text()), f"Unaccepted construct in {path.relative_to(ROOT)}")
    registry = json.loads((ROOT / "catalog/results.json").read_text())
    result_ids = set()
    for kind in ("complete_solutions", "subquestion_solutions", "direct_advances"):
        for result in registry[kind]:
            require(result["id"] not in result_ids, "Duplicate result ID")
            result_ids.add(result["id"])
            require(result["problem_id"] in {r["id"] for r in rows if r["status"] != "excluded"},
                    "Result refers to excluded or unknown problem")
            require(result.get("lean_declarations"), "No declarations to audit")
            require(result.get("resolution_kind") in {"proof", "disproof", "partial_advance"},
                    "Resolution kind must be explicit")
            if kind != "direct_advances":
                require(result["resolution_kind"] != "partial_advance", "Partial result marked complete")
            if kind == "subquestion_solutions":
                require(result.get("subquestion_statement") and result.get("parent_problem_status"),
                        "Subquestion results must state their target and the parent problem's status")
            for field in ("lean_file", "latex_file", "pdf_file", "review_file", "statement_file"):
                artifact(result[field])
            require(artifact(result["pdf_file"]).read_bytes().startswith(b"%PDF-"), "Invalid PDF")
            require(result.get("full_solution_relevance"), "No full-solution relevance documented")
    print(f"Inventory valid: {len(direct)} direct, {len(eligible)} assigned, {len(rows)} unique pages.")
    print(f"Initial screening snapshot: {len(screened_ids)} eligible records; evidence depth varies.")
    print(f"Accepted main-problem solutions: {len(registry['complete_solutions'])}; "
          f"subquestion solutions: {len(registry['subquestion_solutions'])}; "
          f"direct advances: {len(registry['direct_advances'])}.")
    print("Artifact checks do not establish mathematical correctness or novelty.")


if __name__ == "__main__":
    main()
