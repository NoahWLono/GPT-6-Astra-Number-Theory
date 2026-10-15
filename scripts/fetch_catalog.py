#!/usr/bin/env python3
"""Capture complete category membership through MediaWiki continuation tokens."""
import datetime as dt
import hashlib
import json
from pathlib import Path
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
CATEGORY = "Category:Unsolved problems in number theory"
EXCLUDED = "Magic square of squares"


def members(title):
    query = dict(action="query", list="categorymembers", cmtitle=title,
                 cmlimit="500", format="json")
    rows = []
    while True:
        url = "https://en.wikipedia.org/w/api.php?" + urllib.parse.urlencode(query)
        request = urllib.request.Request(url, headers={
            "User-Agent": "GPT6AstraNumberTheory/0.1 (public research catalog)"})
        with urllib.request.urlopen(request, timeout=60) as response:
            data = json.load(response)
        if "error" in data:
            raise RuntimeError(data["error"])
        rows.extend(data["query"]["categorymembers"])
        if "continue" not in data:
            return rows
        query.update(data["continue"])


def main():
    pending, categories, articles = [CATEGORY], {}, {}
    while pending:
        category = pending.pop(0)
        if category in categories:
            continue
        rows = members(category)
        categories[category] = rows
        for row in rows:
            if row["ns"] == 14:
                pending.append(row["title"])
            elif row["ns"] == 0:
                pageid = row["pageid"]
                if pageid not in articles:
                    articles[pageid] = dict(
                        id=f"wiki-{pageid}", title=row["title"], pageid=pageid,
                        url="https://en.wikipedia.org/wiki/" + urllib.parse.quote(
                            row["title"].replace(" ", "_"), safe="()'"),
                        categories=[], status="not_screened")
                articles[pageid]["categories"].append(category)
    rows = sorted(articles.values(), key=lambda r: r["title"].casefold())
    eligible = []
    for row in rows:
        row["scope"] = "direct" if CATEGORY in row["categories"] else "subcategory"
        if row["title"] == EXCLUDED:
            row.update(status="excluded", assignment=None,
                       exclusion_reason="User assigned this problem to a separate agent.")
        elif row["scope"] == "direct":
            eligible.append(row)
        else:
            row["assignment"] = "parent"
    for index, row in enumerate(eligible):
        row["assignment"] = "batch-" + "abc"[min(2, index * 3 // len(eligible))]
    payload = dict(
        schema_version=1,
        retrieved_at_utc=dt.datetime.now(dt.timezone.utc).isoformat(),
        source_url="https://en.wikipedia.org/wiki/" + CATEGORY.replace(" ", "_"),
        source_api="https://en.wikipedia.org/w/api.php",
        note="Membership snapshot only; mathematical status requires separate review.",
        direct_pages=sum(r["scope"] == "direct" for r in rows),
        eligible_direct_pages=len(eligible), unique_pages=len(rows),
        categories=categories, entries=rows)
    dest = ROOT / "catalog"
    dest.mkdir(exist_ok=True)
    output = json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    (dest / "inventory.json").write_text(output)
    digest = hashlib.sha256(output.encode()).hexdigest()
    (dest / "inventory.sha256").write_text(f"{digest}  catalog/inventory.json\n")
    lines = ["# Category inventory", "", f"Retrieved: {payload['retrieved_at_utc']}", "",
             f"{payload['direct_pages']} direct pages; {len(eligible)} eligible after exclusion; "
             f"{len(rows)} unique pages including subcategories.", "",
             "This is an inventory, not a completed mathematical review.", "",
             "| ID | Article | Scope | Assignment |", "| --- | --- | --- | --- |"]
    for row in rows:
        assignment = row.get("assignment") or "EXCLUDED"
        lines.append(f"| {row['id']} | [{row['title']}]({row['url']}) | {row['scope']} | {assignment} |")
    (dest / "README.md").write_text("\n".join(lines) + "\n")
    for batch in "abc":
        path = ROOT / "research" / f"batch-{batch}"
        path.mkdir(parents=True, exist_ok=True)
        (path / "assignment.json").write_text(json.dumps(
            [r for r in rows if r.get("assignment") == f"batch-{batch}"],
            ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k:payload[k] for k in ["direct_pages","eligible_direct_pages","unique_pages"]}))
    print(f"Categories: {len(categories)}; SHA256: {digest}")


if __name__ == "__main__":
    main()
