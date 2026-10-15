# GPT-6 Astra Number Theory

This project seeks complete Lean-verified solutions to problems listed in
[Wikipedia's unsolved number theory category](https://en.wikipedia.org/wiki/Category:Unsolved_problems_in_number_theory).
It is an active research project. **No open problem has been solved by this
project at initialization.**

The first phase inventories every direct entry and checks the linked
subcategories. Each entry needs a precise target and a current literature check
before proof work begins. Category membership alone does not establish that a
problem remains open.

The magic square of squares is excluded because it is being attempted in a
separate project.

## Research policy

The aim is complete solutions, including proofs and disproofs on equal terms.
Complete resolutions of substantive, precisely identified open subquestions are
recorded separately, with the parent conjecture's remaining status explicit.
We retain partial mathematical work only when it has a documented role in
advancing a full solution. We do not count finite
verification, a conditional result, or a formalization of a known theorem as a
solution to an open problem.

Accepted solutions require a Lean proof, matching LaTeX and PDF exposition,
reproducible source code, an axiom audit, and independent review of both the
mathematics and the correspondence between the formal and informal statements.
See [AGENTS.md](AGENTS.md) for the research and verification rules.

## Layout

- `catalog/`: dated inventory, exclusions, and assignment records.
- `research/`: literature screening and documented attempts by stable problem ID.
- `NumberTheory/`: accepted Lean modules that directly advance a full solution.
- `papers/`: LaTeX sources and corresponding PDFs.
- `scripts/`: catalog and verification tools.
- `docs/`: coordination policy and implementation plan.

Three GPT-6 Astra Ultra research chats screen disjoint groups of direct entries.
The parent coordinates integration, audits subcategory coverage, and reviews
candidate proof targets.

The initial snapshot contains 124 direct pages (123 eligible) and 143 unique
pages including the abc subcategory. The
[subcategory scope review](research/parent/REPORT.md) distinguishes additional
open questions from biographies, definitions, and established theorems.

## Reproduction

The Lean version is pinned in `lean-toolchain`; Mathlib is pinned in
`lakefile.toml` and `lake-manifest.json` when dependencies are resolved.
Local tooling can be installed without changing shell profiles:

```sh
bash scripts/setup_lean.sh
scripts/with_lean.sh lake build
python3 scripts/check_integrity.py
```

Refresh the Wikipedia membership snapshot with:

```sh
python3 scripts/fetch_catalog.py
```

Compile accepted manuscripts on Linux x86_64 with:

```sh
bash scripts/setup_tex.sh
python3 scripts/build_papers.py
```

The Tectonic 0.17.0 installer verifies the official release asset's SHA-256.
The manuscript command reports that there is nothing to compile until a result
is registered. Generated PDFs still require visual and mathematical review.

The catalog records when membership was retrieved. Its page titles and links
identify source articles; original mathematical summaries are written separately
with references. No general software or document license has yet been selected.
