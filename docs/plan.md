# Initial research and verification plan

The user authorized a public repository, a long-horizon goal, and three GPT-6
Astra Ultra research chats in this folder. The selected strategy is broad
screening followed by focused attempts; retain only mathematics that directly
advances a full solution. The magic square of squares is excluded.

## Initial deliverables

- [x] Capture all direct category members and recursively inspect subcategories.
  Save source URLs, retrieval time, stable IDs, scope, and an explicit exclusion.
- [x] Assign every eligible direct member to exactly one of three research chats.
  The parent reviews additional subcategory entries and duplicates.
- [x] Pin Lean and Mathlib, resolve dependencies, and run a clean baseline build.
  An empty verified library must never be described as a mathematical result.
- [x] Publish the public repository with catalog, policy, sources, and CI checks.
- [x] Complete initial literature screening, separating established results,
  genuine open statements, compound questions, and uncertain status.
- [x] Select focused attempts using exact statements, potential proof routes,
  and identified obstructions. Avoid routine formalization without a direct role.

All 123 eligible direct entries now have initial records, and the 19 additional
subcategory pages have an article-scope review. This does not certify an
exhaustive literature search or the correctness of any external proof claim.
The current round keeps a balanced mix of universal arguments and exact
construction searches, following the user's preference.

## Candidate acceptance

For a promising candidate, write its mathematical specification first. Search for
prior work and existing Lean statements. Attempt a proof or disproof, then test
the argument independently before formalization. Check every quantifier and
hypothesis against the source problem. Record failures so later attempts can
avoid repeating them.

Every proposed complete result must include Lean source, a successful build and
axiom audit, matching LaTeX and PDF, full computational source when used, and
independent review. Inspect the compiled PDF visually. Publish its exact status
and unresolved limitations. Only the parent integrates reviewed artifacts.

## Coordination

Workers share the checkout but write disjoint research directories. The parent
owns shared configuration and publication. Parent/worker chat identifiers stay
in ignored local coordination files. Review persistent files and compact chat
status snapshots instead of repeatedly reading full conversation transcripts.

The goal stays active while required research remains. No successful outcome is
assumed and no finite verification is counted as a solution to an infinite claim.
