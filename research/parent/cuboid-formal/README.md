# Verified odd/odd restriction for the second cuboid quintic

For positive unequal odd integers `p,q`, the polynomial `P_s` at `s=(p/q)^2`
has no rational divisor of degree two. Coprimality is not required. The exact
polynomial and proof appear in [the LaTeX source](odd-parameters.tex) and
[the PDF research note](odd-parameters.pdf).

The final Lean theorem is
`NumberTheoryResearch.BatchA.Cuboid.odd_odd_P_no_quadratic` in
[OddOddExclusion.lean](../../batch-a/OddOddExclusion.lean). Its hypotheses
include positivity, oddness, inequality, and the divisor's degree. Split and
repeated quadratic divisors are covered. The transitive axiom list is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

This is a restriction within the full quadratic-factor target for catalog
entry `wiki-48707305`. It leaves the opposite-parity case unresolved and does
not establish the second cuboid conjecture. Novelty is unverified; the result
is retained as a complete supporting theorem with a direct role in the full
target. It is not entered in the accepted-solution registry.

## Reproduce the proof

After running the repository's `scripts/setup_lean.sh`, run this single command
from the repository root:

```sh
scripts/with_lean.sh lake env python3 research/parent/cuboid-formal/verify.py
```

The verifier compiles all eight research modules into a fresh temporary
directory and checks the printed transitive axioms. The pinned versions are
Lean 4.35.0 and mathlib `e91b128082cc221d6432a6a5aadcd3243af8e76c`.
This check is separate from the accepted-library build; an empty accepted
library is not evidence for this theorem.

The dependency order is:

1. `ParityObstruction.lean`: the generic modulo-four factor obstruction.
2. `GaussTransfer.lean`: rational divisors give integral divisors of equal degree.
3. `IntegralQuintic.lean`: concrete coefficient and parity arithmetic.
4. `QuinticExclusion.lean`: the transformed quintic has no quadratic divisor.
5. `research/batch-a/CuboidIdentities.lean`: exact polynomial identities.
6. `research/batch-a/FactorDegreeTransfer.lean`: quotient algebras preserve divisor degrees.
7. `research/batch-a/CuboidEquivalence.lean`: the two algebra isomorphisms.
8. `research/batch-a/OddOddExclusion.lean`: the original quintic's odd/odd theorem.

The known algebraic helpers are included only as dependencies of this result.
They carry no separate novelty claim. The
[review record](../cuboid-review/FINAL_REVIEW.md) distinguishes mathematical
correctness, statement alignment, and the unresolved novelty question.

## Rebuild the note

```sh
bash scripts/setup_tex.sh
.tools/tectonic/tectonic -X compile research/parent/cuboid-formal/odd-parameters.tex --outdir research/parent/cuboid-formal
```

The standalone LaTeX source also opens in the Codex editor with PDF preview.
The exported PDF is included in the repository. Its mathematical scope is the
same as the final Lean theorem.
