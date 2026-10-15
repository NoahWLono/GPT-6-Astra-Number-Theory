# Gauss factor transfer: checked helper

Date: 2026-10-15. Status: both theorems in `GaussTransfer.lean` compile with the pinned Lean 4.35.0 and mathlib revision `e91b128082cc221d6432a6a5aadcd3243af8e76c`. This is a known Gauss-lemma dependency for the proposed cuboid restriction. It has no novelty claim or solution-registry entry.

The main checked signature, in namespace `CuboidResearch`, is:

```lean
theorem rational_quadratic_divisor_integral_factorization
    (F : Polynomial ℤ) (hF : F ≠ 0) (hdegree : F.natDegree = 5)
    (hdiv : ∃ D : Polynomial ℚ,
      D.natDegree = 2 ∧ D ∣ F.map (Int.castRingHom ℚ)) :
    ∃ A B : Polynomial ℤ,
      F = A * B ∧ A.natDegree = 2 ∧ B.natDegree = 3
```

There is no primitivity hypothesis on `F`. The general helper `integral_divisor_of_rational_divisor` transfers any rational divisor to an integral divisor with the same natural degree. Its proof clears denominators using `IsLocalization.integerNormalization`, takes the primitive part, and applies mathlib's `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`. The complementary integral factor absorbs any content of `F`.

Reproduction command from the workspace root:

```sh
scripts/with_lean.sh lake env lean research/parent/cuboid-formal/GaussTransfer.lean
```

The command exits successfully. Each `#print axioms` reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, `admit`, custom axiom, or `native_decide`. Its scope ends at rational-to-integral factor transfer. Concrete cuboid coefficient arithmetic and the rational quotient-algebra maps remain separate obligations owned by the parent and batch A.
