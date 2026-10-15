import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-!
Known Gauss-lemma dependency for the proposed odd/odd cuboid restriction.

Target: a rational degree-two divisor of a nonzero integral degree-five
polynomial gives integral factors of degrees two and three. No primitivity
assumption on the original polynomial is needed. This file does not prove
the cuboid transformations or any cuboid conjecture.
-/

namespace CuboidResearch

open Polynomial
open scoped nonZeroDivisors

/-- Transfer a rational divisor to an integral divisor of the same natural degree. -/
theorem integral_divisor_of_rational_divisor (F : Polynomial ℤ) (D : Polynomial ℚ)
    (hdiv : D ∣ F.map (Int.castRingHom ℚ)) :
    ∃ A : Polynomial ℤ, A ∣ F ∧ A.natDegree = D.natDegree := by
  let N := IsLocalization.integerNormalization (nonZeroDivisors ℤ) D
  obtain ⟨b, hb, hN⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) D
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hNmap : N.map (Int.castRingHom ℚ) = C (b : ℚ) * D := by
    simpa [N, Algebra.smul_def, Polynomial.algebraMap_apply] using hN
  have hpart : N.primPart.map (Int.castRingHom ℚ) ∣ N.map (Int.castRingHom ℚ) :=
    Polynomial.map_dvd (Int.castRingHom ℚ) N.primPart_dvd
  have hunit : IsUnit (C (b : ℚ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbQ)
  have hpartD : N.primPart.map (Int.castRingHom ℚ) ∣ D := by
    apply hunit.dvd_mul_left.mp
    rwa [← hNmap]
  have hpartF : N.primPart ∣ F :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _
      N.isPrimitive_primPart).mpr (hpartD.trans hdiv)
  refine ⟨N.primPart, hpartF, ?_⟩
  rw [N.natDegree_primPart]
  calc
    N.natDegree = (N.map (Int.castRingHom ℚ)).natDegree :=
      (natDegree_map_eq_of_injective Int.cast_injective N).symm
    _ = D.natDegree := by rw [hNmap, natDegree_C_mul hbQ]

/-- A degree-two rational divisor of a degree-five integral polynomial gives
an integral factorization of degrees two and three, with no content hypothesis. -/
theorem rational_quadratic_divisor_integral_factorization
    (F : Polynomial ℤ) (hF : F ≠ 0) (hdegree : F.natDegree = 5)
    (hdiv : ∃ D : Polynomial ℚ,
      D.natDegree = 2 ∧ D ∣ F.map (Int.castRingHom ℚ)) :
    ∃ A B : Polynomial ℤ, F = A * B ∧ A.natDegree = 2 ∧ B.natDegree = 3 := by
  obtain ⟨D, hD, hDF⟩ := hdiv
  obtain ⟨A, hAF, hAD⟩ := integral_divisor_of_rational_divisor F D hDF
  obtain ⟨B, hAB⟩ := hAF
  have hA : A.natDegree = 2 := hAD.trans hD
  have hnz : A * B ≠ 0 := by rwa [← hAB]
  have hsum := natDegree_mul (mul_ne_zero_iff.mp hnz).1 (mul_ne_zero_iff.mp hnz).2
  rw [← hAB, hdegree, hA] at hsum
  exact ⟨A, B, hAB, hA, by omega⟩

#print axioms integral_divisor_of_rational_divisor
#print axioms rational_quadratic_divisor_integral_factorization

end CuboidResearch
