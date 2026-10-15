import research.parent.«cuboid-formal».ParityObstruction
import research.parent.«cuboid-formal».GaussTransfer
import research.parent.«cuboid-formal».IntegralQuintic

/-!
The transformed quintic's odd/odd obstruction. This module does not prove
the changes of variable from the original second-cuboid polynomial.
-/

namespace CuboidResearch
open Polynomial

theorem integralQuintic_no_quadratic (d p q : ℤ)
    (hd : Odd d) (hp : Odd p) (hq : Odd q) (D : Polynomial ℚ)
    (hD : D.natDegree = 2) :
    ¬ D ∣ (integralQuintic d p q).map (Int.castRingHom ℚ) := by
  intro hdiv
  have hd0 : d ≠ 0 := by
    intro hz
    subst d
    exact Int.not_odd_zero hd
  have hdegree := integralQuintic_natDegree d p q hd0
  have hF0 : integralQuintic d p q ≠ 0 := by
    intro hz
    simp [hz] at hdegree
  obtain ⟨A, B, hfactor, hA, hB⟩ :=
    rational_quadratic_divisor_integral_factorization _ hF0 hdegree ⟨D, hD, hdiv⟩
  have hlead : ((integralQuintic d p q).leadingCoeff : ZMod 2) ≠ 0 := by
    rw [integralQuintic_leadingCoeff d p q hd0, Int.cast_pow,
      odd_cast_two_eq_one d hd]
    norm_num
  exact no_two_three_integral_factorization _ A B hfactor hA hB hlead
    (integralQuintic_mod_two d p q hd)
    (integralQuintic_constant_not_four_dvd d p q hp hq)

noncomputable def transformedQuintic (k : ℚ) : Polynomial ℚ :=
  X ^ 5 + X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 + C (2 - 2 * k)

theorem integralQuintic_map (d p q : ℤ) (k : ℚ)
    (hscale : (d : ℚ) ^ 2 * (1 - k) = (p : ℚ) ^ 2 * (q : ℚ) ^ 2) :
    (integralQuintic d p q).map (Int.castRingHom ℚ) =
      C ((d : ℚ) ^ 2) * transformedQuintic k := by
  have hc : 2 * (p : ℚ) ^ 2 * (q : ℚ) ^ 2 = (d : ℚ) ^ 2 * (2 - 2 * k) := by
    nlinarith [hscale]
  simp only [integralQuintic, transformedQuintic, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_ofNat,
    Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [hc, C_mul]
  ring

theorem transformedQuintic_no_quadratic (d p q : ℤ) (k : ℚ)
    (hd : Odd d) (hp : Odd p) (hq : Odd q)
    (hscale : (d : ℚ) ^ 2 * (1 - k) = (p : ℚ) ^ 2 * (q : ℚ) ^ 2)
    (D : Polynomial ℚ) (hD : D.natDegree = 2) :
    ¬ D ∣ transformedQuintic k := by
  intro hdiv
  apply integralQuintic_no_quadratic d p q hd hp hq D hD
  rw [integralQuintic_map d p q k hscale]
  exact dvd_mul_of_dvd_right hdiv _

theorem half_sum_scale (p q : ℤ) (hp : Odd p) (hq : Odd q) :
    (((p ^ 2 + q ^ 2) / 2 : ℤ) : ℚ) ^ 2 *
      (1 - (((p : ℚ) ^ 2 - (q : ℚ) ^ 2) /
        ((p : ℚ) ^ 2 + (q : ℚ) ^ 2)) ^ 2) =
      (p : ℚ) ^ 2 * (q : ℚ) ^ 2 := by
  let d : ℤ := (p ^ 2 + q ^ 2) / 2
  have hp0 : p ≠ 0 := by
    intro hz
    subst p
    exact Int.not_odd_zero hp
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  have hs0 : (p : ℚ) ^ 2 + (q : ℚ) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hpQ) (sq_nonneg _))
  have heq : 2 * (d : ℚ) = (p : ℚ) ^ 2 + (q : ℚ) ^ 2 := by
    exact_mod_cast twice_half_sum_squares p q hp hq
  have hdQ : (d : ℚ) = ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) / 2 := by linarith
  change (d : ℚ) ^ 2 * (1 - (((p : ℚ) ^ 2 - (q : ℚ) ^ 2) /
    ((p : ℚ) ^ 2 + (q : ℚ) ^ 2)) ^ 2) = _
  rw [hdQ]
  field_simp
  ring

theorem odd_odd_transformedQuintic_no_quadratic (p q : ℤ)
    (hp : Odd p) (hq : Odd q) (D : Polynomial ℚ) (hD : D.natDegree = 2) :
    ¬ D ∣ transformedQuintic
      ((((p : ℚ) ^ 2 - (q : ℚ) ^ 2) /
        ((p : ℚ) ^ 2 + (q : ℚ) ^ 2)) ^ 2) := by
  exact transformedQuintic_no_quadratic ((p ^ 2 + q ^ 2) / 2) p q _
    (odd_half_sum_squares p q hp hq) hp hq (half_sum_scale p q hp hq) D hD

theorem ratio_parameter (p q : ℚ) (hq : q ≠ 0) :
    ((p / q) ^ 2 - 1) / ((p / q) ^ 2 + 1) =
      (p ^ 2 - q ^ 2) / (p ^ 2 + q ^ 2) := by
  have hs : p ^ 2 + q ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hq))
  have ht : (p / q) ^ 2 + 1 ≠ 0 := by positivity
  field_simp

theorem odd_odd_ratio_transformedQuintic_no_quadratic (p q : ℤ)
    (hp : Odd p) (hq : Odd q) (D : Polynomial ℚ) (hD : D.natDegree = 2) :
    ¬ D ∣ transformedQuintic
      (((((p : ℚ) / (q : ℚ)) ^ 2 - 1) /
        (((p : ℚ) / (q : ℚ)) ^ 2 + 1)) ^ 2) := by
  have hq0 : q ≠ 0 := by
    intro hz
    subst q
    exact Int.not_odd_zero hq
  rw [ratio_parameter _ _ (by exact_mod_cast hq0)]
  exact odd_odd_transformedQuintic_no_quadratic p q hp hq D hD

#print axioms integralQuintic_no_quadratic
#print axioms transformedQuintic_no_quadratic
#print axioms odd_odd_transformedQuintic_no_quadratic
#print axioms odd_odd_ratio_transformedQuintic_no_quadratic

end CuboidResearch
