import Mathlib

/-!
Arithmetic for the integral quintic in the odd/odd cuboid argument.
These lemmas are supporting research, not a resolution of the cuboid conjecture.
-/

namespace CuboidResearch
open Polynomial

noncomputable def integralQuintic (d p q : ℤ) : Polynomial ℤ :=
  C (d ^ 2) * (X ^ 5 + X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2)
    + C (2 * p ^ 2 * q ^ 2)

theorem odd_cast_two_eq_one (n : ℤ) (hn : Odd n) : (n : ZMod 2) = 1 := by
  exact hn.intCast_zmod_two

theorem integralQuintic_natDegree (d p q : ℤ) (hd : d ≠ 0) :
    (integralQuintic d p q).natDegree = 5 := by
  unfold integralQuintic
  compute_degree!

theorem integralQuintic_leadingCoeff (d p q : ℤ) (hd : d ≠ 0) :
    (integralQuintic d p q).leadingCoeff = d ^ 2 := by
  rw [Polynomial.leadingCoeff, integralQuintic_natDegree d p q hd]
  unfold integralQuintic
  compute_degree!

theorem integralQuintic_coeff_zero (d p q : ℤ) :
    (integralQuintic d p q).coeff 0 = 2 * p ^ 2 * q ^ 2 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [integralQuintic]

theorem integralQuintic_mod_two (d p q : ℤ) (hd : Odd d) :
    (integralQuintic d p q).map (Int.castRingHom (ZMod 2)) =
      X ^ 4 * (X + 1) := by
  have hd1 := odd_cast_two_eq_one d hd
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h2p : (2 : Polynomial (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C : ZMod 2 → Polynomial (ZMod 2)) h2
  simp only [integralQuintic, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_ofNat, Int.coe_castRingHom, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, hd1, h2, h2p]
  simp only [one_pow, C_1, one_mul, zero_mul, sub_zero, C_0, add_zero]
  ring

theorem integralQuintic_constant_not_four_dvd (d p q : ℤ)
    (hp : Odd p) (hq : Odd q) : ¬ (4 : ℤ) ∣ (integralQuintic d p q).coeff 0 := by
  rw [integralQuintic_coeff_zero]
  have ho : Odd (p ^ 2 * q ^ 2) := (hp.pow).mul (hq.pow)
  have hm := Int.odd_iff.mp ho
  intro hdiv
  rw [mul_assoc] at hdiv
  omega

theorem odd_square_mod_four (n : ℤ) (hn : Odd n) : n ^ 2 % 4 = 1 := by
  have hm := Int.odd_iff.mp hn
  have hcases : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h <;> rw [pow_two, Int.mul_emod, h] <;> norm_num

theorem odd_half_sum_squares (p q : ℤ) (hp : Odd p) (hq : Odd q) :
    Odd ((p ^ 2 + q ^ 2) / 2) := by
  have hpm := odd_square_mod_four p hp
  have hqm := odd_square_mod_four q hq
  apply Int.odd_iff.mpr
  omega

theorem twice_half_sum_squares (p q : ℤ) (hp : Odd p) (hq : Odd q) :
    2 * ((p ^ 2 + q ^ 2) / 2) = p ^ 2 + q ^ 2 := by
  have hpm := odd_square_mod_four p hp
  have hqm := odd_square_mod_four q hq
  omega

#print axioms integralQuintic_natDegree
#print axioms integralQuintic_mod_two
#print axioms integralQuintic_constant_not_four_dvd
#print axioms odd_half_sum_squares
#print axioms twice_half_sum_squares

end CuboidResearch
