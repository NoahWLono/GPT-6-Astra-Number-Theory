import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
Research dependency for the proposed odd/odd cuboid factor exclusion.
This file proves only the generic modular obstruction. The rational changes of
variable and Gauss-lemma transfer to the cuboid polynomial are separate steps.
It is not imported by the accepted library or registered as a new result.
-/

namespace CuboidResearch
open Polynomial

theorem constant_zero_of_mod_two_divisor (a : Polynomial (ZMod 2))
    (hdegree : 1 < a.natDegree) (hdiv : a ∣ X ^ 4 * (X + 1)) :
    a.coeff 0 = 0 := by
  by_contra hconstant
  have hx : ¬ (X : Polynomial (ZMod 2)) ∣ a := by
    simpa only [X_dvd_iff] using hconstant
  have hcop : IsCoprime a (X ^ 4 : Polynomial (ZMod 2)) :=
    ((prime_X (R := ZMod 2)).irreducible.coprime_iff_not_dvd.mpr hx).symm.pow_right
  have hsmall : a ∣ (X + 1 : Polynomial (ZMod 2)) := hcop.dvd_of_dvd_mul_left hdiv
  have hne : (X + 1 : Polynomial (ZMod 2)) ≠ 0 := by
    simpa using (monic_X_add_C (1 : ZMod 2)).ne_zero
  have hbound := Polynomial.natDegree_le_of_dvd hsmall hne
  have hlin : (X + 1 : Polynomial (ZMod 2)).natDegree = 1 := by
    simp
  omega

theorem no_two_three_integral_factorization (F A B : Polynomial ℤ)
    (hfactor : F = A * B)
    (hA : A.natDegree = 2) (hB : B.natDegree = 3)
    (hlead : (F.leadingCoeff : ZMod 2) ≠ 0)
    (hmod : F.map (Int.castRingHom (ZMod 2)) = X ^ 4 * (X + 1))
    (hconstant : ¬ (4 : ℤ) ∣ F.coeff 0) : False := by
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hprod : (A.leadingCoeff : ZMod 2) * (B.leadingCoeff : ZMod 2) ≠ 0 := by
    simpa [hfactor, Polynomial.leadingCoeff_mul] using hlead
  have hla : φ A.leadingCoeff ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hlb : φ B.leadingCoeff ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hda : (A.map φ).natDegree = 2 :=
    (natDegree_map_of_leadingCoeff_ne_zero φ hla).trans hA
  have hdb : (B.map φ).natDegree = 3 :=
    (natDegree_map_of_leadingCoeff_ne_zero φ hlb).trans hB
  have hm : A.map φ * B.map φ = X ^ 4 * (X + 1) := by
    rw [← Polynomial.map_mul, ← hfactor]
    exact hmod
  have ha0 : (A.map φ).coeff 0 = 0 :=
    constant_zero_of_mod_two_divisor _ (by omega) ⟨B.map φ, hm.symm⟩
  have hb0 : (B.map φ).coeff 0 = 0 :=
    constant_zero_of_mod_two_divisor _ (by omega) ⟨A.map φ, hm.symm.trans (mul_comm _ _)⟩
  have ha2 : (2 : ℤ) ∣ A.coeff 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simpa [φ] using ha0
  have hb2 : (2 : ℤ) ∣ B.coeff 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simpa [φ] using hb0
  apply hconstant
  simpa [hfactor] using mul_dvd_mul ha2 hb2

#print axioms constant_zero_of_mod_two_divisor
#print axioms no_two_three_integral_factorization

end CuboidResearch
