import research.«batch-a».CuboidEquivalence
import research.parent.«cuboid-formal».QuinticExclusion

/- A parity restriction advancing the quadratic-factor target.
   No full second-cuboid irreducibility theorem is asserted. -/
namespace NumberTheoryResearch.BatchA.Cuboid
open Polynomial

theorem gPoly_eq_transformedQuintic (k : ℚ) :
    gPoly k = CuboidResearch.transformedQuintic k := by
  simp only [gPoly, G, CuboidResearch.transformedQuintic, C_sub, C_mul, C_ofNat]
  ring

theorem odd_odd_P_no_quadratic (p q : ℤ) (hp : Odd p) (hq : Odd q)
    (hppos : 0 < p) (hqpos : 0 < q) (hpq : p ≠ q)
    (D : ℚ[X]) (hD : D.natDegree = 2) :
    ¬ D ∣ pPoly (((p : ℚ) / (q : ℚ)) ^ 2) := by
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hppos
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hqpos
  have hq0 : (q : ℚ) ≠ 0 := ne_of_gt hqQ
  have hrpos : (0 : ℚ) < (p : ℚ) / (q : ℚ) := div_pos hpQ hqQ
  let s : ℚ := ((p : ℚ) / (q : ℚ)) ^ 2
  have hspos : 0 < s := sq_pos_of_pos hrpos
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hs1 : s + 1 ≠ 0 := by linarith
  have hsne : s ≠ 1 := by
    intro heq
    have hrone : (p : ℚ) / (q : ℚ) = 1 := by dsimp [s] at heq; nlinarith
    have hpqQ : (p : ℚ) = q := (div_eq_one_iff_eq hq0).mp hrone
    exact hpq (by exact_mod_cast hpqQ)
  intro hdiv
  obtain ⟨E, hE, hdeg⟩ := quadratic_factor_transfer s hs0 hsne hs1 D hD hdiv
  rw [gPoly_eq_transformedQuintic] at hE
  exact CuboidResearch.odd_odd_ratio_transformedQuintic_no_quadratic p q hp hq E hdeg hE

#print axioms odd_odd_P_no_quadratic
end NumberTheoryResearch.BatchA.Cuboid
