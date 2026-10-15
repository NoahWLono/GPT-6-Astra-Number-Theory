import Mathlib

/- Quotient algebras preserve factor degrees, including multiplicities.
   This is supporting infrastructure for the cuboid argument only. -/
namespace NumberTheoryResearch.BatchA.Cuboid
open Polynomial

theorem isUnit_sub_of_aeval_eq_zero
    {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (f : K[X]) (x : S) (a : K) (hx : aeval x f = 0) (ha : f.eval a ≠ 0) :
    IsUnit (x - algebraMap K S a) := by
  have hd := map_dvd (aeval x).toRingHom (X_sub_C_dvd_sub_C_eval (p := f) (a := a))
  have hd' : x - algebraMap K S a ∣ -algebraMap K S (f.eval a) := by
    simpa [hx] using hd
  apply isUnit_of_dvd_unit hd'
  exact ((isUnit_iff_ne_zero.mpr ha).map (algebraMap K S)).neg

theorem inverse_mem_of_mul_eq_one
    {K S : Type*} [Field K] [CommRing S] [Algebra K S] [Module.Finite K S]
    (A : Subalgebra K S) (x y : S) (hx : x ∈ A) (hxy : x * y = 1) : y ∈ A := by
  let μ : A →ₗ[K] A := LinearMap.mul K A ⟨x, hx⟩
  have hinj : Function.Injective μ := by
    intro a b hab
    apply Subtype.ext
    have hab' : x * (a : S) = x * (b : S) := congrArg Subtype.val hab
    calc
      (a : S) = y * (x * (a : S)) := by rw [← mul_assoc, mul_comm y x, hxy, one_mul]
      _ = y * (x * (b : S)) := by rw [hab']
      _ = (b : S) := by rw [← mul_assoc, mul_comm y x, hxy, one_mul]
  obtain ⟨z, hz⟩ := (LinearMap.surjective_of_injective hinj) 1
  have hz' : x * (z : S) = 1 := congrArg Subtype.val hz
  have heq : (z : S) = y := by
    calc
      (z : S) = y * (x * (z : S)) := by rw [← mul_assoc, mul_comm y x, hxy, one_mul]
      _ = y := by rw [hz', mul_one]
  exact heq ▸ z.property

theorem factor_of_generated_algebra
    {K S : Type*} [Field K] [CommRing S] [Algebra K S] [Module.Finite K S]
    (f : K[X]) (x : S) (hgen : Algebra.adjoin K {x} = ⊤)
    (hroot : aeval x f = 0) :
    ∃ d : K[X], d ∣ f ∧ d.natDegree = Module.finrank K S := by
  let h := IsAdjoinRootMonic.mkOfAdjoinEqTop' hgen
  refine ⟨minpoly K x, ?_, h.finrank.symm⟩
  have hf : f ∈ RingHom.ker h.map := hroot
  rw [h.ker_map, Ideal.mem_span_singleton] at hf
  exact hf

theorem factor_degree_transfer
    {K : Type*} [Field K] (f g d : K[X]) (hd : d ∣ f) (hd0 : d ≠ 0)
    (e : AdjoinRoot g ≃ₐ[K] AdjoinRoot f) :
    ∃ c : K[X], c ∣ g ∧ c.natDegree = d.natDegree := by
  have : Module.Finite K (AdjoinRoot d) := (AdjoinRoot.powerBasis hd0).finite
  let φ : AdjoinRoot g →ₐ[K] AdjoinRoot d :=
    (AdjoinRoot.algHomOfDvd K f d hd).comp e.toAlgHom
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    refine ⟨e.symm (AdjoinRoot.mk f p), ?_⟩
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply]
    change aeval (AdjoinRoot.root d) p = AdjoinRoot.mk d p
    exact (AdjoinRoot.aeval_eq p)
  have hgen : Algebra.adjoin K {φ (AdjoinRoot.root g)} = ⊤ := by
    rw [← AlgHom.map_adjoin_singleton, AdjoinRoot.adjoinRoot_eq_top,
      Algebra.map_top, AlgHom.range_eq_top]
    exact hsurj
  obtain ⟨c, hc, hcdeg⟩ := factor_of_generated_algebra g (φ (AdjoinRoot.root g)) hgen
    (AdjoinRoot.aeval_algHom_eq_zero g φ)
  refine ⟨c, hc, hcdeg.trans ?_⟩
  exact finrank_quotient_span_eq_natDegree

#print axioms factor_of_generated_algebra
#print axioms factor_degree_transfer
#print axioms inverse_mem_of_mul_eq_one
#print axioms isUnit_sub_of_aeval_eq_zero
end NumberTheoryResearch.BatchA.Cuboid
