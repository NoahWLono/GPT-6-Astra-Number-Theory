import «research».«batch-a».CuboidIdentities
import «research».«batch-a».FactorDegreeTransfer

namespace NumberTheoryResearch.BatchA.Cuboid
open Polynomial

noncomputable def gPoly (k : ℚ) : ℚ[X] := G (C k) X
noncomputable def tPoly (k : ℚ) : ℚ[X] := T (C k) X
noncomputable def pPoly (s : ℚ) : ℚ[X] := P (C s) X

theorem gPoly_degree (k : ℚ) : (gPoly k).natDegree = 5 := by
  unfold gPoly G
  compute_degree!

theorem tPoly_degree (k : ℚ) : (tPoly k).natDegree = 5 := by
  unfold tPoly T
  compute_degree!

theorem pPoly_degree (s : ℚ) : (pPoly s).natDegree = 5 := by
  unfold pPoly P
  compute_degree!

theorem aeval_pPoly {S : Type*} [CommRing S] [Algebra ℚ S] (s : ℚ) (x : S) :
    aeval x (pPoly s) = P (algebraMap ℚ S s) x := by
  simp [pPoly, P, map_ofNat]

theorem aeval_gPoly {S : Type*} [CommRing S] [Algebra ℚ S] (k : ℚ) (v : S) :
    aeval v (gPoly k) = G (algebraMap ℚ S k) v := by
  simp [gPoly, G, map_ofNat]

theorem aeval_tPoly {S : Type*} [CommRing S] [Algebra ℚ S] (k : ℚ) (w : S) :
    aeval w (tPoly k) = T (algebraMap ℚ S k) w := by
  simp [tPoly, T, map_ofNat]

theorem adjoin_one_sub_sq
    {S : Type*} [CommRing S] [Algebra ℚ S] [Module.Finite ℚ S]
    (k : ℚ) (hk : k ≠ 1) (v : S) (hv : G (algebraMap ℚ S k) v = 0)
    (hgen : Algebra.adjoin ℚ {v} = ⊤) : Algebra.adjoin ℚ {1 - v ^ 2} = ⊤ := by
  let A := Algebra.adjoin ℚ ({1 - v ^ 2} : Set S)
  have hw : 1 - v ^ 2 ∈ A := Algebra.subset_adjoin (Set.mem_singleton _)
  have hdmem : (1 - v ^ 2) ^ 2 - 1 ∈ A := A.sub_mem (A.pow_mem hw 2) A.one_mem
  have hdunit : IsUnit ((1 - v ^ 2) ^ 2 - 1) := by
    have hc : IsUnit (algebraMap ℚ S (2 * (k - 1))) :=
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hk))).map _
    apply isUnit_of_dvd_unit _ hc
    refine ⟨v + 1, ?_⟩
    simp only [map_mul, map_sub, map_ofNat, map_one]
    unfold G at hv
    linear_combination -hv
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hdunit
  have humem : u ∈ A := inverse_mem_of_mul_eq_one A _ u hdmem hu
  have hnmem : 2 * algebraMap ℚ S k - 1 - (1 - v ^ 2) ^ 2 ∈ A := by
    exact A.sub_mem (A.sub_mem (A.mul_mem (A.natCast_mem 2) (A.algebraMap_mem k))
      A.one_mem) (A.pow_mem hw 2)
  have heq : (2 * algebraMap ℚ S k - 1 - (1 - v ^ 2) ^ 2) * u = v := by
    have hi := inverse_v_cleared (algebraMap ℚ S k) v
    linear_combination u * hi - u * hv + v * hu
  have hvmem : v ∈ A := heq ▸ A.mul_mem hnmem humem
  apply top_unique
  rw [← hgen]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hvmem)

noncomputable def tEquivG (k : ℚ) (hk : k ≠ 1) :
    AdjoinRoot (tPoly k) ≃ₐ[ℚ] AdjoinRoot (gPoly k) := by
  have hg0 : gPoly k ≠ 0 := by
    intro h
    have := gPoly_degree k
    simp [h] at this
  have ht0 : tPoly k ≠ 0 := by
    intro h
    have := tPoly_degree k
    simp [h] at this
  have : Module.Finite ℚ (AdjoinRoot (gPoly k)) := (AdjoinRoot.powerBasis hg0).finite
  have : Module.Finite ℚ (AdjoinRoot (tPoly k)) := (AdjoinRoot.powerBasis ht0).finite
  let v := AdjoinRoot.root (gPoly k)
  have hv : G (algebraMap ℚ (AdjoinRoot (gPoly k)) k) v = 0 := by
    rw [← aeval_gPoly, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hw : aeval (1 - v ^ 2) (tPoly k) = 0 := by
    rw [aeval_tPoly, T_comp, hv, zero_mul]
  let φ : AdjoinRoot (tPoly k) →ₐ[ℚ] AdjoinRoot (gPoly k) :=
    AdjoinRoot.liftAlgHom (tPoly k) (Algebra.ofId ℚ _) (1 - v ^ 2) hw
  have hsurj : Function.Surjective φ := by
    have hgen := adjoin_one_sub_sq k hk v hv AdjoinRoot.adjoinRoot_eq_top
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hgen
    intro z
    obtain ⟨p, hp⟩ := hgen z
    refine ⟨AdjoinRoot.mk (tPoly k) p, ?_⟩
    exact hp
  apply AlgEquiv.ofBijective φ
  apply OrzechProperty.bijective_of_surjective_of_finrank_le φ.toLinearMap hsurj
  change Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {tPoly k}) ≤
    Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {gPoly k})
  rw [finrank_quotient_span_eq_natDegree, finrank_quotient_span_eq_natDegree,
    tPoly_degree, gPoly_degree]

theorem mobius_root
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (s h : ℚ) (hs : h * (s + 1) = s - 1) (hs1 : s + 1 ≠ 0)
    (x u : S) (hu : (x + algebraMap ℚ S s) * u = 1)
    (hx : P (algebraMap ℚ S s) x = 0) :
    T ((algebraMap ℚ S h) ^ 2) (algebraMap ℚ S h * (x - algebraMap ℚ S s) * u) = 0 := by
  have hs' : algebraMap ℚ S h * (algebraMap ℚ S s + 1) = algebraMap ℚ S s - 1 := by
    simpa only [map_mul, map_add, map_sub, map_one] using congrArg (algebraMap ℚ S) hs
  have hi := T_homogeneous_relation (algebraMap ℚ S s) (algebraMap ℚ S h) x hs'
  rw [hx, mul_zero] at hi
  have hc : IsUnit (algebraMap ℚ S s + 1) := by
    simpa using (isUnit_iff_ne_zero.mpr hs1).map (algebraMap ℚ S)
  have hth := (hc.pow 4).mul_right_eq_zero.mp hi
  rw [TH_inverse _ _ _ u hu] at hth
  have hden : IsUnit (x + algebraMap ℚ S s) := isUnit_iff_exists_inv.mpr ⟨u, hu⟩
  exact (hden.pow 5).mul_left_eq_zero.mp hth

theorem adjoin_mobius
    {S : Type*} [CommRing S] [Algebra ℚ S] [Module.Finite ℚ S]
    (s h : ℚ) (hs : s ≠ 0) (hh : h ≠ 0)
    (x u : S) (hu : (x + algebraMap ℚ S s) * u = 1)
    (hgen : Algebra.adjoin ℚ {x} = ⊤) :
    Algebra.adjoin ℚ {algebraMap ℚ S h * (x - algebraMap ℚ S s) * u} = ⊤ := by
  let a := algebraMap ℚ S s
  let b := algebraMap ℚ S h
  let w := b * (x - a) * u
  let A := Algebra.adjoin ℚ ({w} : Set S)
  have hw : w ∈ A := Algebra.subset_adjoin (Set.mem_singleton _)
  have ha : a ∈ A := A.algebraMap_mem s
  have hb : b ∈ A := A.algebraMap_mem h
  have haunit : IsUnit a := (isUnit_iff_ne_zero.mpr hs).map _
  have hbunit : IsUnit b := (isUnit_iff_ne_zero.mpr hh).map _
  have h2unit : IsUnit (2 : S) := by
    have hi : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using hi.map (algebraMap ℚ S)
  have huunit : IsUnit u := isUnit_iff_exists_inv.mpr ⟨x + a, by simpa [mul_comm] using hu⟩
  have hdeneq : b - w = 2 * b * a * u := by
    dsimp [w, a, b]
    linear_combination -(algebraMap ℚ S h) * hu
  have hdenunit : IsUnit (b - w) := by
    rw [hdeneq]
    exact ((h2unit.mul hbunit).mul haunit).mul huunit
  obtain ⟨j, hj⟩ := isUnit_iff_exists_inv.mp hdenunit
  have hjmem : j ∈ A := inverse_mem_of_mul_eq_one A _ _ (A.sub_mem hb hw) hj
  have hrel : x * (b - w) = a * (b + w) := by
    dsimp [w, a, b]
    linear_combination -(algebraMap ℚ S h) * (x - algebraMap ℚ S s) * hu
  have heq : a * (b + w) * j = x := by
    linear_combination -j * hrel + x * hj
  have hxmem : x ∈ A := heq ▸ A.mul_mem (A.mul_mem ha (A.add_mem hb hw)) hjmem
  apply top_unique
  rw [← hgen]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxmem)

noncomputable def tEquivP (s h : ℚ) (hs : s ≠ 0) (hsne : s ≠ 1)
    (hs1 : s + 1 ≠ 0) (hh : h ≠ 0) (hrel : h * (s + 1) = s - 1) :
    AdjoinRoot (tPoly (h ^ 2)) ≃ₐ[ℚ] AdjoinRoot (pPoly s) := by
  have hp0 : pPoly s ≠ 0 := by
    intro hz
    have := pPoly_degree s
    simp [hz] at this
  have ht0 : tPoly (h ^ 2) ≠ 0 := by
    intro hz
    have := tPoly_degree (h ^ 2)
    simp [hz] at this
  have : Module.Finite ℚ (AdjoinRoot (pPoly s)) := (AdjoinRoot.powerBasis hp0).finite
  have : Module.Finite ℚ (AdjoinRoot (tPoly (h ^ 2))) := (AdjoinRoot.powerBasis ht0).finite
  let x := AdjoinRoot.root (pPoly s)
  have hx : aeval x (pPoly s) = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have heval : (pPoly s).eval (-s) ≠ 0 := by
    have heq : (pPoly s).eval (-s) = P s (-s) := by simp [pPoly, P]
    rw [heq, P_at_neg_s]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hs))
      (pow_ne_zero 4 (sub_ne_zero.mpr hsne))
  have hunit : IsUnit (x + algebraMap ℚ (AdjoinRoot (pPoly s)) s) := by
    simpa using isUnit_sub_of_aeval_eq_zero (pPoly s) x (-s) hx heval
  let u := Classical.choose (isUnit_iff_exists_inv.mp hunit)
  have hu : (x + algebraMap ℚ (AdjoinRoot (pPoly s)) s) * u = 1 :=
    Classical.choose_spec (isUnit_iff_exists_inv.mp hunit)
  let w := algebraMap ℚ (AdjoinRoot (pPoly s)) h *
    (x - algebraMap ℚ (AdjoinRoot (pPoly s)) s) * u
  have hw : aeval w (tPoly (h ^ 2)) = 0 := by
    rw [aeval_tPoly, map_pow]
    exact mobius_root s h hrel hs1 x u hu ((aeval_pPoly s x).symm ▸ hx)
  let φ : AdjoinRoot (tPoly (h ^ 2)) →ₐ[ℚ] AdjoinRoot (pPoly s) :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ _) w hw
  have hsurj : Function.Surjective φ := by
    have hgen := adjoin_mobius s h hs hh x u hu AdjoinRoot.adjoinRoot_eq_top
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hgen
    intro z
    obtain ⟨p, hp⟩ := hgen z
    exact ⟨AdjoinRoot.mk _ p, hp⟩
  apply AlgEquiv.ofBijective φ
  apply OrzechProperty.bijective_of_surjective_of_finrank_le φ.toLinearMap hsurj
  change Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {tPoly (h ^ 2)}) ≤
    Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {pPoly s})
  rw [finrank_quotient_span_eq_natDegree, finrank_quotient_span_eq_natDegree,
    tPoly_degree, pPoly_degree]

noncomputable def pEquivG (s : ℚ) (hs : s ≠ 0) (hsne : s ≠ 1) (hs1 : s + 1 ≠ 0) :
    AdjoinRoot (pPoly s) ≃ₐ[ℚ] AdjoinRoot (gPoly (((s - 1) / (s + 1)) ^ 2)) := by
  let h := (s - 1) / (s + 1)
  have hh : h ≠ 0 := div_ne_zero (sub_ne_zero.mpr hsne) hs1
  have hrel : h * (s + 1) = s - 1 := div_mul_cancel₀ _ hs1
  have hk : h ^ 2 ≠ 1 := by
    intro hz
    have heq := congrArg (fun a : ℚ => a ^ 2) hrel
    rw [mul_pow, hz, one_mul] at heq
    apply hs
    nlinarith
  exact (tEquivP s h hs hsne hs1 hh hrel).symm.trans (tEquivG (h ^ 2) hk)

theorem quadratic_factor_transfer (s : ℚ) (hs : s ≠ 0) (hsne : s ≠ 1)
    (hs1 : s + 1 ≠ 0) (D : ℚ[X]) (hD : D.natDegree = 2) (hd : D ∣ pPoly s) :
    ∃ E : ℚ[X], E ∣ gPoly (((s - 1) / (s + 1)) ^ 2) ∧ E.natDegree = 2 := by
  have hd0 : D ≠ 0 := by
    intro hz
    simp [hz] at hD
  obtain ⟨E, hE, hdeg⟩ := factor_degree_transfer _ _ D hd hd0 (pEquivG s hs hsne hs1).symm
  exact ⟨E, hE, hdeg.trans hD⟩

#print axioms tEquivG
#print axioms tEquivP
#print axioms pEquivG
#print axioms quadratic_factor_transfer
end NumberTheoryResearch.BatchA.Cuboid
