import Mathlib

/- Exact identities supporting ODD_ODD_PROOF.md.
   These lemmas do not assert the full second cuboid conjecture. -/
namespace NumberTheoryResearch.BatchA.Cuboid

section RingIdentities
variable {R : Type*} [CommRing R]

def P (s x : R) : R :=
  x ^ 5 + (2 + s) * (3 - 2 * s) * x ^ 4
    + (1 + 10 * s + 4 * s ^ 2 - 14 * s ^ 3 + s ^ 4) * x ^ 3
    - s * (1 - 14 * s + 4 * s ^ 2 + 10 * s ^ 3 + s ^ 4) * x ^ 2
    - s ^ 3 * (1 + 2 * s) * (-2 + 3 * s) * x - s ^ 5

def T (k w : R) : R := w * (w ^ 2 - 1) ^ 2 + 4 * (1 - k) * (w ^ 2 - k)

def G (k v : R) : R := v ^ 5 + v ^ 4 - 2 * v ^ 3 - 2 * v ^ 2 + 2 - 2 * k

def TH (k a b : R) : R :=
  a * (a ^ 2 - b ^ 2) ^ 2 + 4 * (1 - k) * (a ^ 2 - k * b ^ 2) * b ^ 3

theorem TH_one (k a : R) : TH k a 1 = T k a := by unfold TH T; ring

theorem TH_scale (k a b z : R) : TH k (a * z) (b * z) = TH k a b * z ^ 5 := by
  unfold TH
  ring

theorem TH_inverse (k a b u : R) (hu : b * u = 1) :
    TH k a b = T k (a * u) * b ^ 5 := by
  have h : a * u * b = a := by calc
    a * u * b = a * (b * u) := by ring
    _ = a := by rw [hu, mul_one]
  have ht := TH_scale k (a * u) 1 b
  rw [h, one_mul, TH_one] at ht
  exact ht

theorem P_at_neg_s (s : R) : P s (-s) = -2 * s ^ 3 * (s - 1) ^ 4 := by
  unfold P
  ring

theorem T_at_h (h : R) : T (h ^ 2) h = h * (h - 1) ^ 2 * (h + 1) ^ 2 := by
  unfold T
  ring

theorem T_at_one (k : R) : T k 1 = 4 * (k - 1) ^ 2 := by
  unfold T
  ring

theorem T_at_neg_one (k : R) : T k (-1) = 4 * (k - 1) ^ 2 := by
  unfold T
  ring

theorem T_comp (k v : R) : T k (1 - v ^ 2) = G k v * G k (-v) := by
  unfold T G
  ring

theorem G_denominator (k v : R) :
    G k v = v ^ 2 * (v ^ 2 - 2) * (v + 1) + 2 * (1 - k) := by
  unfold G
  ring

theorem T_denominator (k w : R) :
    T k w = (w ^ 2 - 1) * (w * (w ^ 2 - 1) + 4 * (1 - k))
      + 4 * (1 - k) ^ 2 := by
  unfold T
  ring

theorem inverse_v_cleared (k v : R) :
    2 * k - 1 - (1 - v ^ 2) ^ 2 - v * ((1 - v ^ 2) ^ 2 - 1) = -G k v := by
  unfold G
  ring

theorem inverse_w_cleared (k w : R) :
    (1 - w) * (w ^ 2 - 1) ^ 2 - (2 * k - 1 - w ^ 2) ^ 2 = -T k w := by
  unfold T
  ring

theorem quadratic_remainder (k v A B : R) :
    G k v = (v ^ 2 - A * v + B) *
      (v ^ 3 + (A + 1) * v ^ 2 + (A ^ 2 + A - B - 2) * v
        + A ^ 3 + A ^ 2 - 2 * A * B - 2 * A - B - 2)
      + (B ^ 2 - (3 * A ^ 2 + 2 * A - 2) * B + A * (A + 1) * (A ^ 2 - 2)) * v
      + B * ((2 * A + 1) * B - (A + 1) * (A ^ 2 - 2)) + 2 - 2 * k := by
  unfold G
  ring

theorem quadratic_discriminant (A : R) :
    (3 * A ^ 2 + 2 * A - 2) ^ 2 - 4 * A * (A + 1) * (A ^ 2 - 2)
      = 5 * A ^ 4 + 8 * A ^ 3 + 4 := by ring

theorem square_cover (A c : R) :
    let B := A ^ 2 + A - 2 - 2 * A * c ^ 2
    B ^ 2 - (3 * A ^ 2 + 2 * A - 2) * B + A * (A + 1) * (A ^ 2 - 2)
      = A * (4 * A * c ^ 4 + (2 * A ^ 2 + 4) * c ^ 2 - A ^ 3 - 2 * A ^ 2 + A) := by
  dsimp
  ring

theorem T_homogeneous_relation (s h x : R) (hs : h * (s + 1) = s - 1) :
    (s + 1) ^ 4 * TH (h ^ 2) (h * (x - s)) (x + s) = 16 * s ^ 2 * h * P s x := by
  unfold TH P
  linear_combination (-h ^ 4 * s ^ 8 + 5 * h ^ 4 * s ^ 7 * x - 3 * h ^ 4 * s ^ 7 - 10 * h ^ 4 * s ^ 6 * x ^ 2 + 15 * h ^ 4 * s ^ 6 * x - 3 * h ^ 4 * s ^ 6 + 10 * h ^ 4 * s ^ 5 * x ^ 3 - 30 * h ^ 4 * s ^ 5 * x ^ 2 + 15 * h ^ 4 * s ^ 5 * x - h ^ 4 * s ^ 5 - 5 * h ^ 4 * s ^ 4 * x ^ 4 + 30 * h ^ 4 * s ^ 4 * x ^ 3 - 30 * h ^ 4 * s ^ 4 * x ^ 2 + 5 * h ^ 4 * s ^ 4 * x + h ^ 4 * s ^ 3 * x ^ 5 - 15 * h ^ 4 * s ^ 3 * x ^ 4 + 30 * h ^ 4 * s ^ 3 * x ^ 3 - 10 * h ^ 4 * s ^ 3 * x ^ 2 + 3 * h ^ 4 * s ^ 2 * x ^ 5 - 15 * h ^ 4 * s ^ 2 * x ^ 4 + 10 * h ^ 4 * s ^ 2 * x ^ 3 + 3 * h ^ 4 * s * x ^ 5 - 5 * h ^ 4 * s * x ^ 4 + h ^ 4 * x ^ 5 - h ^ 3 * s ^ 8 + 21 * h ^ 3 * s ^ 7 * x - h ^ 3 * s ^ 7 + 38 * h ^ 3 * s ^ 6 * x ^ 2 + 53 * h ^ 3 * s ^ 6 * x + h ^ 3 * s ^ 6 + 58 * h ^ 3 * s ^ 5 * x ^ 3 + 134 * h ^ 3 * s ^ 5 * x ^ 2 + 43 * h ^ 3 * s ^ 5 * x + h ^ 3 * s ^ 5 + 11 * h ^ 3 * s ^ 4 * x ^ 4 + 154 * h ^ 3 * s ^ 4 * x ^ 3 + 154 * h ^ 3 * s ^ 4 * x ^ 2 + 11 * h ^ 3 * s ^ 4 * x + h ^ 3 * s ^ 3 * x ^ 5 + 43 * h ^ 3 * s ^ 3 * x ^ 4 + 134 * h ^ 3 * s ^ 3 * x ^ 3 + 58 * h ^ 3 * s ^ 3 * x ^ 2 + h ^ 3 * s ^ 2 * x ^ 5 + 53 * h ^ 3 * s ^ 2 * x ^ 4 + 38 * h ^ 3 * s ^ 2 * x ^ 3 - h ^ 3 * s * x ^ 5 + 21 * h ^ 3 * s * x ^ 4 - h ^ 3 * x ^ 5 + h ^ 2 * s ^ 8 + 19 * h ^ 2 * s ^ 7 * x + 7 * h ^ 2 * s ^ 7 + 34 * h ^ 2 * s ^ 6 * x ^ 2 + 5 * h ^ 2 * s ^ 6 * x + 7 * h ^ 2 * s ^ 6 + 62 * h ^ 2 * s ^ 5 * x ^ 3 + 46 * h ^ 2 * s ^ 5 * x ^ 2 - 27 * h ^ 2 * s ^ 5 * x + h ^ 2 * s ^ 5 + 13 * h ^ 2 * s ^ 4 * x ^ 4 + 50 * h ^ 2 * s ^ 4 * x ^ 3 - 50 * h ^ 2 * s ^ 4 * x ^ 2 - 13 * h ^ 2 * s ^ 4 * x - h ^ 2 * s ^ 3 * x ^ 5 + 27 * h ^ 2 * s ^ 3 * x ^ 4 - 46 * h ^ 2 * s ^ 3 * x ^ 3 - 62 * h ^ 2 * s ^ 3 * x ^ 2 - 7 * h ^ 2 * s ^ 2 * x ^ 5 - 5 * h ^ 2 * s ^ 2 * x ^ 4 - 34 * h ^ 2 * s ^ 2 * x ^ 3 - 7 * h ^ 2 * s * x ^ 5 - 19 * h ^ 2 * s * x ^ 4 - h ^ 2 * x ^ 5 + h * s ^ 8 + 3 * h * s ^ 7 * x + 5 * h * s ^ 7 - 14 * h * s ^ 6 * x ^ 2 - 81 * h * s ^ 6 * x - 5 * h * s ^ 6 + 14 * h * s ^ 5 * x ^ 3 - 166 * h * s ^ 5 * x ^ 2 - 47 * h * s ^ 5 * x - h * s ^ 5 - 3 * h * s ^ 4 * x ^ 4 - 218 * h * s ^ 4 * x ^ 3 - 218 * h * s ^ 4 * x ^ 2 - 3 * h * s ^ 4 * x - h * s ^ 3 * x ^ 5 - 47 * h * s ^ 3 * x ^ 4 - 166 * h * s ^ 3 * x ^ 3 + 14 * h * s ^ 3 * x ^ 2 - 5 * h * s ^ 2 * x ^ 5 - 81 * h * s ^ 2 * x ^ 4 - 14 * h * s ^ 2 * x ^ 3 + 5 * h * s * x ^ 5 + 3 * h * s * x ^ 4 + h * x ^ 5) * hs

end RingIdentities

section FieldIdentities
variable {K : Type*} [Field K]

theorem P_to_T (h w : K) (hh : 1 - h ≠ 0) (hw : h - w ≠ 0) :
    P ((1 + h) / (1 - h)) (((1 + h) / (1 - h)) * (h + w) / (h - w))
      = 32 * h ^ 4 * (h + 1) ^ 3 * T (h ^ 2) w / ((h - w) ^ 5 * (1 - h) ^ 7) := by
  unfold P T
  field_simp
  ring

end FieldIdentities

#print axioms P_at_neg_s
#print axioms T_comp
#print axioms inverse_v_cleared
#print axioms inverse_w_cleared
#print axioms quadratic_remainder
#print axioms square_cover
#print axioms P_to_T

end NumberTheoryResearch.BatchA.Cuboid
