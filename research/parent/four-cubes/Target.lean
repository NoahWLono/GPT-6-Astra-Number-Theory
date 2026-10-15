import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FourCubesResearch

/-- Integer-valued on every integer, without requiring integral coefficients. -/
def IntegerValued (f : Polynomial ℚ) : Prop :=
  ∀ z : ℤ, ∃ w : ℤ, f.eval (z : ℚ) = (w : ℚ)

/-- An identity of rational polynomials, with four signed cubes. -/
def AffineIdentity (f : Fin 4 → Polynomial ℚ) (slope offset : ℤ) : Prop :=
  (∑ i, f i ^ 3) = Polynomial.C (slope : ℚ) * Polynomial.X +
    Polynomial.C (offset : ℚ)

/-- The subsidiary question under investigation. This definition is no proof. -/
def SlopeDivisibility : Prop :=
  ∀ (f : Fin 4 → Polynomial ℚ) (slope offset : ℤ),
    (∀ i, IntegerValued (f i)) → AffineIdentity f slope offset → 3 ∣ slope

/-- A counterexample would refute the subsidiary question. -/
def Counterexample : Prop :=
  ∃ (f : Fin 4 → Polynomial ℚ) (slope offset : ℤ),
    (∀ i, IntegerValued (f i)) ∧ AffineIdentity f slope offset ∧ ¬3 ∣ slope

end FourCubesResearch
