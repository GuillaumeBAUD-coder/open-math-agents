import Mathlib

namespace OMA.S_wp_grothendieck_katz_p_curvature_conjecture

open Filter NumberField IsDedekindDomain
open scoped BigOperators Polynomial

/-- Formal differentiation of a rational function over its constant field. -/
noncomputable def rationalDerivative {F : Type*} [Field F] (f : RatFunc F) :
    RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F)
    (f.num.derivative * f.denom - f.num * f.denom.derivative) /
      (algebraMap (Polynomial F) (RatFunc F) f.denom) ^ 2

/-- A coefficient matrix obtained from polynomial numerators and a common denominator. -/
noncomputable def systemMatrix {R F : Type*} [CommRing R] [Field F] {n : ℕ}
    (map : R →+* F) (num : Matrix (Fin n) (Fin n) (Polynomial R)) (den : Polynomial R) :
    Matrix (Fin n) (Fin n) (RatFunc F) :=
  fun i j => algebraMap (Polynomial F) (RatFunc F) ((num i j).map map) /
    algebraMap (Polynomial F) (RatFunc F) (den.map map)

/-- The connection in the independent-variable direction for the equation y' = A y. -/
noncomputable def connection {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RatFunc F)) (y : Fin n → RatFunc F) :
    Fin n → RatFunc F :=
  fun i => rationalDerivative (y i) - ∑ j, A i j * y j

/-- The denominator survives reduction and the reduced connection has zero p-curvature. -/
def goodAt {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (num : Matrix (Fin n) (Fin n) (Polynomial (𝓞 K))) (den : Polynomial (𝓞 K))
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let red := Ideal.Quotient.mk v.asIdeal
  den.map red ≠ 0 ∧
    ∀ y : Fin n → RatFunc (𝓞 K ⧸ v.asIdeal),
      Nat.iterate (connection (systemMatrix red num den))
        (ringChar (𝓞 K ⧸ v.asIdeal)) y = 0

/-- An invertible fundamental solution matrix in a finite algebraic differential extension. -/
def algebraicSolutions {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RatFunc K)) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Algebra (RatFunc K) L)
    (_ : IsScalarTower K (RatFunc K) L),
    FiniteDimensional (RatFunc K) L ∧
      ∃ D : Derivation K L L,
        (∀ f : RatFunc K, D (algebraMap (RatFunc K) L f) =
          algebraMap (RatFunc K) L (rationalDerivative f)) ∧
        ∃ Y : Matrix (Fin n) (Fin n) L, Y.det ≠ 0 ∧
          ∀ i j, D (Y i j) = ∑ k, algebraMap (RatFunc K) L (A i k) * Y k j

/-- The Grothendieck–Katz p-curvature conjecture for linear ordinary systems
with rational-function coefficients over number fields. -/
theorem main :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
      (num : Matrix (Fin n) (Fin n) (Polynomial (𝓞 K))) (den : Polynomial (𝓞 K)),
      0 < n → den ≠ 0 →
      (∀ᶠ v in cofinite, goodAt num den v) →
      algebraicSolutions (systemMatrix (algebraMap (𝓞 K) K) num den) := by
  sorry

end OMA.S_wp_grothendieck_katz_p_curvature_conjecture
