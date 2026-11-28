import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

namespace OMA.S_oeis_a005103

/-- A symmetric `n × n` integer Gram matrix of a positive-definite integral lattice of minimal
nonzero norm `3` (for `n = 0`, the trivial 0-dimensional lattice has determinant `1`). -/
def IsNorm3Gram (n : ℕ) (G : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j : Fin n, G i j = G j i) ∧
  0 < G.det ∧
  (∀ v : Fin n → ℤ, v ≠ 0 → 3 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * G i j * v j) ∧
  (n = 0 ∨ ∃ v : Fin n → ℤ, v ≠ 0 ∧ ∑ i : Fin n, ∑ j : Fin n, v i * G i j * v j = 3)

/-- OEIS A005103: minimal determinant of an `n`-dimensional integral positive-definite lattice
of minimum norm `3` (`a(0)=1, a(1)=3, a(2)=8, a(3)=16, a(4)=32, a(5)=48, a(6)=64, a(7)=64, ...`). -/
noncomputable def a005103 (n : ℕ) : ℕ :=
  sInf {d : ℕ | ∃ G : Matrix (Fin n) (Fin n) ℤ, IsNorm3Gram n G ∧ G.det = (d : ℤ)}

/-- Simon Plouffe's 1992 conjectured generating function for OEIS A005103:
`∑_{n ≥ 0} a(n) z^n = (1 + z + 2 z^2 + 2 z^3 + 6 z^4) / (1 - 2 z + 2 z^3)`,
equivalently `(1 - 2 z + 2 z^3) * ∑_{n ≥ 0} a(n) z^n = 1 + z + 2 z^2 + 2 z^3 + 6 z^4`. -/
theorem main :
    ((1 : PowerSeries ℤ) - 2 * PowerSeries.X + 2 * PowerSeries.X ^ 3) *
      PowerSeries.mk (fun n => (a005103 n : ℤ)) =
      1 + PowerSeries.X + 2 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 4 := by
  sorry

end OMA.S_oeis_a005103
