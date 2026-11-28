import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace OMA.S_oeis_a225611

/-- The `(p - 1) × (p - 1)` Legendre-symbol matrix with `(i, j)`-entry
`(((i + 1)^2 + 6*(i + 1)*(j + 1) + (j + 1)^2) / p)` for `0 ≤ i, j < p - 1`
(corresponding to indices `1, ..., p - 1`). -/
def sunMatrix (p : ℕ) [Fact p.Prime] : Matrix (Fin (p - 1)) (Fin (p - 1)) ℤ :=
  Matrix.of (fun i j =>
    legendreSym p (((i.val + 1 : ℕ) : ℤ) ^ 2 +
      6 * ((i.val + 1 : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ) +
      ((j.val + 1 : ℕ) : ℤ) ^ 2))

/-- OEIS A225611 (Zhi-Wei Sun) Conjecture: for every prime `p ≡ 3 (mod 4)`,
the determinant of the `(p - 1) × (p - 1)` matrix `[((i^2 + 6*i*j + j^2) / p)]_{1 ≤ i, j ≤ p - 1}`
equals `0`. -/
theorem main :
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → (sunMatrix p).det = 0 := by
  sorry

end OMA.S_oeis_a225611
