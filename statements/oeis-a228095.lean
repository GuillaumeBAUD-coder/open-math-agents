import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace OMA.S_oeis_a228095

/-- The `p × p` Legendre-symbol matrix with `(i, j)`-entry `((i^2 + 3*i*j + 3*j^2) / p)`
for `i, j ∈ Fin p`. -/
def sunMatrix (p : ℕ) [Fact p.Prime] : Matrix (Fin p) (Fin p) ℤ :=
  Matrix.of (fun i j => legendreSym p ((i.val : ℤ) ^ 2 + 3 * (i.val : ℤ) * (j.val : ℤ) + 3 * (j.val : ℤ) ^ 2))

/-- OEIS A228095 (Zhi-Wei Sun) Conjecture: for every prime `p ≡ 5 (mod 6)`,
the determinant of the `p × p` matrix `[((i^2 + 3*i*j + 3*j^2) / p)]_{0 ≤ i, j < p}` equals `0`. -/
theorem main :
    ∀ (p : ℕ) [Fact p.Prime], p % 6 = 5 → (sunMatrix p).det = 0 := by
  sorry

end OMA.S_oeis_a228095
