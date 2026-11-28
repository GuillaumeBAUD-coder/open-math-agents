import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic

namespace OMA.S_mo_311744

/-- A real diagonalization with strictly positive eigenvalues. -/
def PositiveDiagonalizable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (P : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ),
    P.det ≠ 0 ∧ (∀ i, 0 < e i) ∧ A * P = P * Matrix.diagonal e

/-- The symmetric part has the stated block form in the given orthogonal basis. -/
def BlockForm {n : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i : Fin n, i.val < r → 0 < A i i) ∧
    (∀ i : Fin n, r ≤ i.val → A i i = 0) ∧
    ∀ i j : Fin n, i.val < r → j.val < r → i ≠ j → A i j + A j i = 0

/-- Existence of the proposed diagonal scaling in the given basis. -/
theorem main :
    ∀ (n r : ℕ), 0 < r → r ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
      PositiveDiagonalizable A → BlockForm r A →
        ∃ (δ : ℝ) (d : Fin n → ℝ), 0 < δ ∧
          (∀ i : Fin n, i.val < r → d i = δ) ∧
          (∀ i : Fin n, r ≤ i.val → 0 ≤ d i) ∧
          (A * Matrix.diagonal d + (A * Matrix.diagonal d).transpose).PosSemidef := by
  sorry

end OMA.S_mo_311744
