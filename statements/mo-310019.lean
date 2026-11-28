import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic

namespace OMA.S_mo_310019

/-- The strict quadratic Lyapunov condition for the linear system
with coefficient matrix `A`. -/
def Lyapunov {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P.PosDef ∧ (-(A.transpose * P + P * A)).PosDef

/-- A common certificate works for the sum. Independent certificates
can coexist with an unstable eigenvalue and no certificate for the sum. -/
theorem main :
    (∀ (n : ℕ) (A B P : Matrix (Fin n) (Fin n) ℝ),
      Lyapunov A P → Lyapunov B P → Lyapunov (A+B) P) ∧
    ∃ A B P Q : Matrix (Fin 2) (Fin 2) ℝ,
      Lyapunov A P ∧ Lyapunov B Q ∧
      (∃ v : Fin 2 → ℝ, v ≠ 0 ∧ (A+B).mulVec v = v) ∧
      ¬ ∃ R : Matrix (Fin 2) (Fin 2) ℝ, Lyapunov (A+B) R := by
  sorry

end OMA.S_mo_310019
