import Mathlib

namespace OMA.S_mo_57253

open Polynomial

/-- For the nonprincipal minor obtained by deleting the second row and first
column of a positive-definite real matrix, every monic quadratic is possible. -/
theorem main :
    ∀ t d : ℝ, ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.PosDef ∧
      (M.submatrix (1 : Fin 3).succAbove (0 : Fin 3).succAbove).charpoly =
        X ^ 2 + C t * X + C d := by
  sorry

end OMA.S_mo_57253
