import OMAStatements.S_mo_473367

open Finset Matrix OMA.S_mo_473367

-- David Roberson gave this signed triangle in MathOverflow 473367.
-- A triangle with one negative edge has nonnegative cuts, but its
-- Laplacian is negative in the direction separating the endpoints of that edge.
private def weights : Matrix (Fin 3) (Fin 3) ℤ := !![0, -1, 1; -1, 0, 1; 1, 1, 0]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_473367.main) := by
  intro h
  have hcut : ∀ S : Finset (Fin 3), S.Nonempty → S ≠ univ →
      0 ≤ ∑ i ∈ S, ∑ j ∈ univ \ S, weights i j := by decide
  have hsym : ∀ i j, weights i j = weights j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  have hsign : ∀ i j, i ≠ j → weights i j = -1 ∨ weights i j = 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  have hL : Laplacian weights = !![0, 1, -1; 1, 0, -1; -1, -1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hh := h 3 weights (by decide) hsym hsign hcut ![1, -1, 0]
  norm_num [quadraticForm, hL, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hh
