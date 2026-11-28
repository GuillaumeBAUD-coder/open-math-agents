import OMAStatements.S_oeis_a103910
import Mathlib

/-!
# A103910: the second claim fails at `n = 2`, `k = 1`

The leading `3 × 3` block of the Fibonomial triangle is `[1, 0, 0; 1, 1, 0; 1, 1, 1]`, with inverse
`[1, 0, 0; -1, 1, 0; 0, -1, 1]`, so `T(3, 2) = -1` (as in the data of the entry). The second claim
at `n = 2`, `k = 1` says `T(3, 2) = A010048(2, 1) * T(1, 1) = 1 * 1 = 1`. Hence the conjunction
is false.
-/

namespace A103910Disproof

open OMA.S_oeis_a103910

theorem inv3 : (fibMatrix 3)⁻¹ = !![1, 0, 0; -1, 1, 0; 0, -1, 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibMatrix, fibonomial, Matrix.mul_apply, Fin.sum_univ_three, Finset.prod_range_succ]

theorem inv1 : (fibMatrix 1)⁻¹ = !![1] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i; fin_cases j
  simp [fibMatrix, fibonomial, Matrix.mul_apply]

theorem T32 : T 3 2 = -1 := by
  have h : (1 : ℕ) ≤ 2 ∧ 2 ≤ 3 := by omega
  rw [T, dif_pos h, inv3]
  rfl

theorem T11 : T 1 1 = 1 := by
  have h : (1 : ℕ) ≤ 1 ∧ 1 ≤ 1 := by omega
  rw [T, dif_pos h, inv1]
  rfl

theorem fib21 : fibonomial 2 1 = 1 := by
  simp [fibonomial]

end A103910Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103910.main) := by
  intro h
  have h2 := h.2 2 1 (by norm_num) (by norm_num)
  have e : (2 : ℕ) + 1 = 3 := rfl
  have e' : (2 : ℕ) + 1 - 1 = 2 := rfl
  rw [e', e, A103910Disproof.T32, A103910Disproof.T11, A103910Disproof.fib21] at h2
  norm_num at h2
