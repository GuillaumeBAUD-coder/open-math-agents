import OMAStatements.S_oeis_a103910
import Mathlib

namespace OMA.A103910Proof

open OMA.S_oeis_a103910

lemma fibMatrix_one : fibMatrix 1 = !![1] := by
  ext i j
  fin_cases i; fin_cases j
  simp [fibMatrix, fibonomial]

lemma fibMatrix_three : fibMatrix 3 = !![1, 0, 0; 1, 1, 0; 1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fibMatrix, fibonomial, Finset.prod_range_succ]

lemma inv_one : (fibMatrix 1)⁻¹ = !![1] := by
  apply Matrix.inv_eq_left_inv
  rw [fibMatrix_one]
  ext i j
  fin_cases i; fin_cases j
  simp

lemma inv_three : (fibMatrix 3)⁻¹ = !![1, 0, 0; -1, 1, 0; 0, -1, 1] := by
  apply Matrix.inv_eq_left_inv
  rw [fibMatrix_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma T11 : T 1 1 = 1 := by
  simp only [T, le_refl, and_self, dite_true, inv_one]
  rfl

lemma T32 : T 3 2 = -1 := by
  simp [T, inv_three]

lemma fib21 : fibonomial 2 1 = 1 := by
  simp [fibonomial]

theorem main_disproof :
    ¬ ((∀ n : ℕ, 2 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = 0) ∧
      (∀ n k : ℕ, 1 < n → 1 ≤ k → T (n + k) n = fibonomial (n + k - 1) k * T k 1)) := by
  rintro ⟨-, h⟩
  have := h 2 1 (by norm_num) le_rfl
  norm_num [T11, T32, fib21] at this

end OMA.A103910Proof

open OMA.A103910Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103910.main) := main_disproof
