import OMAStatements.S_oeis_a030229
import Mathlib

open OMA.S_oeis_a030229

def B : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 0;
     -1, 1, 0, 0, 0, 0;
     -1, 0, 1, 0, 0, 0;
     0, -1, 0, 1, 0, 0;
     -1, 0, 0, 0, 1, 0;
     1, -1, -1, 0, 0, 1]

lemma MB : M 6 * B = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, B, Matrix.mul_apply, Fin.sum_univ_succ]

lemma six_mem : (6 : ℕ) ∈ A030229 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (6:ℕ) = 2 * 3 by rfl]
    exact (Nat.squarefree_mul (by norm_num)).2 ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  · rw [show (6:ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a030229.main) := by
  intro h
  have := h 6 6 six_mem le_rfl
  rw [Matrix.inv_eq_right_inv MB] at this
  simp [B] at this
  norm_num at this
