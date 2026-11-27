import OMAReductions.R_OeisA24356_conjecture_R1
import Mathlib

-- Step OeisA24356.conjecture.R1.H1: hypothesis H1 of reduction OeisA24356.conjecture.R1
-- Credit: @ivillar
-- Proof follows the upstream test lemma OeisA24356.a_4 (formal-conjectures).

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := by
  unfold OMA.R_OeisA24356_conjecture_R1.H1 OeisA24356.a
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have h5 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count hp13
  have h6 : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count hp17
  have hM :
      (Matrix.of fun (i j : Fin 4) ↦ (Nat.nth Nat.Prime (i.val + j.val) : ℤ)) =
        !![(2 : ℤ), 3, 5, 7; 3, 5, 7, 11; 5, 7, 11, 13; 7, 11, 13, 17] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
        Nat.nth_prime_four_eq_eleven, h5, h6]
  rw [hM]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (v := ![(6 : ℤ), -3, -2, 1]) (i := 0)
  · decide
  · norm_num [nonZeroDivisors]
