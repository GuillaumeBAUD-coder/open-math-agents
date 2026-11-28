import OMAStatements.S_oeis_a337949
import Mathlib

open OMA.S_oeis_a337949 in
theorem OMA.solution : type_of% @OMA.S_oeis_a337949.main := by
  have Q : ∀ k, 2^k % 3 = if k % 2 = 0 then 1 else 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih]; split_ifs <;> omega
  have F : ∀ k, 2^(k*(k-1)/2) % 3 = if k % 4 = 0 ∨ k % 4 = 1 then 1 else 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.triangle_succ, pow_add, Nat.mul_mod, ih, Q]; split_ifs <;> omega
  have A : ∀ n, a (n+1) % 3 = ((if (n+1) % 4 = 0 ∨ (n+1) % 4 = 1 then 1 else 2) +
      if (n+2) % 4 = 0 ∨ (n+2) % 4 = 1 then 1 else 2) % 3 := by
    intro n
    rw [a, if_neg (by omega), show (n+1)*(n+1+1)/2 = (n+1+1)*(n+1+1-1)/2 by rw [mul_comm]; rfl,
      Nat.add_mod, F, F]
  intro n
  refine ⟨?_, ?_, ?_⟩ <;> rw [A] <;> split_ifs <;> omega
