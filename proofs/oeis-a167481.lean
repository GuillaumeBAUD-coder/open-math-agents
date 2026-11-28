import OMAStatements.S_oeis_a167481
import Mathlib

open OMA.S_oeis_a167481 in
theorem OMA.solution : type_of% @OMA.S_oeis_a167481.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have s (j : ℕ) : a (j+1) = -2 * a j + (j+1).centralBinom := by
    simp only [a, Finset.sum_range_succ _ (j+1), Finset.mul_sum, Nat.sub_self, pow_zero, one_mul,
      Nat.centralBinom]
    congr 1
    exact Finset.sum_congr rfl fun x hx => by
      rw [Nat.succ_sub (Finset.mem_range_succ_iff.1 hx), pow_succ]
      ring
  have c : ((k:ℤ)+2) * (k+2).centralBinom = 2*(2*(k+1)+1) * (k+1).centralBinom :=
    mod_cast Nat.succ_mul_centralBinom_succ (k+1)
  simp [s]
  linear_combination c
