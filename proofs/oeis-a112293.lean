import OMAStatements.S_oeis_a112293

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: since (2m+1)!! = (2m+1) * (2m-1)!!, splitting off the last term of the sum gives
-- a (m+1) = (2m+1) * a m + 1. Using this for m = k+1 and m = k, the left side of Mathar's
-- recurrence at n = k+2 is a linear combination of the two identities, hence 0. No computer search.

namespace OMA.P_oeis_a112293

open OMA.S_oeis_a112293

theorem df_succ (m : ℕ) :
    ((2 * (m + 1) - 1).doubleFactorial : ℚ) = (2 * (m : ℚ) + 1) * ((2 * m - 1).doubleFactorial : ℚ) := by
  cases m with
  | zero => norm_num
  | succ j =>
    have h1 : 2 * (j + 1 + 1) - 1 = (2 * j + 1) + 2 := by omega
    have h2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [h1, h2, Nat.doubleFactorial_add_two]
    push_cast
    ring

theorem df_pos (m : ℕ) : ((m.doubleFactorial : ℕ) : ℚ) ≠ 0 := by
  have := Nat.doubleFactorial_pos m
  positivity

theorem step (m : ℕ) : a (m + 1) = (2 * (m : ℚ) + 1) * a m + 1 := by
  unfold a
  rw [Finset.sum_range_succ, div_self (df_pos _), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [df_succ]
  ring

theorem solution : ∀ n : ℕ, 2 ≤ n →
    a n - 2 * (n : ℚ) * a (n - 1) + (2 * (n : ℚ) - 3) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h1 : k + 2 - 1 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2]
  have hA := step (k + 1)
  have hB := step k
  push_cast at hA hB ⊢
  linear_combination hA - hB

end OMA.P_oeis_a112293

theorem OMA.solution : type_of% @OMA.S_oeis_a112293.main := OMA.P_oeis_a112293.solution
