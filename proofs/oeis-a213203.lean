import OMAStatements.S_oeis_a213203
import Mathlib

open OMA.S_oeis_a213203 in
theorem OMA.solution : type_of% @OMA.S_oeis_a213203.main := by
  have T (n N : ℕ) : 2 * (∑ k ∈ Finset.Icc 1 N, if n ∣ k then -(k : ℤ) else (k : ℤ)) =
      N * (N + 1) - 2 * n * (N / n : ℕ) * ((N / n : ℕ) + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      by_cases h : n ∣ N + 1
      · have hq : (((N / n : ℕ) : ℤ) + 1) * n = N + 1 :=
          mod_cast (by rw [← Nat.succ_div_of_dvd h]; exact Nat.div_mul_cancel h)
        simp only [h, ↓reduceIte, Nat.succ_div_of_dvd h, Nat.cast_add, Nat.cast_one]
        linear_combination 4 * hq
      · simp only [h, ↓reduceIte, Nat.succ_div_of_not_dvd h, Nat.cast_add, Nat.cast_one]
        ring
  have A (k : ℕ) : 2 * a (k + 1) = (k + 1) * k.factorial * ((k - 1) * k.factorial - 1) := by
    have h := T (k + 1) (k + 1).factorial
    rw [Nat.factorial_succ, Nat.mul_div_cancel_left _ k.succ_pos] at h
    rw [a, Nat.factorial_succ, h]
    push_cast
    ring
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h5 := A (k + 4)
  have h4 := A (k + 3)
  have h3 := A (k + 2)
  have h2 := A (k + 1)
  have h1 := A k
  simp [Nat.factorial_succ, add_assoc] at h1 h2 h3 h4 h5 ⊢
  exact mul_left_cancel₀ two_ne_zero (by
    linear_combination h5 + (-(k+5:ℤ)^2 - (k+5) - 11) * h4 + ((k+5:ℤ)^3 + 7*(k+5)^2 - 13*(k+5) + 39) * h3
      - 2*(k+3:ℤ)*(4*(k+5)^2 - 2*(k+5) - 15) * h2 + 20*(k+3:ℤ)*(k+2)*(k+1) * h1)
