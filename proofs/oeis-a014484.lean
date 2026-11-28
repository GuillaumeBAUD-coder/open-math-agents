import OMAStatements.S_oeis_a014484
import Mathlib

open OMA.S_oeis_a014484 in
lemma OMA.ha (k : ℕ) : (a k : ℤ) * 6 = ((k + 2).factorial * (2 * k + 3) * 2 ^ k : ℕ) := by
  have h : 6 ∣ (k + 2).factorial * (2 * k + 3) * 2 ^ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Nat.factorial_dvd_factorial (show 3 ≤ k + 2 by omega)) _) _
  simp only [a]
  exact_mod_cast Nat.div_mul_cancel h

theorem OMA.solution : type_of% @OMA.S_oeis_a014484.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have h0 := OMA.ha m
  have h1 := OMA.ha (m + 1)
  have h2 := OMA.ha (m + 2)
  rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ] at h1
  rw [show m + 2 + 2 = ((m + 2) + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ] at h2
  push_cast at h0 h1 h2
  have : ((m + 2).factorial : ℤ) * 2 ^ m * 6 ≠ 0 := by positivity
  push_cast
  apply mul_right_cancel₀ (show (6 : ℤ) ≠ 0 by norm_num)
  linear_combination h2 + (-2 * ((m:ℤ) + 2) - 9) * h1 + 6 * ((m:ℤ) + 2 + 1) * h0
