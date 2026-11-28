import OMAStatements.S_oeis_a091540
import Mathlib

open OMA.S_oeis_a091540 in
theorem OMA.solution : type_of% @OMA.S_oeis_a091540.main := by
  have e (m : ℕ) : 6 * a (m + 2) = numerator (m + 2) := by
    obtain ⟨u, hu⟩ : (2 : ℤ) ∣ q (m + 2) := dvd_trans (by norm_num)
      (Finset.dvd_prod_of_mem (fun j : ℕ => 3 * (j : ℤ) + 1) (Finset.mem_range.2 (by omega : 1 < m + 2)))
    obtain ⟨v, hv⟩ : (2 : ℤ) ∣ (m + 2).factorial := mod_cast Nat.dvd_factorial two_pos (by omega)
    exact Int.mul_ediv_cancel' ⟨3 ^ (m + 1) * v - u, by rw [numerator, hu, hv]; ring⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp only [Nat.reduceSubDiff]
  have h0 := e m
  have h1 := e (m + 1)
  have h2 := e (m + 2)
  simp only [numerator, q, Finset.prod_range_succ, Nat.factorial_succ] at h0 h1 h2
  push_cast at h0 h1 h2 ⊢
  apply mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0)
  linear_combination h2 + (-6 * ((m : ℤ) + 4) + 5) * h1 + 3 * ((m : ℤ) + 3) * (3 * m + 7) * h0
