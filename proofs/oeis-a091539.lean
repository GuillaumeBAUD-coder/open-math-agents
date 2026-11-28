import OMAStatements.S_oeis_a091539
import Mathlib

-- Original Lean proof by @treybeathard-jpg.

open OMA.S_oeis_a091539 in
theorem OMA.solution : type_of% @OMA.S_oeis_a091539.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have d (m : ℕ) : 6 * rescaled (m+2) = numerator (m+2) := Int.mul_ediv_cancel' (by
    obtain ⟨u, hu⟩ : (2:ℤ) ∣ q (m+2) := (by norm_num : (2:ℤ) ∣ 3*((1:ℕ):ℤ)+1).trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))
    obtain ⟨v, hv⟩ : (2:ℤ) ∣ (m+2).factorial := mod_cast Nat.dvd_factorial two_pos (by omega)
    exact ⟨3^(m+1)*v - u, by rw [numerator, hu, hv]; ring⟩)
  have e (m : ℕ) : 10 * factor (m+2) = block (m+2) := Int.mul_ediv_cancel' (by
    simp [block, Finset.prod_range_succ', mul_assoc])
  have scaled (m : ℕ) : 60 * a (m+2) = block (m+2) * numerator (m+2) := by
    rw [← e m, ← d m, a]
    ring
  simp only [Nat.reduceSubDiff]
  refine mul_left_cancel₀ (by norm_num : (60:ℤ) ≠ 0) ?_
  simp only [mul_sub, mul_add, mul_left_comm (60 : ℤ), mul_zero,
    scaled (k+2), scaled (k+1), scaled k]
  simp [numerator, block, q, Finset.prod_range_succ, Nat.factorial_succ]
  ring
