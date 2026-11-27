import OMAStatements.S_oeis_a134119
import Mathlib

-- Proof: floor((k+10)^2/10) = floor(k^2/10) + 2k + 10 for every integer k, so a(n+10) = a(n) + 2
-- for every n, which kills every coefficient of index at least 11; the first eleven coefficients
-- are computed directly.

namespace OMA.P_oeis_a134119
open OMA.S_oeis_a134119 PowerSeries

lemma shift (k : ℤ) : ⌊((k : ℚ) + 10) ^ 2 / 10⌋ = ⌊(k : ℚ) ^ 2 / 10⌋ + (2 * k + 10) := by
  have : ((k : ℚ) + 10) ^ 2 / 10 = (k : ℚ) ^ 2 / 10 + ((2 * k + 10 : ℤ) : ℚ) := by
    push_cast; ring
  rw [this, Int.floor_add_intCast]

lemma per (n : ℕ) : a (n + 10) = a n + 2 := by
  unfold a
  have h1 := shift (n : ℤ)
  have h2 := shift ((n : ℤ) - 1)
  push_cast at h1 h2 ⊢
  rw [show (n : ℚ) + 10 - 1 = ((n : ℚ) - 1) + 10 by ring, h1, h2]
  ring

lemma small (n : ℕ) (h : n < 11) :
    a n = if n < 4 then 0 else if n < 8 then 1 else 2 := by
  interval_cases n <;> norm_num [a, Int.floor_eq_iff]

end OMA.P_oeis_a134119

open OMA.P_oeis_a134119 in
theorem OMA.solution : type_of% @OMA.S_oeis_a134119.main := by
  open OMA.S_oeis_a134119 PowerSeries in
  ext n
  rw [mul_comm]
  have hD : (X ^ 11 - X ^ 10 - X + 1 : ℤ⟦X⟧) = 1 - X ^ 1 - X ^ 10 + X ^ 11 := by ring
  have hN : (X ^ 4 * (X ^ 4 + 1) : ℤ⟦X⟧) = X ^ 4 + X ^ 8 := by ring
  rw [hD, hN]
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases h : n < 11
  · interval_cases n <;> simp [small]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    simp only [if_pos (show 1 ≤ m + 11 by omega), if_pos (show 10 ≤ m + 11 by omega),
      if_pos (show 11 ≤ m + 11 by omega), if_neg (show m + 11 ≠ 4 by omega),
      if_neg (show m + 11 ≠ 8 by omega),
      show m + 11 - 1 = m + 10 by omega, show m + 11 - 10 = m + 1 by omega,
      show m + 11 - 11 = m by omega, show m + 11 = (m + 1) + 10 by omega, per]
    ring
