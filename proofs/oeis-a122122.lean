import OMAStatements.S_oeis_a122122
import Mathlib

/-!
For j ≥ 0, a(j+1) = (j+3) 4^(j+1) / 8 - (4j+1)/2 * binomial(2j, j), using
(j+1) binomial(2j+2, j+1) = 2(2j+1) binomial(2j, j). Substituting this closed form and the same
central binomial relation, both recurrences become rational identities in n, 4^n and
binomial(2n, n).
-/

namespace R122122
open OMA.S_oeis_a122122

theorem cbq (k j : ℕ) (h : k = j + 1) :
    ((2 * k).choose k : ℚ) = 2 * (2 * j + 1) / (j + 1) * ((2 * j).choose j : ℚ) := by
  subst h
  have h := Nat.succ_mul_centralBinom_succ j
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have hq : ((j : ℚ) + 1) * ((2 * (j + 1)).choose (j + 1) : ℚ) =
      2 * (2 * j + 1) * ((2 * j).choose j : ℚ) := by exact_mod_cast h
  have hj : (j : ℚ) + 1 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hj]
  linear_combination hq

theorem aform (k j : ℕ) (h : k = j + 1) :
    a k = ((j : ℚ) + 3) * 4 ^ (j + 1) / 8 - (4 * (j : ℚ) + 1) / 2 * ((2 * j).choose j : ℚ) := by
  subst h
  unfold a
  rw [if_neg (show j + 1 ≠ 0 by omega)]
  have hz : (4 : ℚ) ^ (((j + 1 : ℕ) : ℤ) - 2) = 4 ^ (j + 1) / 16 := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast]
    norm_num
  rw [hz, cbq (j + 1) j rfl]
  push_cast
  have h1 : (1 : ℚ) - 2 * ((j : ℚ) + 1) ≠ 0 := by
    have : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    intro h
    linarith
  field_simp
  ring

end R122122

theorem OMA.solution : type_of% @OMA.S_oeis_a122122.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, R122122.aform (m + 2 + 1) (m + 2) rfl,
      R122122.aform (m + 2) (m + 1) rfl, R122122.aform (m + 1) m rfl,
      R122122.cbq (m + 2) (m + 1) rfl, R122122.cbq (m + 1) m rfl]
    push_cast
    field_simp
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, R122122.aform (m + 4 + 1) (m + 4) rfl,
      R122122.aform (m + 4) (m + 3) rfl, R122122.aform (m + 3) (m + 2) rfl,
      R122122.aform (m + 2) (m + 1) rfl, R122122.aform (m + 1) m rfl,
      R122122.cbq (m + 4) (m + 3) rfl, R122122.cbq (m + 3) (m + 2) rfl,
      R122122.cbq (m + 2) (m + 1) rfl, R122122.cbq (m + 1) m rfl]
    push_cast
    field_simp
    ring
