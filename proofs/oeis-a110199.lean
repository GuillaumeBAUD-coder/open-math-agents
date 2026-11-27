import OMAStatements.S_oeis_a110199
import Mathlib

namespace OMA.P_oeis_a110199

open OMA.S_oeis_a110199

theorem key (j : ℕ) :
    ((j : ℤ) + 2) * (catalan (j + 1) : ℤ) = 2 * (2 * (j : ℤ) + 1) * (catalan j : ℤ) := by
  have h1 : (((j + 1 + 1) * catalan (j + 1) : ℕ) : ℤ) = ((Nat.centralBinom (j + 1) : ℕ) : ℤ) := by
    rw [succ_mul_catalan_eq_centralBinom]
  have h2 : (((j + 1) * catalan j : ℕ) : ℤ) = ((Nat.centralBinom j : ℕ) : ℤ) := by
    rw [succ_mul_catalan_eq_centralBinom]
  have h3 : (((j + 1) * Nat.centralBinom (j + 1) : ℕ) : ℤ)
      = ((2 * (2 * j + 1) * Nat.centralBinom j : ℕ) : ℤ) := by
    rw [Nat.succ_mul_centralBinom_succ]
  push_cast at h1 h2 h3
  apply mul_left_cancel₀ (show ((j : ℤ) + 1) ≠ 0 by positivity)
  linear_combination ((j : ℤ) + 1) * h1 + h3 - 2 * (2 * (j : ℤ) + 1) * h2

theorem aval (n j : ℕ) (h : n / 2 = j) : a n = ∑ k ∈ Finset.range (j + 1), catalan k := by
  rw [a, h]

end OMA.P_oeis_a110199

theorem OMA.solution : type_of% @OMA.S_oeis_a110199.main := by
  intro n hn
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    subst hk
    rw [OMA.P_oeis_a110199.aval (2 * (j + 2)) (j + 1 + 1) (by omega),
      OMA.P_oeis_a110199.aval (2 * (j + 2) - 1) (j + 1) (by omega),
      OMA.P_oeis_a110199.aval (2 * (j + 2) - 2) (j + 1) (by omega),
      OMA.P_oeis_a110199.aval (2 * (j + 2) - 3) j (by omega)]
    simp only [Finset.sum_range_succ]
    have e := OMA.P_oeis_a110199.key (j + 1)
    push_cast at e ⊢
    linear_combination (-2 : ℤ) * e
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    subst hk
    rw [OMA.P_oeis_a110199.aval (2 * (j + 1) + 1) (j + 1) (by omega),
      OMA.P_oeis_a110199.aval (2 * (j + 1) + 1 - 1) (j + 1) (by omega),
      OMA.P_oeis_a110199.aval (2 * (j + 1) + 1 - 2) j (by omega),
      OMA.P_oeis_a110199.aval (2 * (j + 1) + 1 - 3) j (by omega)]
    push_cast
    ring
