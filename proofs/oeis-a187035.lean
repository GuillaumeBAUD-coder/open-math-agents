import OMAStatements.S_oeis_a187035
import Mathlib

/-! Proof for OEIS A187035: `T(n-k, k)` is `(-1)^n` when `n/3 ≤ k ≤ n/2` and `0` otherwise, so
`a(n) = (-1)^n (⌊n/2⌋ + 1 - ⌊(n+2)/3⌋)`; the recurrence reduces to an identity between floors.
Credit: Sudharsan Rajendiran -/

namespace OMA.P187035
open OMA.S_oeis_a187035

lemma term (n k : ℕ) :
    T (n - k) k = if 2 * k ≤ n ∧ n ≤ 3 * k then (-1 : ℤ) ^ n else 0 := by
  unfold T
  by_cases h : 2 * k ≤ n ∧ n ≤ 3 * k
  · rw [if_pos ⟨by omega, Nat.choose_pos (by omega)⟩, if_pos h]
    have e : n = (n - k - k) + 2 * k := by omega
    conv_rhs => rw [e]
    rw [pow_add, pow_mul]; norm_num
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2⟩
    apply h
    refine ⟨by omega, ?_⟩
    by_contra hc
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h2
    exact lt_irrefl _ h2

lemma closed (n : ℕ) : a n = (-1 : ℤ) ^ n * ((n / 2 + 1 - (n + 2) / 3 : ℕ) : ℤ) := by
  unfold a
  rw [Finset.sum_congr rfl (fun k _ => term n k), Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have : (Finset.range (n + 1)).filter (fun k => 2 * k ≤ n ∧ n ≤ 3 * k) =
      Finset.Icc ((n + 2) / 3) (n / 2) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]

end OMA.P187035

theorem OMA.P187035.old_main : ∀ n : ℕ, 5 ≤ n → OMA.S_oeis_a187035.a n = OMA.S_oeis_a187035.a (n - 2) - OMA.S_oeis_a187035.a (n - 3) + OMA.S_oeis_a187035.a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [OMA.P187035.closed, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 5 = m by omega]
  have hc : ((m + 5) / 2 + 1 - (m + 5 + 2) / 3 : ℕ) + (m / 2 + 1 - (m + 2) / 3 : ℕ) =
      ((m + 3) / 2 + 1 - (m + 3 + 2) / 3 : ℕ) + ((m + 2) / 2 + 1 - (m + 2 + 2) / 3 : ℕ) := by omega
  have hc' : (((m + 5) / 2 + 1 - (m + 5 + 2) / 3 : ℕ) : ℤ) + ((m / 2 + 1 - (m + 2) / 3 : ℕ) : ℤ) =
      (((m + 3) / 2 + 1 - (m + 3 + 2) / 3 : ℕ) : ℤ) + (((m + 2) / 2 + 1 - (m + 2 + 2) / 3 : ℕ) : ℤ) := by
    exact_mod_cast hc
  rw [pow_add (-1 : ℤ) m 5, pow_add (-1 : ℤ) m 3, pow_add (-1 : ℤ) m 2,
    show (-1 : ℤ) ^ 5 = -1 by norm_num, show (-1 : ℤ) ^ 3 = -1 by norm_num,
    show (-1 : ℤ) ^ 2 = 1 by norm_num]
  linear_combination (-(-1 : ℤ) ^ m) * hc'

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a187035.main := by
  refine ⟨OMA.P187035.old_main, ?_⟩
  have hD : ((1 - X) * (1 - X + X ^ 2) * (1 + X) ^ 2 : PowerSeries ℤ) = 1 - X ^ 2 + X ^ 3 - X ^ 5 := by ring
  rw [hD]
  ext m
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mk, coeff_mul_X_pow', coeff_one]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> decide
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      OMA.P187035.old_main m hm]
    ring
