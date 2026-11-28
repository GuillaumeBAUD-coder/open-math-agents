import OMAStatements.S_oeis_a289923
import Mathlib

namespace OMA.S_oeis_a289923

open PowerSeries

noncomputable def Pq : PowerSeries ℤ := 1 + C (2 : ℤ) * X ^ 1 + X ^ 2 + X ^ 21 + C (2 : ℤ) * X ^ 22 + X ^ 23

lemma DP : denominator * Pq = 1 - X ^ 10 - X ^ 11 - X ^ 20 := by
  have e : denominator * Pq = denominator + C (2 : ℤ) * (X ^ 1 * denominator) + X ^ 2 * denominator
      + X ^ 21 * denominator + C (2 : ℤ) * (X ^ 22 * denominator) + X ^ 23 * denominator := by
    unfold Pq; ring
  rw [e]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', denominator, coeff_mk, coeff_one]
  by_cases hn : n < 23
  · interval_cases n <;> simp [weight] <;> norm_num [coeff_X_pow, coeff_C_mul]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 23 := ⟨n - 23, by omega⟩
    simp only [weight]
    have i1 : m + 23 - 1 = m + 22 := by omega
    have i2 : m + 23 - 2 = m + 21 := by omega
    have i3 : m + 23 - 21 = m + 2 := by omega
    have i4 : m + 23 - 22 = m + 1 := by omega
    have i5 : m + 23 - 23 = m := by omega
    simp only [i1, i2, i3, i4, i5, if_pos (show 1 ≤ m + 23 by omega), if_pos (show 2 ≤ m + 23 by omega),
      if_pos (show 21 ≤ m + 23 by omega), if_pos (show 22 ≤ m + 23 by omega),
      if_pos (show 23 ≤ m + 23 by omega), coeff_X_pow, if_neg (show ¬ (m + 23 = 0) by omega),
      if_neg (show m + 23 ≠ 10 by omega), if_neg (show m + 23 ≠ 11 by omega),
      if_neg (show m + 23 ≠ 20 by omega)]
    have q0 : (19 * (m + 23 + 1) + 20) / 21 = (19 * (m + 2 + 1) + 20) / 21 + 19 := by omega
    have q1 : (19 * (m + 22 + 1) + 20) / 21 = (19 * (m + 1 + 1) + 20) / 21 + 19 := by omega
    have q2 : (19 * (m + 21 + 1) + 20) / 21 = (19 * (m + 1) + 20) / 21 + 19 := by omega
    rw [q0, q1, q2]
    push_cast
    ring_nf

lemma Ar : denominator * invOfUnit denominator 1 = 1 :=
  mul_invOfUnit _ _ (by simp [denominator, weight])

lemma Pq_eq : Pq = invOfUnit denominator 1 * (1 - X ^ 10 - X ^ 11 - X ^ 20) := by
  rw [← DP, ← mul_assoc, mul_comm (invOfUnit denominator 1), Ar, one_mul]

lemma rec (n : ℕ) : a n = coeff n Pq + (if 10 ≤ n then a (n - 10) else 0) +
    (if 11 ≤ n then a (n - 11) else 0) + (if 20 ≤ n then a (n - 20) else 0) := by
  have h := congrArg (coeff n) Pq_eq
  have e : invOfUnit denominator 1 * (1 - X ^ 10 - X ^ 11 - X ^ 20) =
      invOfUnit denominator 1 - X ^ 10 * invOfUnit denominator 1 -
        X ^ 11 * invOfUnit denominator 1 - X ^ 20 * invOfUnit denominator 1 := by ring
  rw [e] at h
  simp only [map_sub, coeff_X_pow_mul'] at h
  unfold a
  split_ifs at h ⊢ <;> linarith

lemma Pq_coeff (k : ℕ) : coeff k Pq = (if k = 0 then 1 else 0) + 2 * (if k = 1 then 1 else 0) +
    (if k = 2 then 1 else 0) + (if k = 21 then 1 else 0) + 2 * (if k = 22 then 1 else 0) +
    (if k = 23 then 1 else 0) := by
  simp only [Pq, map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow]

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have r := rec n
    have c : 0 ≤ coeff n Pq := by
      rw [Pq_coeff]
      split_ifs <;> norm_num
    rw [r]
    have h1 : 0 ≤ (if 10 ≤ n then a (n - 10) else 0) := by
      split_ifs with h
      · exact ih _ (by omega)
      · exact le_rfl
    have h2 : 0 ≤ (if 11 ≤ n then a (n - 11) else 0) := by
      split_ifs with h
      · exact ih _ (by omega)
      · exact le_rfl
    have h3 : 0 ≤ (if 20 ≤ n then a (n - 20) else 0) := by
      split_ifs with h
      · exact ih _ (by omega)
      · exact le_rfl
    linarith

end OMA.S_oeis_a289923

theorem OMA.solution : type_of% @OMA.S_oeis_a289923.main := fun n => OMA.S_oeis_a289923.a_nonneg n
