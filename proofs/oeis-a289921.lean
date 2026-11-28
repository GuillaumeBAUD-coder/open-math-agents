import OMAStatements.S_oeis_a289921
import Mathlib

namespace OMA.S_oeis_a289921

open PowerSeries

noncomputable def Pq : PowerSeries ℤ := 1 + C (2 : ℤ) * X ^ 1 + X ^ 2 - X ^ 10 - C (2 : ℤ) * X ^ 11 - X ^ 12

lemma DP : denominator * Pq = 1 - C (2 : ℤ) * X ^ 10 - X ^ 11 := by
  have e : denominator * Pq = denominator + C (2 : ℤ) * (X ^ 1 * denominator) + X ^ 2 * denominator
      - X ^ 10 * denominator - C (2 : ℤ) * (X ^ 11 * denominator) - X ^ 12 * denominator := by
    unfold Pq; ring
  rw [e]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', denominator, coeff_mk, coeff_one]
  by_cases hn : n < 12
  · interval_cases n <;> simp [weight] <;> norm_num [coeff_X_pow, coeff_C_mul]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    simp only [weight]
    have i1 : m + 12 - 1 = m + 11 := by omega
    have i2 : m + 12 - 2 = m + 10 := by omega
    have i3 : m + 12 - 10 = m + 2 := by omega
    have i4 : m + 12 - 11 = m + 1 := by omega
    have i5 : m + 12 - 12 = m := by omega
    simp only [i1, i2, i3, i4, i5, if_pos (show 1 ≤ m + 12 by omega), if_pos (show 2 ≤ m + 12 by omega),
      if_pos (show 10 ≤ m + 12 by omega), if_pos (show 11 ≤ m + 12 by omega),
      if_pos (show 12 ≤ m + 12 by omega), coeff_X_pow, if_neg (show ¬ (m + 12 = 0) by omega),
      if_neg (show m + 12 ≠ 10 by omega), if_neg (show m + 12 ≠ 11 by omega)]
    have q0 : 9 * (m + 12 + 1) / 10 = 9 * (m + 2 + 1) / 10 + 9 := by omega
    have q1 : 9 * (m + 11 + 1) / 10 = 9 * (m + 1 + 1) / 10 + 9 := by omega
    have q2 : 9 * (m + 10 + 1) / 10 = 9 * (m + 1) / 10 + 9 := by omega
    rw [q0, q1, q2]
    push_cast
    ring_nf

lemma Ar : denominator * invOfUnit denominator 1 = 1 :=
  mul_invOfUnit _ _ (by simp [denominator, weight])

lemma Pq_eq : Pq = invOfUnit denominator 1 * (1 - C (2 : ℤ) * X ^ 10 - X ^ 11) := by
  rw [← DP, ← mul_assoc, mul_comm (invOfUnit denominator 1), Ar, one_mul]

lemma rec (n : ℕ) : a n = coeff n Pq + 2 * (if 10 ≤ n then a (n - 10) else 0) +
    (if 11 ≤ n then a (n - 11) else 0) := by
  have h := congrArg (coeff n) Pq_eq
  have e : invOfUnit denominator 1 * (1 - C (2 : ℤ) * X ^ 10 - X ^ 11) =
      invOfUnit denominator 1 - C (2 : ℤ) * (X ^ 10 * invOfUnit denominator 1) -
        X ^ 11 * invOfUnit denominator 1 := by ring
  rw [e] at h
  simp only [map_sub, coeff_C_mul, coeff_X_pow_mul'] at h
  unfold a
  split_ifs at h ⊢ <;> linarith

lemma Pq_coeff (k : ℕ) : coeff k Pq = (if k = 0 then 1 else 0) + 2 * (if k = 1 then 1 else 0) +
    (if k = 2 then 1 else 0) - (if k = 10 then 1 else 0) - 2 * (if k = 11 then 1 else 0) -
    (if k = 12 then 1 else 0) := by
  simp only [Pq, map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow]

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have r := rec n
    have c : ∀ k, 13 ≤ k → coeff k Pq = 0 := by
      intro k hk
      rw [Pq_coeff]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
    by_cases hn : 13 ≤ n
    · rw [r, c n hn]
      have h1 := ih (n - 10) (by omega)
      have h2 := ih (n - 11) (by omega)
      rw [if_pos (by omega), if_pos (by omega)]
      linarith
    · have r0 := rec 0
      have r1 := rec 1
      have r2 := rec 2
      simp [Pq_coeff] at r0 r1 r2
      interval_cases n
      all_goals first | (rw [r]; simp [Pq_coeff]; try linarith) | skip

end OMA.S_oeis_a289921

theorem OMA.solution : type_of% @OMA.S_oeis_a289921.main := fun n => OMA.S_oeis_a289921.a_nonneg n
