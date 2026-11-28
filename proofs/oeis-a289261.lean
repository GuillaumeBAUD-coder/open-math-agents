import OMAStatements.S_oeis_a289261
import Mathlib

namespace OMA.S_oeis_a289261

open PowerSeries

def w (n : ℕ) : ℕ := (13 * (n + 1)) / 8

lemma weight_eq (n : ℕ) : weight ((13 : ℝ) / 8) n = ((w n : ℕ) : ℚ) := by
  unfold weight
  have h : ⌊((n : ℝ) + 1) * (13 / 8)⌋ = ((w n : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff]
    have h1 : 8 * w n ≤ 13 * (n + 1) := by unfold w; omega
    have h2 : 13 * (n + 1) < 8 * w n + 8 := by unfold w; omega
    have h1' : (8 * (w n : ℝ)) ≤ 13 * ((n : ℝ) + 1) := by exact_mod_cast h1
    have h2' : 13 * ((n : ℝ) + 1) < 8 * (w n : ℝ) + 8 := by exact_mod_cast h2
    push_cast
    constructor <;> linarith
  rw [h]
  simp

noncomputable def Dq : PowerSeries ℚ := PowerSeries.mk fun n => (-1 : ℚ) ^ n * (w n : ℚ)

lemma den_eq : denominator ((13 : ℝ) / 8) = Dq := by
  ext n
  simp [denominator, Dq, weight_eq]

noncomputable def Pq : PowerSeries ℚ :=
  1 + C (2 : ℚ) * X ^ 1 + X ^ 2 - X ^ 8 - C (2 : ℚ) * X ^ 9 - X ^ 10

noncomputable def Qq : PowerSeries ℚ :=
  1 - X ^ 1 - X ^ 2 - X ^ 3 + X ^ 5 + X ^ 6 - C (2 : ℚ) * X ^ 8

lemma DP : Dq * Pq = Qq := by
  have e : Dq * Pq = Dq + C (2 : ℚ) * (X ^ 1 * Dq) + X ^ 2 * Dq
      - X ^ 8 * Dq - C (2 : ℚ) * (X ^ 9 * Dq) - X ^ 10 * Dq := by
    unfold Pq; ring
  rw [e]
  ext n
  simp only [Qq, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', Dq, coeff_mk, coeff_one, coeff_X_pow]
  by_cases hn : n < 11
  · interval_cases n <;> simp [w] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    have i1 : m + 11 - 1 = m + 10 := by omega
    have i2 : m + 11 - 2 = m + 9 := by omega
    have i3 : m + 11 - 8 = m + 3 := by omega
    have i4 : m + 11 - 9 = m + 2 := by omega
    have i5 : m + 11 - 10 = m + 1 := by omega
    simp only [i1, i2, i3, i4, i5, if_pos (show 1 ≤ m + 11 by omega), if_pos (show 2 ≤ m + 11 by omega),
      if_pos (show 8 ≤ m + 11 by omega), if_pos (show 9 ≤ m + 11 by omega),
      if_pos (show 10 ≤ m + 11 by omega), if_neg (show ¬ (m + 11 = 0) by omega),
      if_neg (show m + 11 ≠ 1 by omega), if_neg (show m + 11 ≠ 2 by omega),
      if_neg (show m + 11 ≠ 3 by omega), if_neg (show m + 11 ≠ 5 by omega),
      if_neg (show m + 11 ≠ 6 by omega), if_neg (show m + 11 ≠ 8 by omega)]
    have q0 : w (m + 11) = w (m + 3) + 13 := by unfold w; omega
    have q1 : w (m + 10) = w (m + 2) + 13 := by unfold w; omega
    have q2 : w (m + 9) = w (m + 1) + 13 := by unfold w; omega
    rw [q0, q1, q2]
    push_cast
    ring_nf

noncomputable def Aq : PowerSeries ℚ := (Dq)⁻¹

lemma Dq_inv : Dq * Aq = 1 := by
  unfold Aq
  exact PowerSeries.mul_inv_cancel _ (by simp [Dq, w])

lemma AQ : Aq * Qq = Pq := by
  rw [← DP, ← mul_assoc, mul_comm Aq, Dq_inv, one_mul]

lemma Pq_coeff (k : ℕ) : coeff k Pq = (if k = 0 then 1 else 0) + 2 * (if k = 1 then 1 else 0) +
    (if k = 2 then 1 else 0) - (if k = 8 then 1 else 0) - 2 * (if k = 9 then 1 else 0) -
    (if k = 10 then 1 else 0) := by
  simp only [Pq, map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow]

lemma rec (n : ℕ) : coeff n Aq = coeff n Pq + (if 1 ≤ n then coeff (n - 1) Aq else 0) +
    (if 2 ≤ n then coeff (n - 2) Aq else 0) + (if 3 ≤ n then coeff (n - 3) Aq else 0) -
    (if 5 ≤ n then coeff (n - 5) Aq else 0) - (if 6 ≤ n then coeff (n - 6) Aq else 0) +
    2 * (if 8 ≤ n then coeff (n - 8) Aq else 0) := by
  have h := congrArg (coeff n) AQ
  have e : Aq * Qq = Aq - X ^ 1 * Aq - X ^ 2 * Aq - X ^ 3 * Aq + X ^ 5 * Aq + X ^ 6 * Aq
      - C (2 : ℚ) * (X ^ 8 * Aq) := by
    unfold Qq; ring
  rw [e] at h
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul'] at h
  split_ifs at h ⊢ <;> linarith

lemma tab : coeff 0 Aq = 1 ∧ coeff 1 Aq = 3 ∧ coeff 2 Aq = 5 ∧ coeff 3 Aq = 9 ∧ coeff 4 Aq = 17 ∧
    coeff 5 Aq = 30 ∧ coeff 6 Aq = 52 ∧ coeff 7 Aq = 91 := by
  have r0 := rec 0
  have r1 := rec 1
  have r2 := rec 2
  have r3 := rec 3
  have r4 := rec 4
  have r5 := rec 5
  have r6 := rec 6
  have r7 := rec 7
  simp [Pq_coeff] at r0
  simp [Pq_coeff, r0] at r1
  simp [Pq_coeff, r0, r1] at r2
  simp [Pq_coeff, r0, r1, r2] at r3
  simp [Pq_coeff, r0, r1, r2, r3] at r4
  simp [Pq_coeff, r0, r1, r2, r3, r4] at r5
  simp [Pq_coeff, r0, r1, r2, r3, r4, r5] at r6
  simp [Pq_coeff, r0, r1, r2, r3, r4, r5, r6] at r7
  have r0' : coeff 0 Aq = 1 := by rw [coeff_zero_eq_constantCoeff_apply]; exact r0
  refine ⟨r0', by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma mono (n : ℕ) : 1 ≤ coeff n Aq ∧ coeff n Aq + 1 ≤ coeff (n + 1) Aq := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩ := tab
    by_cases hn : n < 7
    · interval_cases n <;> simp [t0, t1, t2, t3, t4, t5, t6, t7] <;> norm_num
    · have r := rec (n + 1)
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have e1 : k + 7 + 1 - 1 = k + 7 := by omega
      have e2 : k + 7 + 1 - 2 = k + 6 := by omega
      have e3 : k + 7 + 1 - 3 = k + 5 := by omega
      have e4 : k + 7 + 1 - 5 = k + 3 := by omega
      have e5 : k + 7 + 1 - 6 = k + 2 := by omega
      have e6 : k + 7 + 1 - 8 = k := by omega
      rw [e1, e2, e3, e4, e5, e6, if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_pos (by omega), if_pos (by omega)] at r
      have m0 := ih k (by omega)
      have m1 := ih (k + 1) (by omega)
      have m2 := ih (k + 2) (by omega)
      have m3 := ih (k + 3) (by omega)
      have m4 := ih (k + 4) (by omega)
      have m5 := ih (k + 5) (by omega)
      have m6 := ih (k + 6) (by omega)
      have hc : -2 ≤ coeff (k + 7 + 1) Pq := by
        rw [Pq_coeff]; split_ifs <;> first | (exfalso; omega) | norm_num
      refine ⟨by linarith [m0.1, m0.2, m1.2, m2.2, m3.2, m4.2, m5.2, m6.2], ?_⟩
      linarith [m0.1, m2.2, m3.2, m4.2, m5.2, m6.2, m0.2, m1.2]

end OMA.S_oeis_a289261

theorem OMA.solution : type_of% @OMA.S_oeis_a289261.main := by
  open OMA.S_oeis_a289261 in
  apply strictMono_nat_of_lt_succ
  intro n
  have h : OMA.S_oeis_a289261.a ((13 : ℝ) / 8) n = PowerSeries.coeff n Aq := by
    unfold OMA.S_oeis_a289261.a
    rw [den_eq]; rfl
  have h' : OMA.S_oeis_a289261.a ((13 : ℝ) / 8) (n + 1) = PowerSeries.coeff (n + 1) Aq := by
    unfold OMA.S_oeis_a289261.a
    rw [den_eq]; rfl
  rw [h, h']
  have := (mono n).2
  linarith
