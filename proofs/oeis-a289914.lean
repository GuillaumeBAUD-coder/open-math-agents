import OMAStatements.S_oeis_a289914
import Mathlib

namespace OMA.S_oeis_a289914

open PowerSeries

def w (n : ℕ) : ℕ := (14 * (n + 1) + 5) / 10

lemma weight_eq (n : ℕ) : weight ((7 : ℝ) / 5) n = ((w n : ℕ) : ℚ) := by
  unfold weight
  have h : round (((n : ℝ) + 1) * (7 / 5)) = ((w n : ℕ) : ℤ) := by
    rw [round_eq, Int.floor_eq_iff]
    have h1 : 10 * w n ≤ 14 * (n + 1) + 5 := by unfold w; omega
    have h2 : 14 * (n + 1) + 5 < 10 * w n + 10 := by unfold w; omega
    have h1' : (10 * (w n : ℝ)) ≤ 14 * ((n : ℝ) + 1) + 5 := by exact_mod_cast h1
    have h2' : 14 * ((n : ℝ) + 1) + 5 < 10 * (w n : ℝ) + 10 := by exact_mod_cast h2
    push_cast
    constructor <;> linarith
  rw [h]
  simp

noncomputable def Dq : PowerSeries ℚ := PowerSeries.mk fun n => (-1 : ℚ) ^ n * (w n : ℚ)

lemma den_eq : denominator ((7 : ℝ) / 5) = Dq := by
  ext n
  simp [denominator, Dq, weight_eq]

noncomputable def Pq : PowerSeries ℚ :=
  1 + C (2 : ℚ) * X ^ 1 + X ^ 2 + X ^ 5 + C (2 : ℚ) * X ^ 6 + X ^ 7

noncomputable def Qq : PowerSeries ℚ := 1 - X ^ 1 - X ^ 2 - X ^ 3 - X ^ 4 + X ^ 5

lemma DP : Dq * Pq = Qq := by
  have e : Dq * Pq = Dq + C (2 : ℚ) * (X ^ 1 * Dq) + X ^ 2 * Dq
      + X ^ 5 * Dq + C (2 : ℚ) * (X ^ 6 * Dq) + X ^ 7 * Dq := by
    unfold Pq; ring
  rw [e]
  ext n
  simp only [Qq, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', Dq, coeff_mk, coeff_one, coeff_X_pow]
  by_cases hn : n < 8
  · interval_cases n <;> simp [w] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have i1 : m + 8 - 1 = m + 7 := by omega
    have i2 : m + 8 - 2 = m + 6 := by omega
    have i3 : m + 8 - 5 = m + 3 := by omega
    have i4 : m + 8 - 6 = m + 2 := by omega
    have i5 : m + 8 - 7 = m + 1 := by omega
    simp only [i1, i2, i3, i4, i5, if_pos (show 1 ≤ m + 8 by omega), if_pos (show 2 ≤ m + 8 by omega),
      if_pos (show 5 ≤ m + 8 by omega), if_pos (show 6 ≤ m + 8 by omega),
      if_pos (show 7 ≤ m + 8 by omega), if_neg (show ¬ (m + 8 = 0) by omega),
      if_neg (show m + 8 ≠ 1 by omega), if_neg (show m + 8 ≠ 2 by omega),
      if_neg (show m + 8 ≠ 3 by omega), if_neg (show m + 8 ≠ 4 by omega),
      if_neg (show m + 8 ≠ 5 by omega)]
    have q0 : w (m + 8) = w (m + 3) + 7 := by unfold w; omega
    have q1 : w (m + 7) = w (m + 2) + 7 := by unfold w; omega
    have q2 : w (m + 6) = w (m + 1) + 7 := by unfold w; omega
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
    (if k = 2 then 1 else 0) + (if k = 5 then 1 else 0) + 2 * (if k = 6 then 1 else 0) +
    (if k = 7 then 1 else 0) := by
  simp only [Pq, map_add, coeff_one, coeff_C_mul, coeff_X_pow]

lemma rec (n : ℕ) : coeff n Aq = coeff n Pq + (if 1 ≤ n then coeff (n - 1) Aq else 0) +
    (if 2 ≤ n then coeff (n - 2) Aq else 0) + (if 3 ≤ n then coeff (n - 3) Aq else 0) +
    (if 4 ≤ n then coeff (n - 4) Aq else 0) - (if 5 ≤ n then coeff (n - 5) Aq else 0) := by
  have h := congrArg (coeff n) AQ
  have e : Aq * Qq = Aq - X ^ 1 * Aq - X ^ 2 * Aq - X ^ 3 * Aq - X ^ 4 * Aq + X ^ 5 * Aq := by
    unfold Qq; ring
  rw [e] at h
  simp only [map_sub, map_add, coeff_X_pow_mul'] at h
  split_ifs at h ⊢ <;> linarith

lemma tab : coeff 0 Aq = 1 ∧ coeff 1 Aq = 3 ∧ coeff 2 Aq = 5 ∧ coeff 3 Aq = 9 ∧ coeff 4 Aq = 18 := by
  have r0 := rec 0
  have r1 := rec 1
  have r2 := rec 2
  have r3 := rec 3
  have r4 := rec 4
  simp [Pq_coeff] at r0
  simp [Pq_coeff, r0] at r1
  simp [Pq_coeff, r0, r1] at r2
  simp [Pq_coeff, r0, r1, r2] at r3
  simp [Pq_coeff, r0, r1, r2, r3] at r4
  have r0' : coeff 0 Aq = 1 := by rw [coeff_zero_eq_constantCoeff_apply]; exact r0
  refine ⟨r0', by linarith, by linarith, by linarith, by linarith⟩

lemma mono (n : ℕ) : 1 ≤ coeff n Aq ∧ coeff n Aq < coeff (n + 1) Aq := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨t0, t1, t2, t3, t4⟩ := tab
    by_cases hn : n < 4
    · interval_cases n <;> simp [t0, t1, t2, t3, t4] <;> norm_num
    · have r := rec (n + 1)
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have e1 : k + 4 + 1 - 1 = k + 4 := by omega
      have e2 : k + 4 + 1 - 2 = k + 3 := by omega
      have e3 : k + 4 + 1 - 3 = k + 2 := by omega
      have e4 : k + 4 + 1 - 4 = k + 1 := by omega
      have e5 : k + 4 + 1 - 5 = k := by omega
      rw [e1, e2, e3, e4, e5, if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)] at r
      have m0 := ih k (by omega)
      have m1 := ih (k + 1) (by omega)
      have m2 := ih (k + 2) (by omega)
      have m3 := ih (k + 3) (by omega)
      have hc : 0 ≤ coeff (k + 4 + 1) Pq := by
        rw [Pq_coeff]; split_ifs <;> norm_num
      refine ⟨by linarith [m0.1, m0.2, m1.2, m2.2, m3.2], ?_⟩
      linarith [m0.2, m2.1, m3.1]

end OMA.S_oeis_a289914

theorem OMA.solution : type_of% @OMA.S_oeis_a289914.main := by
  open OMA.S_oeis_a289914 in
  apply strictMono_nat_of_lt_succ
  intro n
  have h : OMA.S_oeis_a289914.a ((7 : ℝ) / 5) n = PowerSeries.coeff n Aq := by
    unfold OMA.S_oeis_a289914.a
    rw [den_eq]; rfl
  have h' : OMA.S_oeis_a289914.a ((7 : ℝ) / 5) (n + 1) = PowerSeries.coeff (n + 1) Aq := by
    unfold OMA.S_oeis_a289914.a
    rw [den_eq]; rfl
  rw [h, h']
  exact (mono n).2
