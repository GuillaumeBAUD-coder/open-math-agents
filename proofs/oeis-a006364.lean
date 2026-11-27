import OMAStatements.S_oeis_a006364
import Mathlib

namespace OMA.P_oeis_a006364

open OMA.S_oeis_a006364

theorem bc_zero : bitCount 0 = 0 := by simp [bitCount]

theorem bc_double (k : ℕ) : bitCount (2 * k) = bitCount k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [bitCount]
  · unfold bitCount
    rw [Nat.digits_def' (by norm_num) (by omega), show 2 * k % 2 = 0 by omega,
      show 2 * k / 2 = k by omega, List.sum_cons, zero_add]

theorem bc_double_add_one (k : ℕ) : bitCount (2 * k + 1) = bitCount k + 1 := by
  unfold bitCount
  rw [Nat.digits_def' (by norm_num) (by omega), show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega, List.sum_cons, add_comm]

theorem bc_le (k : ℕ) : bitCount k ≤ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [bc_zero]
    · obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [bc_double]
        have := ih m (by omega)
        omega
      · rw [bc_double_add_one]
        have := ih m (by omega)
        omega

theorem count_four [DecidablePred Qualifies] (t : ℕ) :
    Nat.count Qualifies (4 * t) = 2 * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 4 * (t + 1) = 4 * t + 3 + 1 by ring, Nat.count_succ, Nat.count_succ,
      Nat.count_succ, Nat.count_succ, ih]
    have h0 : Qualifies (4 * t) ↔ bitCount t % 2 = 0 := by
      unfold Qualifies
      rw [show 4 * t / 2 = 2 * t by omega, bc_double]
    have h1 : Qualifies (4 * t + 1) ↔ bitCount t % 2 = 0 := by
      unfold Qualifies
      rw [show (4 * t + 1) / 2 = 2 * t by omega, bc_double]
    have h2 : Qualifies (4 * t + 2) ↔ (bitCount t + 1) % 2 = 0 := by
      unfold Qualifies
      rw [show (4 * t + 2) / 2 = 2 * t + 1 by omega, bc_double_add_one]
    have h3 : Qualifies (4 * t + 3) ↔ (bitCount t + 1) % 2 = 0 := by
      unfold Qualifies
      rw [show (4 * t + 3) / 2 = 2 * t + 1 by omega, bc_double_add_one]
    simp only [h0, h1, h2, h3]
    split_ifs <;> omega

theorem nth_pair (k : ℕ) :
    Nat.nth Qualifies (2 * k) = 4 * k + 2 * (bitCount k % 2) ∧
    Nat.nth Qualifies (2 * k + 1) = 4 * k + 2 * (bitCount k % 2) + 1 := by
  classical
  have hc := count_four k
  rcases Nat.mod_two_eq_zero_or_one (bitCount k) with h | h
  · rw [h]
    have q0 : Qualifies (4 * k) := by
      unfold Qualifies
      rw [show 4 * k / 2 = 2 * k by omega, bc_double]
      exact h
    have q1 : Qualifies (4 * k + 1) := by
      unfold Qualifies
      rw [show (4 * k + 1) / 2 = 2 * k by omega, bc_double]
      exact h
    have c1 : Nat.count Qualifies (4 * k + 1) = 2 * k + 1 := by
      rw [Nat.count_succ, hc, if_pos q0]
    constructor
    · have := Nat.nth_count q0
      rw [hc] at this
      simpa using this
    · have := Nat.nth_count q1
      rw [c1] at this
      simpa using this
  · rw [h]
    have n0 : ¬ Qualifies (4 * k) := by
      unfold Qualifies
      rw [show 4 * k / 2 = 2 * k by omega, bc_double]
      omega
    have n1 : ¬ Qualifies (4 * k + 1) := by
      unfold Qualifies
      rw [show (4 * k + 1) / 2 = 2 * k by omega, bc_double]
      omega
    have q2 : Qualifies (4 * k + 2) := by
      unfold Qualifies
      rw [show (4 * k + 2) / 2 = 2 * k + 1 by omega, bc_double_add_one]
      omega
    have q3 : Qualifies (4 * k + 2 + 1) := by
      unfold Qualifies
      rw [show (4 * k + 2 + 1) / 2 = 2 * k + 1 by omega, bc_double_add_one]
      omega
    have c2 : Nat.count Qualifies (4 * k + 2) = 2 * k := by
      rw [Nat.count_succ, Nat.count_succ, hc, if_neg n0, if_neg n1]
      omega
    have c3 : Nat.count Qualifies (4 * k + 2 + 1) = 2 * k + 1 := by
      rw [Nat.count_succ, c2, if_pos q2]
    constructor
    · have := Nat.nth_count q2
      rw [c2] at this
      simpa using this
    · have := Nat.nth_count q3
      rw [c3] at this
      simpa using this

end OMA.P_oeis_a006364

theorem OMA.solution : type_of% @OMA.S_oeis_a006364.main := by
  intro n hn
  unfold OMA.S_oeis_a006364.a
  have hb := OMA.P_oeis_a006364.bc_le
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n - 1)
  · obtain rfl : n = 2 * k + 1 := by omega
    rw [hk, (OMA.P_oeis_a006364.nth_pair k).1, OMA.P_oeis_a006364.bc_double]
    have hbk := hb k
    have hpow : (-1 : ℤ) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
    rw [hpow]
    rcases Nat.mod_two_eq_zero_or_one (OMA.S_oeis_a006364.bitCount k) with h | h
    · rw [h, Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]
      push_cast
      norm_num
      ring
    · rw [h, Even.neg_one_pow (Nat.even_iff.mpr (by omega))]
      push_cast
      norm_num
      ring
  · obtain rfl : n = 2 * k + 2 := by omega
    rw [hk, (OMA.P_oeis_a006364.nth_pair k).2, OMA.P_oeis_a006364.bc_double_add_one]
    have hbk := hb k
    have hpow : (-1 : ℤ) ^ (2 * k + 2) = 1 := Even.neg_one_pow ⟨k + 1, by ring⟩
    rw [hpow]
    rcases Nat.mod_two_eq_zero_or_one (OMA.S_oeis_a006364.bitCount k) with h | h
    · rw [h, Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]
      push_cast
      norm_num
      ring
    · rw [h, Even.neg_one_pow (Nat.even_iff.mpr (by omega))]
      push_cast
      norm_num
      ring
