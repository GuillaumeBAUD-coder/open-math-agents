import OMAStatements.S_oeis_a112884
import Mathlib

namespace OMA.P112884

/-- 16^m ≤ 4 m C(2m,m)^2 for m ≥ 1. -/
lemma lower (m : ℕ) (hm : 1 ≤ m) : 16 ^ m ≤ 4 * m * (Nat.centralBinom m) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
    have c1 : Nat.centralBinom 1 = 2 := by decide
    rw [c1]
    norm_num
  | succ m hm ih =>
    have r := Nat.succ_mul_centralBinom_succ m
    have key : (m + 1) * 16 ^ (m + 1)
        ≤ (m + 1) * (4 * (m + 1) * (Nat.centralBinom (m + 1)) ^ 2) := by
      have e1 : (m + 1) * (4 * (m + 1) * (Nat.centralBinom (m + 1)) ^ 2)
          = 4 * ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 := by ring
      rw [e1, r]
      have e2 : 4 * (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2
          = 16 * (Nat.centralBinom m) ^ 2 * (2 * m + 1) ^ 2 := by ring
      have e3 : (m + 1) * 16 ^ (m + 1) = 16 * (m + 1) * 16 ^ m := by ring
      rw [e2, e3]
      calc 16 * (m + 1) * 16 ^ m ≤ 16 * (m + 1) * (4 * m * (Nat.centralBinom m) ^ 2) :=
            Nat.mul_le_mul_left _ ih
        _ = 16 * (Nat.centralBinom m) ^ 2 * (4 * m * (m + 1)) := by ring
        _ ≤ 16 * (Nat.centralBinom m) ^ 2 * (2 * m + 1) ^ 2 :=
            Nat.mul_le_mul_left _ (by nlinarith)
    exact Nat.le_of_mul_le_mul_left key (by omega)

/-- (2m+1) C(2m,m)^2 ≤ 16^m. -/
lemma upper (m : ℕ) : (2 * m + 1) * (Nat.centralBinom m) ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have r := Nat.succ_mul_centralBinom_succ m
    have key : (m + 1) ^ 2 * ((2 * (m + 1) + 1) * (Nat.centralBinom (m + 1)) ^ 2)
        ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
      have e1 : (m + 1) ^ 2 * ((2 * (m + 1) + 1) * (Nat.centralBinom (m + 1)) ^ 2)
          = (2 * m + 3) * ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 := by ring
      rw [e1, r]
      calc (2 * m + 3) * (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2
            = 4 * (2 * m + 3) * (2 * m + 1) * ((2 * m + 1) * (Nat.centralBinom m) ^ 2) := by ring
        _ ≤ 4 * (2 * m + 3) * (2 * m + 1) * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_right _ (by nlinarith)
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

end OMA.P112884

theorem OMA.solution : type_of% @OMA.S_oeis_a112884.main := by
  intro n
  unfold OMA.S_oeis_a112884.a
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hE : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hk : k + 1 < 2 * 2 ^ k := by
      rw [← hE]
      exact Nat.lt_pow_self (by norm_num)
    have h4 : 4 * 2 ^ k = 2 ^ (k + 2) := by ring
    have hmpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [Nat.add_sub_cancel, hE, ← Nat.centralBinom_eq_two_mul_choose]
    have hL := OMA.P112884.lower (2 ^ k) hmpos
    have hU := OMA.P112884.upper (2 ^ k)
    have hNpos : 0 < Nat.centralBinom (2 ^ k) := Nat.centralBinom_pos _
    generalize hm : 2 ^ k = m at *
    generalize hN : Nat.centralBinom m = N at *
    have h16 : (16 : ℕ) ^ m = 2 ^ (4 * m) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    have hh1 : 2 * ((k + 1) / 2) ≤ k + 1 := by omega
    have hh2 : k ≤ 2 * ((k + 1) / 2) := by omega
    generalize hh : (k + 1) / 2 = h at *
    have c1 : 2 ^ (2 * m - h - 1) ≤ N := by
      have e1 : (2 ^ (2 * m - h - 1)) ^ 2 * 2 ^ (2 * h + 2) = 2 ^ (4 * m) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      have e2 : 4 * m ≤ 2 ^ (2 * h + 2) := by
        rw [h4]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have e3 : (2 ^ (2 * m - h - 1)) ^ 2 * 2 ^ (2 * h + 2) ≤ N ^ 2 * 2 ^ (2 * h + 2) := by
        rw [e1, ← h16]
        calc 16 ^ m ≤ 4 * m * N ^ 2 := hL
          _ ≤ 2 ^ (2 * h + 2) * N ^ 2 := Nat.mul_le_mul_right _ e2
          _ = N ^ 2 * 2 ^ (2 * h + 2) := by ring
      have e4 := Nat.le_of_mul_le_mul_right e3 (by positivity)
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp e4
    have c2 : N < 2 ^ (2 * m - h) := by
      have e1 : (2 ^ (2 * m - h)) ^ 2 * 2 ^ (2 * h) = 2 ^ (4 * m) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      have e2 : 2 ^ (2 * h) ≤ 2 * m := by
        rw [← hE]
        exact Nat.pow_le_pow_right (by norm_num) hh1
      have hN2 : 0 < N ^ 2 := by positivity
      have e3 : N ^ 2 * 2 ^ (2 * h) < (2 ^ (2 * m - h)) ^ 2 * 2 ^ (2 * h) := by
        rw [e1, ← h16]
        calc N ^ 2 * 2 ^ (2 * h) ≤ N ^ 2 * (2 * m) := Nat.mul_le_mul_left _ e2
          _ < (2 * m + 1) * N ^ 2 := by nlinarith
          _ ≤ 16 ^ m := hU
      have e4 := Nat.lt_of_mul_lt_mul_right e3
      exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp e4
    rw [Nat.digits_len 2 N (by norm_num) hNpos.ne']
    have hlog : Nat.log 2 N = 2 * m - h - 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow c1 (by
        rw [show 2 * m - h - 1 + 1 = 2 * m - h by omega]
        exact c2)
    rw [hlog]
    omega
