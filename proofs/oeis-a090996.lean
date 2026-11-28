import OMAStatements.S_oeis_a090996

namespace OMA.P_oeis_a090996

open OMA.S_oeis_a090996

lemma a_step (n : ℕ) (hn : 0 < n) :
    a n = (((Nat.digits 2 (n / 2)).reverse ++ [n % 2]).takeWhile (fun d => d == 1)).length := by
  unfold a
  rw [Nat.digits_def' (by norm_num) hn, List.reverse_cons]

lemma main_lemma (m : ℕ) : ∀ n : ℕ, 2 ^ m ≤ n → n < 2 ^ (m + 1) →
    a n = if n = 2 ^ (m + 1) - 1 then m + 1 else m - Nat.log 2 (2 ^ (m + 1) - 1 - n) := by
  induction m with
  | zero =>
    intro n h1 h2
    have : n = 1 := by simp at h1 h2; omega
    subst this
    simp [a]
  | succ m ih =>
    intro n h1 h2
    have hp : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
    have hp' : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have hn : 0 < n := lt_of_lt_of_le (by positivity) h1
    set h := n / 2 with hh
    have hh1 : 2 ^ m ≤ h := by omega
    have hh2 : h < 2 ^ (m + 1) := by omega
    have hpos : 0 < h := lt_of_lt_of_le (by positivity) hh1
    have IH := ih h hh1 hh2
    have hlen : (Nat.digits 2 h).reverse.length = m + 1 := by
      rw [List.length_reverse, Nat.length_digits 2 h (by norm_num) hpos.ne',
        Nat.log_eq_of_pow_le_of_lt_pow hh1 hh2]
    rw [a_step n hn, List.takeWhile_append]
    unfold a at IH
    rw [← hh]
    by_cases hc : h = 2 ^ (m + 1) - 1
    · rw [if_pos hc] at IH
      rw [if_pos (by rw [IH, hlen]), List.length_append, hlen]
      have hb := Nat.mod_two_eq_zero_or_one n
      rcases hb with hb | hb
      · rw [hb, if_neg (by omega)]
        have e : 2 ^ (m + 1 + 1) - 1 - n = 1 := by omega
        rw [e]; simp
      · rw [hb, if_pos (by omega)]
        simp
    · rw [if_neg hc] at IH
      have hlog : Nat.log 2 (2 ^ (m + 1) - 1 - h) < m + 1 := by
        apply Nat.log_lt_of_lt_pow (by omega); omega
      rw [if_neg (by rw [IH, hlen]; omega), IH, if_neg (by omega)]
      have ec : (2 ^ (m + 1 + 1) - 1 - n) / 2 = 2 ^ (m + 1) - 1 - h := by omega
      have hc2 : 2 ≤ 2 ^ (m + 1 + 1) - 1 - n := by omega
      have hl := Nat.log_div_base 2 (2 ^ (m + 1 + 1) - 1 - n)
      rw [ec] at hl
      have hl1 : 1 ≤ Nat.log 2 (2 ^ (m + 1 + 1) - 1 - n) :=
        Nat.le_log_of_pow_le (by norm_num) (by simpa using hc2)
      omega

end OMA.P_oeis_a090996

theorem OMA.solution : type_of% @OMA.S_oeis_a090996.main := by
  intro n hn
  set m := Nat.log 2 n with hm
  have h1 : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have h2 : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hp : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
  rw [OMA.P_oeis_a090996.main_lemma m n h1 h2]
  unfold OMA.S_oeis_a090996.w
  rw [← hm]
  by_cases hc : n = 2 ^ (m + 1) - 1
  · rw [if_pos hc]
    have e1 : Nat.log 2 (n + 1) = m + 1 := by
      rw [show n + 1 = 2 ^ (m + 1) by omega, Nat.log_pow (by norm_num)]
    rw [e1, show 2 ^ (m + 1 + 1) - n - 1 = 2 ^ (m + 1) by omega, Nat.log_pow (by norm_num)]
    push_cast; ring
  · rw [if_neg hc]
    have e1 : Nat.log 2 (n + 1) = m :=
      Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
    have hlog : Nat.log 2 (2 ^ (m + 1) - 1 - n) ≤ m := by
      have : Nat.log 2 (2 ^ (m + 1) - 1 - n) < m := by
        apply Nat.log_lt_of_lt_pow (by omega)
        have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
      omega
    rw [e1, show 2 ^ (m + 1) - n - 1 = 2 ^ (m + 1) - 1 - n by omega]
    push_cast [hlog]; ring
