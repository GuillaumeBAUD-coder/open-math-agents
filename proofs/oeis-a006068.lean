import OMAStatements.S_oeis_a006068
import Mathlib

namespace OMA.P006068

open OMA.S_oeis_a006068

/-- The prefix-XOR with a fixed number of terms. -/
def G (K n : ℕ) : ℕ := (List.range K).foldl (fun acc k => acc ^^^ (n >>> k)) 0

lemma a_eq (n : ℕ) : a n = G (Nat.log 2 n + 1) n := rfl

lemma G_zero (n : ℕ) : G 0 n = 0 := rfl

lemma G_succ (K n : ℕ) : G (K + 1) n = G K n ^^^ (n >>> K) := by
  unfold G
  rw [List.range_succ, List.foldl_append]
  rfl

lemma add_eq_xor (x L : ℕ) (h : x < 2 ^ L) : 2 ^ L + x = 2 ^ L ^^^ x := by
  have h1 := Nat.two_pow_add_eq_or_of_lt h 1
  rw [mul_one] at h1
  rw [h1]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : L = i
  · subst hi
    have : x.testBit L = false := Nat.testBit_lt_two_pow h
    simp [this]
  · simp [hi]

/-- Telescoping: the Gray code of the prefix-XOR. -/
lemma gray_G (K n : ℕ) : G K n ^^^ (G K n >>> 1) = n ^^^ (n >>> K) := by
  induction K with
  | zero =>
    rw [G_zero, Nat.shiftRight_zero, Nat.xor_self]
    rfl
  | succ K ih =>
    rw [G_succ, Nat.shiftRight_xor_distrib, ← Nat.shiftRight_add]
    have e : G K n ^^^ n >>> K ^^^ (G K n >>> 1 ^^^ n >>> (K + 1))
        = (G K n ^^^ G K n >>> 1) ^^^ (n >>> K ^^^ n >>> (K + 1)) := by ac_rfl
    rw [e, ih]
    have e2 : n ^^^ n >>> K ^^^ (n >>> K ^^^ n >>> (K + 1))
        = n ^^^ ((n >>> K ^^^ n >>> K) ^^^ n >>> (K + 1)) := by ac_rfl
    rw [e2, Nat.xor_self, Nat.zero_xor]

lemma G_xor (K x y : ℕ) : G K (x ^^^ y) = G K x ^^^ G K y := by
  induction K with
  | zero => rw [G_zero, G_zero, G_zero, Nat.xor_self]
  | succ K ih =>
    rw [G_succ, G_succ, G_succ, ih, Nat.shiftRight_xor_distrib]
    ac_rfl

lemma G_shift (K x : ℕ) : G K (x >>> 1) = G K x >>> 1 := by
  induction K with
  | zero => rw [G_zero, G_zero, Nat.zero_shiftRight]
  | succ K ih =>
    rw [G_succ, G_succ, ih, Nat.shiftRight_xor_distrib, ← Nat.shiftRight_add, ← Nat.shiftRight_add,
      Nat.add_comm 1 K]

lemma G_lt (K x t : ℕ) (hx : x < 2 ^ t) : G K x < 2 ^ t := by
  induction K with
  | zero =>
    rw [G_zero]
    exact Nat.pos_of_ne_zero (by positivity)
  | succ K ih =>
    rw [G_succ]
    exact Nat.xor_lt_two_pow ih (lt_of_le_of_lt (Nat.shiftRight_le x K) hx)

/-- The prefix-XOR inverts the Gray code. -/
lemma G_unique (K c n : ℕ) (hc : c < 2 ^ K) (h : c ^^^ (c >>> 1) = n) : G K n = c := by
  rw [← h, G_xor, G_shift, gray_G, Nat.shiftRight_eq_zero c K hc, Nat.xor_zero]

lemma gray_a (n : ℕ) : a n ^^^ (a n >>> 1) = n := by
  rw [a_eq, gray_G, Nat.shiftRight_eq_zero n _ (Nat.lt_pow_succ_log_self (by norm_num) n), Nat.xor_zero]

lemma a_lt (x t : ℕ) (hx : x < 2 ^ t) : a x < 2 ^ t := by
  rw [a_eq]
  exact G_lt _ x t hx

theorem main' : type_of% @OMA.S_oeis_a006068.main := by
  intro n hn
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 n := ⟨_, rfl⟩
  have hlo : 2 ^ L ≤ n := by
    rw [hL]
    exact Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (L + 1) := by
    rw [hL]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · -- n = 1
    have hn1 : n = 1 := by
      rw [h0] at hhi
      norm_num at hhi
      omega
    subst hn1
    decide
  · obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, n = 2 ^ (M + 1) + r := ⟨n - 2 ^ (M + 1), by omega⟩
    have hr : r < 2 ^ (M + 1) := by
      rw [pow_succ] at hhi
      omega
    have hM : (2 : ℕ) ^ M < 2 ^ (M + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hr' : r ^^^ 2 ^ M < 2 ^ (M + 1) := Nat.xor_lt_two_pow hr hM
    have h2 : 2 ≤ 2 ^ (M + 1) + r := by
      have : 2 ≤ 2 ^ (M + 1) := by
        rw [pow_succ]
        have := Nat.one_le_two_pow (n := M)
        omega
      omega
    -- the argument of the recursive call
    have e1 : A063946 (2 ^ (M + 1) + r) = 2 ^ (M + 1) + (r ^^^ 2 ^ M) := by
      unfold A063946
      rw [if_neg (by omega), ← hL, Nat.add_sub_cancel, add_eq_xor r _ hr, add_eq_xor _ _ hr', Nat.xor_assoc]
    have e2 : A053645 (2 ^ (M + 1) + (r ^^^ 2 ^ M)) = r ^^^ 2 ^ M := by
      unfold A053645 A053644
      rw [if_neg (by positivity),
        Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _) (by rw [pow_succ _ (M + 1)]; omega)]
      omega
    have e3 : A053644 (2 ^ (M + 1) + r) = 2 ^ (M + 1) := by
      unfold A053644
      rw [if_neg (by omega), ← hL]
    rw [e1, e2, e3, a_eq (2 ^ (M + 1) + r), ← hL]
    have hb : a (r ^^^ 2 ^ M) < 2 ^ (M + 1) := a_lt _ _ hr'
    apply G_unique
    · rw [pow_succ _ (M + 1)]
      omega
    · rw [Nat.add_comm (a (r ^^^ 2 ^ M)), add_eq_xor _ _ hb, add_eq_xor r _ hr, Nat.shiftRight_xor_distrib]
      have hs : (2 : ℕ) ^ (M + 1) >>> 1 = 2 ^ M := by
        rw [Nat.shiftRight_eq_div_pow, pow_succ]
        norm_num
      rw [hs]
      have e : 2 ^ (M + 1) ^^^ a (r ^^^ 2 ^ M) ^^^ (2 ^ M ^^^ a (r ^^^ 2 ^ M) >>> 1)
          = 2 ^ (M + 1) ^^^ (2 ^ M ^^^ (a (r ^^^ 2 ^ M) ^^^ a (r ^^^ 2 ^ M) >>> 1)) := by ac_rfl
      rw [e, gray_a]
      have e' : 2 ^ (M + 1) ^^^ (2 ^ M ^^^ (r ^^^ 2 ^ M)) = 2 ^ (M + 1) ^^^ (r ^^^ (2 ^ M ^^^ 2 ^ M)) := by
        ac_rfl
      rw [e', Nat.xor_self, Nat.xor_zero]

end OMA.P006068

theorem OMA.solution : type_of% @OMA.S_oeis_a006068.main := OMA.P006068.main'
