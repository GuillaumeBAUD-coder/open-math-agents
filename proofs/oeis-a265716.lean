import OMAStatements.S_oeis_a265716
import Mathlib

/-!
# A265716: McEachen's formula for n IMPL 2n

With L the binary length of n ≥ 1, the binary length of 2n is L + 1, and
2^(L+1) − 1 − n = 2^L + (2^L − 1 − n) with 2^L − 1 − n < 2^L. Comparing bits: below position L both
sides read the bits of 2^L − 1 − n or 2n; at position L both are set, because 2n has its top bit
there; above L both vanish.
-/

namespace A265716Proof

theorem top_bit (x L : ℕ) (h1 : 2 ^ L ≤ x) (h2 : x < 2 ^ (L + 1)) : x.testBit L = true := by
  have e : x = 2 ^ L + (x - 2 ^ L) := by omega
  rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by rw [pow_succ] at h2; omega)]
  rfl

end A265716Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a265716.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [OMA.S_oeis_a265716.a, OMA.S_oeis_a265716.impl, OMA.S_oeis_a265716.A003817]
  unfold OMA.S_oeis_a265716.a OMA.S_oeis_a265716.impl OMA.S_oeis_a265716.A003817
  rw [if_neg hn.ne']
  have hs : Nat.size (2 * n) = Nat.size n + 1 := by
    rw [show 2 * n = n <<< 1 by rw [Nat.shiftLeft_eq]; ring]
    exact Nat.size_shiftLeft hn.ne' 1
  rw [hs]
  have hL : 0 < Nat.size n := Nat.size_pos.mpr hn
  have hnL : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have hLn : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  generalize Nat.size n = L at hL hnL hLn
  have hpow : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hm : 2 ^ (L + 1) - 1 - n = 2 ^ L + (2 ^ L - 1 - n) := by
    rw [pow_succ]; omega
  rw [hm]
  have h2n : (2 * n).testBit L = true :=
    A265716Proof.top_bit _ _ (by omega) (by rw [pow_succ]; omega)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor, Nat.testBit_lor]
  rcases lt_trichotomy i L with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (show 2 ^ i - 1 - n < 2 ^ i by omega), h2n]
    rfl
  · have hi : 2 ^ (L + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [Nat.testBit_lt_two_pow (show 2 ^ L + (2 ^ L - 1 - n) < 2 ^ i by rw [pow_succ] at hi; omega),
      Nat.testBit_lt_two_pow (show 2 ^ L - 1 - n < 2 ^ i by rw [pow_succ] at hi; omega)]
