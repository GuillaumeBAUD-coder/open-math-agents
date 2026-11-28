import Mathlib

/-!
# A240945: Powers of 9 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A240945
Credit: @darealpandaboi

Conjecture: the sequence is finite.

Translation notes.
* The terms are the powers 9^k (k >= 0) whose decimal digits (Nat.digits 10) do not include 0.
* Only finiteness is conjectured in the entry, so only finiteness is stated. The listed data are
  9^k for k = 0, 1, 2, 3, 4, 6, 7, 12, 13, 14, 17, 34, and no other k < 5000 gives a zeroless
  power (checked by computer).
-/

namespace OMA.S_oeis_a240945

theorem main : {m : ℕ | (∃ k : ℕ, m = 9 ^ k) ∧ 0 ∉ Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a240945
