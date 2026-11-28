import Mathlib

/-!
# A245852: Powers of 8 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A245852
Credit: @darealpandaboi

Conjecture: the sequence is finite.

Translation notes.
* The terms are the powers 8^k (k >= 0) whose decimal digits (Nat.digits 10) do not include 0.
* Only finiteness is conjectured in the entry, so only finiteness is stated. The listed data are
  8^k for k = 0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 17, 24, 27, and no other k < 5000 gives a zeroless power (checked by computer).
-/

namespace OMA.S_oeis_a245852

theorem main : {m : ℕ | (∃ k : ℕ, m = 8 ^ k) ∧ 0 ∉ Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a245852
