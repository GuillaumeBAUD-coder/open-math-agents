import Mathlib

/-!
# A245853: Powers of 12 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A245853
Credit: @darealpandaboi

Conjecture: the sequence is finite.

Translation notes.
* The terms are the powers 12^k (k >= 0) whose decimal digits (Nat.digits 10) do not include 0.
* Only finiteness is conjectured in the entry, so only finiteness is stated. The listed data are
  12^k for k = 0, 1, 2, 3, 5, 6, 8, 10, 14, 20, 26, and no other k < 5000 gives a zeroless power (checked by computer).
-/

namespace OMA.S_oeis_a245853

theorem main : {m : ℕ | (∃ k : ℕ, m = 12 ^ k) ∧ 0 ∉ Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a245853
