import Mathlib

/-!
# A092969: a(1) = 2; for n>1, a(n) = largest prime of the form n!/k + 1, where k < n, or 0 if no such prime exists.

Source: https://oeis.org/A092969
Credit: @darealpandaboi

Conjecture: there are only finitely many zeros in this sequence.

Translation notes.
* For n > 1, a(n) = 0 exactly when no k with 1 <= k < n makes n!/k + 1 prime (every such k
  divides n!). a(1) = 2 is not 0, so only n > 1 matters.
* This reproduces the listed data a(1..21) and Robert G. Wilson v's zeros 18, 51, 53, 84, 95,
  100, 104, 106 (all zeros with n <= 110; checked by computer).
-/

namespace OMA.S_oeis_a092969

theorem main :
    {n : ℕ | 1 < n ∧ ¬ ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ (n.factorial / k + 1).Prime}.Finite := by
  sorry

end OMA.S_oeis_a092969
