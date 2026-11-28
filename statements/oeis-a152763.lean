import Mathlib

/-!
# A152763: Number of divisors of Catalan number A000108(n).

Source: https://oeis.org/A152763
Credit: @azmiozgen

Conjectures (Jianing Song, Jun 16 2022, from the entry):
1. a(2^k-1) < a(2^k-2) for all k >= 3 (checked up to k = 263);
2. a(2^k-1) != a(2^k) for all k (checked up to k = 265).

Formalization notes:
* a(n) = number of divisors of `catalan n` (offset 0).
* Conjecture 2 is stated for k ≥ 1: at k = 0 it would compare a(0) = a(1) = 1 (both Catalan
  numbers equal 1), which the entry's checks evidently exclude.
* Controls (computed): a(0..11) = 1, 1, 2, 2, 4, 8, 12, 8, 16, 16, 24, 32, as in the entry;
  conjecture 1 holds for 3 ≤ k ≤ 7 and conjecture 2 for 1 ≤ k ≤ 7
  (at k = 0 the two values are equal).
-/

namespace OMA.S_oeis_a152763

/-- A152763(n): the number of divisors of the `n`-th Catalan number. -/
def a (n : ℕ) : ℕ := (catalan n).divisors.card

/-- The conjecture of the entry. -/
theorem main :
    (∀ k : ℕ, 3 ≤ k → a (2 ^ k - 1) < a (2 ^ k - 2)) ∧ ∀ k : ℕ, 1 ≤ k → a (2 ^ k - 1) ≠ a (2 ^ k) := by
  sorry

end OMA.S_oeis_a152763
