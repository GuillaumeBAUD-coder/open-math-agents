import Mathlib

/-!
# A383244: Primes of the form p(k)*p(k+1)*(p(k+1) - p(k)) + 1 sorted by increasing k.

Source: https://oeis.org/A383244
Credit: @darealpandaboi

Conjecture: there are infinitely many such primes.

Translation notes.
* p(k) is the k-th prime with p(1) = 2; with Mathlib's 0-indexed Nat.nth Nat.Prime, p(k) and
  p(k+1) are Nat.nth Nat.Prime i and Nat.nth Nat.Prime (i + 1) for i = k - 1 >= 0.
* p(k+1) > p(k), so the natural-number subtraction is exact.
* The statement asks for infinitely many distinct primes of this form.
* This reading reproduces the listed data: 7, 31, 71, 647, 4003, 6883, 3527, 14947, 34603, ...
  (checked by computer).
-/

namespace OMA.S_oeis_a383244

theorem main :
    {q : ℕ | q.Prime ∧ ∃ i : ℕ, q = Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) *
      (Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i) + 1}.Infinite := by
  sorry

end OMA.S_oeis_a383244
