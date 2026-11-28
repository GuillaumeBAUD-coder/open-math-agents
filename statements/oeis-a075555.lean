import Mathlib

/-!
# A075555: Smallest prime p such that p+n is a square, or 0 if no such p exists.

Source: https://oeis.org/A075555
Credit: @darealpandaboi

Conjecture: a(n) = 0 only when n has the form ((k-1)/2)^2 with k odd but not prime (for such n,
a(n) = 0 is known); this would follow from Schinzel's hypothesis.

Translation notes.
* a(n) = 0 means no prime p makes p + n a square. Offset 1, so n >= 1; k = 1 gives n = 0, which
  is excluded by n >= 1.
* Both directions are stated, as an equality of sets of n >= 1: the zeros are exactly the
  numbers ((k-1)/2)^2 with k odd and not prime.
* This reproduces the listed data, and for 1 <= n < 3000 the zeros are exactly these numbers
  16, 49, 100, 144, 169, ... (checked by computer).
-/

namespace OMA.S_oeis_a075555

theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ p : ℕ, p.Prime ∧ IsSquare (p + n)} =
      {n : ℕ | 1 ≤ n ∧ ∃ k : ℕ, Odd k ∧ ¬ k.Prime ∧ n = ((k - 1) / 2) ^ 2} := by
  sorry

end OMA.S_oeis_a075555
