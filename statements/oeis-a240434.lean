import Mathlib

/-!
# OEIS A240434: closed form of the binomial transform of the sums of even squares

Source: https://oeis.org/A240434
Credit: @SudharsanAnimations

A240434 is the binomial transform of A002492, the sum of the first `n` even squares. Colin Barker
conjectured (Apr 2014) `a(n) = 2^(n-1) n (5 + 6n + n^2)/3` and the g.f. `-4x(x-1)/(2x-1)^4`. We state
the closed form (the g.f. is equivalent to it).

Conventions: `s(k) = ∑_{i=1}^{k} (2i)^2`, `a(n) = ∑_{k=0}^{n} C(n, k) s(k)`, offset `0`;
`/` is natural-number division (exact here), and `2^(n-1)` uses natural-number subtraction
(the `n = 0` term is `0` either way).
-/

namespace OMA.S_oeis_a240434

/-- A002492: the sum of the first `k` even squares, `∑_{i=1}^{k} (2i)^2`. -/
def s (k : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 k, (2 * i) ^ 2

/-- A240434: the binomial transform of A002492, `a(n) = ∑_{k=0}^{n} C(n, k) s(k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * s k

theorem main : ∀ n : ℕ, a n = 2 ^ (n - 1) * n * (5 + 6 * n + n ^ 2) / 3 := by
  sorry

end OMA.S_oeis_a240434
