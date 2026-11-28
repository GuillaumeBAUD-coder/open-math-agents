import Mathlib

/-!
# A364514: supercongruences for [x^n] (1 - x)^(2n) P_(n-1)((1 + x)/(1 - x))

Source: https://oeis.org/A364514 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A364514 (offset 0): a(0) = 1 and a(n) = [x^n] (1 - x)^(2*n) * Legendre_P(n-1, (1 + x)/(1 - x))
for n >= 1; data 1, -2, 0, 16, 0, -252, 0, 4800, 0, -100100, ...

The entry gives the closed form

  a(n) = Sum_{k = 0..n} (-1)^k * binomial(n-1, n-k)^2 * binomial(n+1, k)

and records (Peter Bala):

  Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes
  p >= 5 and all positive integers n and r.

Reading of the source:
* `a n` is defined by the entry's closed form, as an integer, for `n ≥ 1` (the only arguments the
  conjecture uses, since `n, r ≥ 1`). With natural subtraction the formula also gives a(0) = 1.
  (Check: a(1) = -C(0,0)^2 C(2,1) = -2, as in the data.)
* The congruence is in `ℤ`: `p^(3r)` divides `a(n p^r) - a(n p^(r-1))`.
-/

namespace OMA.S_oeis_a364514

/-- A364514(n) = ∑_{k=0}^{n} (-1)^k C(n-1, n-k)^2 C(n+1, k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ k * ((n - 1).choose (n - k) : ℤ) ^ 2 * ((n + 1).choose k : ℤ)

/-- Bala's conjecture: `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`, `n, r ≥ 1`. -/
theorem main :
    ∀ p n r : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ r →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a364514
