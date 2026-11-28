import Mathlib

/-!
# A358319: a gcd-sum formula for a multiplicative sequence

Source: https://oeis.org/A358319 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Werner Schulte, Nov 09 2022), offset 1:
Multiplicative sequence a(n) with a(p^e) = ((p-2) - (p-1) * e) * p^(e-1) for prime p and e > 0.
Data 1, -1, -1, -4, -1, 1, -1, -12, -9, 1, -1, 4, -1, 1, 1, -32, ...

Formula section: Conjecture: a(n) = Sum_{k=1..n} gcd(k, n) * A076479(gcd(k, n)) for n > 0.

Formalization notes.
* A multiplicative sequence is a function `a` on the positive integers with a(1) = 1 and
  a(m n) = a(m) a(n) for coprime m, n. Its values at the prime powers determine it, so `main`
  quantifies over every function `a : ℕ → ℤ` with these properties. The value `a 0` is not used.
* A076479(m) = mu(rad(m)) = (-1)^omega(m), where omega(m) is the number of distinct primes that
  divide m, `ArithmeticFunction.cardDistinctFactors` in Mathlib.
* The prime power rule is used for e > 0 only, as in the entry, so `e - 1` is the true
  subtraction.
-/

namespace OMA.S_oeis_a358319

/-- Schulte's conjecture: a(n) = Sum_{k=1..n} gcd(k, n) * A076479(gcd(k, n)) for n > 0. -/
theorem main : ∀ a : ℕ → ℤ, a 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n) →
    (∀ p e : ℕ, p.Prime → 0 < e →
      a (p ^ e) = (((p : ℤ) - 2) - ((p : ℤ) - 1) * e) * (p : ℤ) ^ (e - 1)) →
    ∀ n : ℕ, 0 < n →
      a n = ∑ k ∈ Finset.Icc 1 n,
        (Nat.gcd k n : ℤ) * (-1) ^ (ArithmeticFunction.cardDistinctFactors (Nat.gcd k n)) := by
  sorry

end OMA.S_oeis_a358319
