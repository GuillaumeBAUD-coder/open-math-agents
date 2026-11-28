import Mathlib

/-!
# A358272: a gcd-sum formula for the signed square part

Source: https://oeis.org/A358272 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Werner Schulte, Nov 07 2022), offset 1:
Multiplicative sequence with a(p^e) = (-1)^e * p^(2*floor(e/2)) for prime p and e >= 0. Data
1, -1, -1, 4, -1, 1, -1, -4, 9, 1, -1, -4, -1, 1, 1, 16, ...

Formula section: Conjecture: a(n) = Sum_{k=1..n} gcd(k, n) * lambda(gcd(k, n)) for n > 0.

Formalization notes.
* A multiplicative sequence is a function `a` on the positive integers with a(1) = 1 and
  a(m n) = a(m) a(n) for coprime m, n. Its values at the prime powers determine it, so `main`
  quantifies over every function `a : ℕ → ℤ` with these properties. The value `a 0` is not used.
* lambda is the Liouville function A008836, `ArithmeticFunction.liouville` in Mathlib:
  lambda(m) = (-1)^Omega(m), where Omega counts the prime factors with multiplicity.
* floor(e/2) is the quotient `e / 2` of natural numbers.
-/

namespace OMA.S_oeis_a358272

/-- Schulte's conjecture: a(n) = Sum_{k=1..n} gcd(k, n) * lambda(gcd(k, n)) for n > 0. -/
theorem main : ∀ a : ℕ → ℤ, a 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n) →
    (∀ p e : ℕ, p.Prime → a (p ^ e) = (-1) ^ e * (p : ℤ) ^ (2 * (e / 2))) →
    ∀ n : ℕ, 0 < n →
      a n = ∑ k ∈ Finset.Icc 1 n,
        (Nat.gcd k n : ℤ) * ArithmeticFunction.liouville (Nat.gcd k n) := by
  sorry

end OMA.S_oeis_a358272
