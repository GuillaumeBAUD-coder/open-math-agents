import Mathlib

/-!
# OEIS A028576: divisibility of (1/(4n)) Sum_{d|n} mu(n/d) binomial(2d,d)^2

Source: https://oeis.org/A028576
Credit: @sntntHb

A028576: `a(n) = (1/(4*n)) * Sum_{d|n} mu(n/d) * binomial(2*d, d)^2` (offset 1).

F. Chapoton (Feb 25 2026) conjectures: `a(n)` is divisible by `n` and `3*a(n)` by `n^2`.

Formalized: `S n` is the integer `Sum_{d|n} mu(n/d) * binomial(2*d, d)^2` and `a n` is `S n`
divided by `4*n` (the sequence is integral, so this division is exact). `main` states that for
every `n >= 1`, `n` divides `a n` and `n^2` divides `3 * a n`.
-/

namespace OMA.S_oeis_a028576

/-- `Sum_{d|n} mu(n/d) * binomial(2*d, d)^2`. -/
def S (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * ((2 * d).choose d : ℤ) ^ 2

/-- `a(n) = S(n) / (4*n)`. -/
def a (n : ℕ) : ℤ := S n / (4 * n)

theorem main : ∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ a n ∧ (n : ℤ) ^ 2 ∣ 3 * a n := by
  sorry

end OMA.S_oeis_a028576
