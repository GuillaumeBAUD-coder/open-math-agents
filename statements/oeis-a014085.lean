import Mathlib

/-!
# A014085: Number of primes between n^2 and (n+1)^2.

Source: https://oeis.org/A014085
Credit: @tczyzycki

The entry records three open conjectures, stated here as a conjunction:

1. Legendre's conjecture: for every integer `n > 0`, there is at least one prime between `n^2`
   and `(n + 1)^2` (equivalently `a(n) > 0`, since squares are never prime).

2. T. D. Noe (Sep 05 2008): generalization of Legendre's conjecture — for all integers `n > 0`
   and all real numbers `k > log(127) / log(16)`, there is a prime strictly between `n^k` and
   `(n + 1)^k`. (At `k = log(127) / log(16)` and `n = 15`, `(15^k, 16^k) = (113.38..., 127)`
   contains no prime, so the open interval is the standard reading.)

3. Alain Rocchelli (Sep 20 2023): for all integers `n > 1`,
   `|a(n) - n / log(n)| < sqrt(n)`.
-/

namespace OMA.S_oeis_a014085

/-- `A014085(n)`: the number of primes between `n^2` and `(n + 1)^2`
    (equivalently `π((n + 1)^2) - π(n^2)` since squares are never prime). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime).card

theorem main :
    -- Conjecture 1 (Legendre): for every n > 0, there is a prime between n^2 and (n + 1)^2.
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
    -- Conjecture 2 (T. D. Noe): for every n > 0 and every real k > log(127) / log(16),
    -- there is a prime strictly between n^k and (n + 1)^k.
    (∀ n : ℕ, 0 < n → ∀ k : ℝ, Real.log 127 / Real.log 16 < k →
      ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) < ((n + 1 : ℕ) : ℝ) ^ k) ∧
    -- Conjecture 3 (Alain Rocchelli): for every n > 1, |a(n) - n / log(n)| < sqrt(n).
    (∀ n : ℕ, 1 < n →
      |(a n : ℝ) - (n : ℝ) / Real.log (n : ℝ)| < Real.sqrt (n : ℝ)) := by
  sorry

end OMA.S_oeis_a014085
