import Mathlib

/-!
# A002072: a(n) = smallest number m such that for all k > m, either k or k+1 has a prime factor > prime(n).

Source: https://oeis.org/A002072
Credit: @tczyzycki

Here `a(n)` (for `n ≥ 1`, 1-indexed as in OEIS with `prime(1) = 2`) is the smallest `m : ℕ`
such that every `k > m` has a prime factor `> prime(n)` dividing `k` or `k + 1` (by Størmer's
theorem, the set of such `m` is nonempty for every `n ≥ 1`).

The entry states two claims, recorded here as a conjunction:

1. Lucas A. Brown (Sep 20 2020): the effective abc conjecture `c < rad(abc)^2` (for coprime
   positive integers `a + b = c`) implies `a(27) = a(28) = a(29) = a(30) = a(31) = a(32)` and
   `a(33) = 124225935845233319439173`.

2. M. F. Hasler (Jan 16 2015): `a(n) < 10^n / n` for all `n ≥ 1` except `n = 4`
   (written equivalently as `n * a(n) < 10^n` over `ℕ`, avoiding floor truncation).
-/

namespace OMA.S_oeis_a002072

/-- The `n`-th prime, 1-indexed (`nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- `A002072(n)`: the least `m : ℕ` such that for all `k > m`, either `k` or `k + 1`
    has a prime factor strictly greater than `prime(n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ k : ℕ, m < k →
    ∃ p : ℕ, p.Prime ∧ nthPrime n < p ∧ (p ∣ k ∨ p ∣ k + 1)}

/-- The radical of a natural number: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

theorem main :
    -- Claim 1 (Lucas A. Brown, Sep 20 2020): effective abc (c < rad(abc)^2) implies
    -- a(27) = a(28) = ... = a(32) and a(33) = 124225935845233319439173.
    ((∀ x y z : ℕ, 0 < x → 0 < y → Nat.Coprime x y → x + y = z →
        z < rad (x * y * z) ^ 2) →
      a 27 = a 28 ∧ a 28 = a 29 ∧ a 29 = a 30 ∧ a 30 = a 31 ∧ a 31 = a 32 ∧
      a 33 = 124225935845233319439173) ∧
    -- Conjecture 2 (M. F. Hasler, Jan 16 2015): a(n) < 10^n / n for all n ≥ 1 with n ≠ 4.
    (∀ n : ℕ, 1 ≤ n → n ≠ 4 → n * a n < 10 ^ n) := by
  sorry

end OMA.S_oeis_a002072
