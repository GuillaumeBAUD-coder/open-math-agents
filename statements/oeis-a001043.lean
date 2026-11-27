import Mathlib

/-!
# A001043 — Zhi-Wei Sun's unit fraction conjecture with sums of consecutive primes

Source: https://oeis.org/A001043
Credit: @Andyi955

The OEIS entry A001043 lists the numbers that are the sum of two successive primes. Zhi-Wei Sun's
conjecture recorded there reads: for any positive even number `m`, each positive rational number
can be written as a sum of finitely many distinct unit fractions whose denominators are sums of `m`
consecutive primes; and if `m` is an odd number greater than one, then for any positive integers
`c` and `d` with `d` odd, `c / d` can be written as a sum of finitely many distinct unit fractions
whose denominators are sums of `m` consecutive primes.

## Encoding

* `IsSumOfConsecutivePrimes m d` says `d` is the sum of `m` consecutive primes: there is an index
  `k` with `d = p k + p (k + 1) + ... + p (k + m - 1)`, where `p j = Nat.nth Nat.Prime j` is the
  `j`-th prime (`p 0 = 2`).
* A sum of finitely many distinct unit fractions is a `Finset` of denominators (distinct by
  construction) together with the rational value `∑ d ∈ D, (d : ℚ)⁻¹`.
* The two clauses of the source are kept: the even `m` clause for an arbitrary positive rational
  `q`, and the odd `m > 1` clause for `c / d` with `c`, `d` positive and `d` odd.
* `0 < m` with `Even m` is the source's positive even `m`; `Odd m` with `1 < m` is its odd number
  greater than one.
-/

namespace OMA.S_oeis_a001043

/-- `IsSumOfConsecutivePrimes m d` holds when `d` is a sum of `m` consecutive primes, i.e.
`d = p k + p (k + 1) + ... + p (k + m - 1)` for some `k`, where `p j` is the `j`-th prime. -/
def IsSumOfConsecutivePrimes (m d : ℕ) : Prop :=
  ∃ k : ℕ, d = ∑ i ∈ Finset.range m, Nat.nth Nat.Prime (k + i)

/-- **Zhi-Wei Sun's conjecture (OEIS A001043)**: for every positive even `m`, every positive
rational is a sum of distinct unit fractions with denominators sums of `m` consecutive primes; and
for every odd `m > 1`, every `c / d` with `c`, `d` positive and `d` odd is such a sum. -/
theorem main :
    (∀ m : ℕ, 0 < m → Even m → ∀ q : ℚ, 0 < q →
      ∃ D : Finset ℕ, (∀ d ∈ D, IsSumOfConsecutivePrimes m d) ∧
        ∑ d ∈ D, ((d : ℚ))⁻¹ = q) ∧
      (∀ m : ℕ, Odd m → 1 < m → ∀ c d : ℕ, 0 < c → 0 < d → Odd d →
        ∃ E : Finset ℕ, (∀ e ∈ E, IsSumOfConsecutivePrimes m e) ∧
          ∑ e ∈ E, ((e : ℚ))⁻¹ = (c : ℚ) / (d : ℚ)) := by
  sorry

end OMA.S_oeis_a001043
