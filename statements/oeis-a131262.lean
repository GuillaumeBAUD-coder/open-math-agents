import Mathlib

namespace OMA.S_oeis_a131262

/-- The `k`-th odd-index Taylor coefficient of `tan(x)`:
`[x^(2k-1)] tan(x) = (-1)^(k-1) * 2^(2k) * (2^(2k) - 1) * B_(2k) / (2k)!`. -/
def tanCoeff (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ (k - 1) * (2 : ℚ) ^ (2 * k) * ((2 : ℚ) ^ (2 * k) - 1) *
    bernoulli (2 * k) / (Nat.factorial (2 * k) : ℚ)

/-- OEIS A002430: Numerators in the Taylor series for `tan(x)`. -/
def A002430 (k : ℕ) : ℕ := (tanCoeff k).num.natAbs

/-- OEIS A046990: Numerators in the Taylor series for `log(1 / cos(x))`,
whose `[x^(2k)]` coefficient is `tanCoeff(k) / (2k)`. -/
def A046990 (k : ℕ) : ℕ := (tanCoeff k / ((2 * k : ℕ) : ℚ)).num.natAbs

/-- OEIS A092505: `A002430(k) / A046990(k)`. -/
def A092505 (k : ℕ) : ℕ := A002430 k / A046990 k

/-- OEIS A130654: 2-adic valuation of `A092505(k) = A002430(k) / A046990(k)`. -/
noncomputable def A130654 (k : ℕ) : ℕ := padicValNat 2 (A092505 k)

/-- Conjecture (OEIS A131262):
For every `n : ℕ`, the least index `k ≥ 1` such that `A130654(k) = n` is
`k₀ = 2^(2n) - ⌊2^n / 2⌋ = σ(2^n) * φ(2^n)`. -/
theorem main :
    ∀ n : ℕ,
      let k₀ := 2 ^ (2 * n) - 2 ^ n / 2
      k₀ = (∑ d ∈ (2 ^ n).divisors, d) * Nat.totient (2 ^ n) ∧
      1 ≤ k₀ ∧
      A130654 k₀ = n ∧
      ∀ k : ℕ, 1 ≤ k → k < k₀ → A130654 k ≠ n := by
  sorry

end OMA.S_oeis_a131262
