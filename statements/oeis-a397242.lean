import Mathlib

namespace OMA.S_oeis_a397242

/-- OEIS A397242: O.g.f. satisfies `A(x) = exp(x + ∑_{n ≥ 2} (n^2 - 1) * a(n) * x^n / n^2)`,
equivalently `a(0) = 1`, `a(1) = 1`, and for `n ≥ 2`,
`a(n) = n * (a(n - 1) + ∑_{k=2}^{n-1} ((k^2 - 1) / k) * a(k) * a(n - k))`.
Conjectures:
1. `a(n)` is odd iff `n + 1` is a power of `2`.
2. For `n > 0`, `a(n) ≡ 1 (mod 3)` iff `n + 2` is of the form `3^k` or `2 * 3^k`.
3. For `n > 0`, `a(n) ≡ 2 (mod 3)` iff `n + 2` is a sum of two distinct powers of `3`. -/
theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      a 1 = 1 →
      (∀ n : ℕ, 2 ≤ n →
        (a n : ℚ) = (n : ℚ) * ((a (n - 1) : ℚ) +
          ∑ k ∈ Finset.Icc 2 (n - 1),
            ((k ^ 2 - 1 : ℕ) : ℚ) / (k : ℚ) * (a k : ℚ) * (a (n - k) : ℚ))) →
      (∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k) ∧
      (∀ n : ℕ, 1 ≤ n →
        ((a n : ZMod 3) = 1 ↔ (∃ k : ℕ, n + 2 = 3 ^ k) ∨ (∃ k : ℕ, n + 2 = 2 * 3 ^ k))) ∧
      (∀ n : ℕ, 1 ≤ n →
        ((a n : ZMod 3) = 2 ↔ ∃ j k : ℕ, j < k ∧ n + 2 = 3 ^ j + 3 ^ k)) := by
  sorry

end OMA.S_oeis_a397242
