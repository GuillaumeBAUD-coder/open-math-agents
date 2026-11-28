import Mathlib

/-!
# OEIS A386649

Product of the first `n` central trinomial coefficients `A002426(k) = [x^k] (1 + x + x^2)^k`:
`a(n) = Product_{k = 0..n} A002426(k)` for `n >= 0`.
(First terms: `1, 1, 3, 21, 399, 20349, 2869209, ...`)

Conjecture:
For all `n >= 1`, `a(n) = A214589(n) - 2`, equivalently `A214589(n) = a(n) + 2`, where
`A214589(n)` is the number of `n × n × n` triangular `0..2` arrays (row `k` having `k + 1`
entries in `{0, 1, 2}` for `0 <= k < n`) such that every horizontal row has the same average value.
-/

namespace OMA.S_oeis_a386649

/-- Central trinomial coefficient `A002426(k) = [x^k] (1 + x + x^2)^k`. -/
noncomputable def centralTrinomial (k : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ k).coeff k

/-- Sequence A386649: `a(n) = Product_{k = 0..n} A002426(k)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (n + 1), centralTrinomial k

/-- Number of `n × n × n` triangular `0..2` arrays with every horizontal row having the same
average value (OEIS A214589). -/
noncomputable def A214589 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun T : (k : Fin n) → Fin (k.1 + 1) → Fin 3 =>
    ∀ k1 k2 : Fin n,
      (k2.1 + 1) * (∑ j : Fin (k1.1 + 1), (T k1 j).1) =
        (k1.1 + 1) * (∑ j : Fin (k2.1 + 1), (T k2 j).1)).card

theorem main :
    ∀ n : ℕ, 1 ≤ n → A214589 n = a n + 2 := by
  sorry

end OMA.S_oeis_a386649
