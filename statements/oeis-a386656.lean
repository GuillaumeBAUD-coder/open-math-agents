import Mathlib

/-!
# OEIS A386656

Expansion of e.g.f. `Sum_{n >= 0} (3^n * x + LambertW(x))^n / n!`, with explicit formula
`a(n) = 3^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 3^(k * (k + 1)) * (3^k - (n - k))^(n - k - 1)`
(equivalently `Sum_{k = 0..n} binomial(n, k) * 3^(k * (k + 1)) * (3^k - (n - k))^(n - k - 1)`
where the `k = n` term is `3^(n * (n + 1)) * (3^n)^(-1) = 3^(n^2)`).
(First terms: `1, 4, 98, 21901, 45203076, 864855654349, ...`)

Conjecture:
For all `n >= 6`, `a(n) (mod 6)` equals `[4, 3, 2, 1, 0, 1]` repeating
(i.e., `a(n) % 6` is `4, 3, 2, 1, 0, 1` for `n % 6 = 0, 1, 2, 3, 4, 5` respectively).
-/

namespace OMA.S_oeis_a386656

/-- Sequence A386656:
`a(n) = 3^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 3^(k * (k + 1)) * (3^k - (n - k))^(n - k - 1)`. -/
def a (n : ℕ) : ℤ :=
  (3 : ℤ) ^ (n ^ 2) +
    ∑ k ∈ Finset.range n,
      (Nat.choose n k : ℤ) * (3 : ℤ) ^ (k * (k + 1)) *
        ((3 : ℤ) ^ k - ((n - k : ℕ) : ℤ)) ^ (n - k - 1)

/-- The conjectured repeating pattern `[4, 3, 2, 1, 0, 1]` for `n % 6 = 0, 1, 2, 3, 4, 5`. -/
def targetMod6 (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 4
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | 4 => 0
  | _ => 1

theorem main :
    ∀ n : ℕ, 6 ≤ n → a n ≡ targetMod6 n [ZMOD 6] := by
  sorry

end OMA.S_oeis_a386656
