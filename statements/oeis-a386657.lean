import Mathlib

/-!
# OEIS A386657

Expansion of e.g.f. `Sum_{n >= 0} (4^n * x + LambertW(x))^n / n!`, with explicit formula
`a(n) = 4^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 4^(k * (k + 1)) * (4^k - (n - k))^(n - k - 1)`.
(First terms: `1, 5, 287, 274532, 4362420261, 1131407873777920, ...`)

Conjecture:
For all `n >= 6`, `a(n) (mod 6)` equals `[1, 2, 3, 2, 3, 4]` repeating
(i.e., `a(n) % 6` is `1, 2, 3, 2, 3, 4` for `n % 6 = 0, 1, 2, 3, 4, 5` respectively).
-/

namespace OMA.S_oeis_a386657

/-- Sequence A386657:
`a(n) = 4^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 4^(k * (k + 1)) * (4^k - (n - k))^(n - k - 1)`. -/
def a (n : ℕ) : ℤ :=
  (4 : ℤ) ^ (n ^ 2) +
    ∑ k ∈ Finset.range n,
      (Nat.choose n k : ℤ) * (4 : ℤ) ^ (k * (k + 1)) *
        ((4 : ℤ) ^ k - ((n - k : ℕ) : ℤ)) ^ (n - k - 1)

/-- The conjectured repeating pattern `[1, 2, 3, 2, 3, 4]` for `n % 6 = 0, 1, 2, 3, 4, 5`. -/
def targetMod6 (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 3
  | _ => 4

theorem main :
    ∀ n : ℕ, 6 ≤ n → a n ≡ targetMod6 n [ZMOD 6] := by
  sorry

end OMA.S_oeis_a386657
