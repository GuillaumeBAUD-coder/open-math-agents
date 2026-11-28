import Mathlib

/-!
# OEIS A386655

Expansion of e.g.f. `Sum_{n >= 0} (2^n * x + LambertW(x))^n / n!`, with explicit formula
`a(n) = 2^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 2^(k * (k + 1)) * (2^k - (n - k))^(n - k - 1)`.
(First terms: `1, 3, 23, 708, 82677, 39043808, 75384175459, ...`)

Conjecture:
For all `n >= 6`, `a(n) (mod 6)` equals `[1, 0, 3, 0, 3, 2]` repeating
(i.e., `a(n) % 6` is `1, 0, 3, 0, 3, 2` for `n % 6 = 0, 1, 2, 3, 4, 5` respectively).
-/

namespace OMA.S_oeis_a386655

/-- Sequence A386655:
`a(n) = 2^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 2^(k * (k + 1)) * (2^k - (n - k))^(n - k - 1)`. -/
def a (n : ℕ) : ℤ :=
  (2 : ℤ) ^ (n ^ 2) +
    ∑ k ∈ Finset.range n,
      (Nat.choose n k : ℤ) * (2 : ℤ) ^ (k * (k + 1)) *
        ((2 : ℤ) ^ k - ((n - k : ℕ) : ℤ)) ^ (n - k - 1)

/-- The conjectured repeating pattern `[1, 0, 3, 0, 3, 2]` for `n % 6 = 0, 1, 2, 3, 4, 5`. -/
def targetMod6 (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0
  | 4 => 3
  | _ => 2

theorem main :
    ∀ n : ℕ, 6 ≤ n → a n ≡ targetMod6 n [ZMOD 6] := by
  sorry

end OMA.S_oeis_a386655
