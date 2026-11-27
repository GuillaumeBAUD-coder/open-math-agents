import Mathlib

/-!
# A032357: Convolution of Catalan numbers and powers of -1.

Source: https://oeis.org/A032357
Credit: @bnb9001

The sequence has offset 0: a(n) = Sum_{k=0..n} (-1)^(n-k) C(k), with C(k) the Catalan numbers
(Mathlib's `catalan`); it starts 1, 0, 2, 3, 11, 31, ...

Conjecture (R. J. Mathar, 2012): (n+1) a(n) + 3(-n+1) a(n-1) + 2(-2n+1) a(n-2) = 0. Robert Israel
notes that the conjecture is true. The recurrence involves a(n-2), so we state it for `n ≥ 2`.
-/

namespace OMA.S_oeis_a032357

/-- A032357: `a n = ∑_{k ≤ n} (-1)^(n-k) C(k)`. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (catalan k : ℤ)

/-- For every `n ≥ 2`, `(n+1) a(n) + 3(-n+1) a(n-1) + 2(-2n+1) a(n-2) = 0`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-(n : ℤ) + 1) * a (n - 1) + 2 * (-2 * (n : ℤ) + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a032357
