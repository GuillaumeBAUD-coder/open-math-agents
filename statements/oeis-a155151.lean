import Mathlib

/-!
# OEIS A155151: powers of two in T(n, k) = 4nk + 2n + 2k + 2

Source: https://oeis.org/A155151
Credit: @SudharsanAnimations

A155151 is the triangle `T(n, k) = 4 n k + 2 n + 2 k + 2`, `1 ≤ k ≤ n`, read by rows. Vincenzo
Librandi conjectured: if `p` is prime and `2^p` belongs to the sequence, then `2^p - 1` is not a
Mersenne prime. Michel Marcus recorded the proof: if `T(n, k) = 2^p` then
`2^p - 1 = (2n + 1)(2k + 1)`, a product of two factors `≥ 3`. We state this proved result.

Conventions: the triangle has offset `1`, i.e. `1 ≤ k ≤ n` (so `T(1, 1) = 10`).
-/

namespace OMA.S_oeis_a155151

/-- `T(n, k) = 4 n k + 2 n + 2 k + 2` (OEIS A155151), for `1 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℕ := 4 * n * k + 2 * n + 2 * k + 2

theorem main : ∀ p : ℕ, p.Prime → ∀ n k : ℕ, 1 ≤ k → k ≤ n → T n k = 2 ^ p →
    ¬ (2 ^ p - 1).Prime := by
  sorry

end OMA.S_oeis_a155151
