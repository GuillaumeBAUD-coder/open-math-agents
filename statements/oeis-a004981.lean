import Mathlib

/-!
# A004981: a(n) = (2^n/n!) * Product_{k=0..n-1} (4*k + 1).

Source: https://oeis.org/A004981
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a004981

/-- The OEIS sequence `a(n) = (2^n/n!) * ∏_{k=0}^{n-1} (4*k + 1)`. -/
def a (n : ℕ) : ℕ :=
  (2 ^ n * ∏ k ∈ Finset.range n, (4 * k + 1)) / Nat.factorial n

/-- Peter Bala's conjecture: for every prime `p` congruent to `1` modulo `4` and
every positive integer `n`, `a(p*n)` is congruent to `a(n)` modulo `p^2`. -/
theorem main :
    ∀ p n : ℕ, p.Prime → p ≡ 1 [MOD 4] → 0 < n →
      a (p * n) ≡ a n [MOD p ^ 2] := by
  sorry

end OMA.S_oeis_a004981
