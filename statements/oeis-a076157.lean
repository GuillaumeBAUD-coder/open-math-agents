import Mathlib

namespace OMA.S_oeis_a076157

open BigOperators

/-- Gauss continued-fraction remainder map: `cfStep x 0 = x`,
`cfStep x (k + 1) = (cfStep x k - ⌊cfStep x k⌋)⁻¹`. -/
noncomputable def cfStep (x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => (cfStep x k - (⌊cfStep x k⌋ : ℝ))⁻¹

/-- The `k`-th partial quotient (0-indexed) of the simple continued fraction of `x : ℝ`. -/
noncomputable def cfCoeff (x : ℝ) (k : ℕ) : ℤ :=
  ⌊cfStep x k⌋

/-- The constant `c = ∑'_{k : ℕ} 1 / 2^(k!)` of OEIS A076157. -/
noncomputable def liouvilleTwo : ℝ :=
  ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (Nat.factorial k)

/-- Conjecture on OEIS A076157 (1-indexed `a(3*2^n) = 2^((n+1)*(n+2)!) - 1`, i.e.
0-indexed `cfCoeff liouvilleTwo (3 * 2^n - 1) = 2^((n+1)*(n+2)!) - 1` for all `n ≥ 1`):
follows from Shallit's Folding Lemma for `c = ∑_{k ≥ 0} 1 / 2^(k!)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      cfCoeff liouvilleTwo (3 * 2 ^ n - 1) =
        ((2 ^ ((n + 1) * Nat.factorial (n + 2)) - 1 : ℕ) : ℤ) := by
  sorry

end OMA.S_oeis_a076157
