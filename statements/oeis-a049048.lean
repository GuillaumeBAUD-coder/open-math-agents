import Mathlib

/-!
# A049048: Composite numbers n such that k! == 1 (mod n) for some k > 2.

Source: https://oeis.org/A049048
Credit: @ghaffaria

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a049048

/-- David Wilson's conjecture: for composite `c`, at most one `n ≥ 2`
satisfies `n! ≡ 1 (mod c)`. -/
theorem main : ∀ c : ℕ, 2 ≤ c → ¬ c.Prime →
    {n : ℕ | 2 ≤ n ∧ n.factorial ≡ 1 [MOD c]}.Subsingleton := by
  sorry

end OMA.S_oeis_a049048

