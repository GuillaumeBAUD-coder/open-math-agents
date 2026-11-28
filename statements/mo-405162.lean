import Mathlib

/-!
# Local solubility of `y³ + x y + x⁴ + 4 = 0`

Source: https://mathoverflow.net/questions/405162 (Bogdan Grechuk)
Credit: Sudharsan Rajendiran

The question asks how to check local solubility of a curve in practice, and as its example asks
whether `y³ + x y + x⁴ + 4 = 0` is solvable locally, that is, in `ℚ_p` for every prime `p` (and in
`ℝ`, the place at infinity). The general request (software and methods) is not a mathematical
statement; we formalize the example, which is the precise question in the title.

The accepted answer on the source page shows that the answer is yes. Over `ℝ` take
`(x, y) = (0, -∛4)`. For every prime `p`, Hensel's lemma gives `t ∈ pℤ_p`, `t ≠ 0`, with
`t + p t² + p⁴ + 4 t⁴ = 0`, and then `(x, y) = (p / t, 1 / t)` is a solution in `ℚ_p`.
We state this answer.
-/

namespace OMA.S_mo_405162

/-- `y³ + x y + x⁴ + 4 = 0` has a solution in `ℝ` and in `ℚ_p` for every prime `p`. -/
theorem main : (∃ x y : ℝ, y ^ 3 + x * y + x ^ 4 + 4 = 0) ∧
    ∀ p : ℕ, (hp : p.Prime) →
      haveI : Fact p.Prime := ⟨hp⟩
      ∃ x y : ℚ_[p], y ^ 3 + x * y + x ^ 4 + 4 = 0 := by
  sorry

end OMA.S_mo_405162
