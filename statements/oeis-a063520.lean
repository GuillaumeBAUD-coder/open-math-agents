import Mathlib

/-!
# OEIS A063520: when the sum divides the product

Source: https://oeis.org/A063520
`a n` is the number of solutions `(r, s, t)`, `r ≥ s ≥ t > 0`, of `r s t = n (r + s + t)`.
David W. Wilson conjectured that the positive integers occurring as values of `a` are exactly
those other than `2, 4, 7, 11`. The published initial counts are `1, 3, 6, 5, 8`.

For fixed positive `n` the solution set is finite: the equation implies `s * t ≤ 3 * n`
and `r * (s * t - n) = n * (s + t)`, with `s * t - n ≥ 1`. Hence `s, t ≤ 3 * n` and
`r ≤ 6 * n²`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a063520

/-- Number of ordered-by-size triples solving the equation at index `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {p : ℕ × ℕ × ℕ | let (r, s, t) := p
    0 < t ∧ t ≤ s ∧ s ≤ r ∧ r * s * t = n * (r + s + t)}.ncard

theorem main :
    ∀ k : ℕ, 1 ≤ k → ((∃ n : ℕ, 1 ≤ n ∧ a n = k) ↔
      k ≠ 2 ∧ k ≠ 4 ∧ k ≠ 7 ∧ k ≠ 11) := by
  sorry

end OMA.S_oeis_a063520
