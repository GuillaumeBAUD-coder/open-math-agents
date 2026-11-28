import Mathlib

/-!
# A400000: The city-building sequence

Source: https://oeis.org/A400000
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Let `a(n)` (`n ≥ 0`) be the city-building sequence, where `a(n)` is the least
nonnegative integer `h` such that the point `(n, h)` can see exactly `h` earlier points
`(i, a(i))` (`i < n`) in the natural visibility graph (with collinear points counted as
visible). Then `limsup_{n → ∞} (∑_{k < n} a(k)) / n ≤ 3`.

Conventions:
- For `i < n`, point `(i, a(i))` is visible from `(n, h)` iff no intermediate point
  `(j, a(j))` (`i < j < n`) lies strictly above the line segment from `(i, a(i))` to
  `(n, h)`, i.e., `a(j) * (n - i) ≤ a(i) * (n - j) + h * (j - i)`.
- For a nonnegative sequence `f`, `limsup f ≤ 3` is expressed as
  `∀ ε > 0, ∀ᶠ n in atTop, f n ≤ 3 + ε`.
-/

namespace OMA.S_oeis_a400000

open Filter Classical

/-- Predicate asserting that `a : ℕ → ℕ` is the city-building sequence A400000. -/
def IsCityBuildingSeq (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, IsLeast
    {h : ℕ | ((Finset.range n).filter (fun i =>
      ∀ j : ℕ, i < j → j < n →
        (a j : ℤ) * ((n : ℤ) - (i : ℤ)) ≤
          (a i : ℤ) * ((n : ℤ) - (j : ℤ)) + (h : ℤ) * ((j : ℤ) - (i : ℤ)))).card = h}
    (a n)

theorem main :
    ∀ a : ℕ → ℕ, IsCityBuildingSeq a →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop, ((∑ k ∈ Finset.range n, a k : ℕ) : ℝ) / (n : ℝ) ≤ 3 + ε := by
  sorry

end OMA.S_oeis_a400000
