import Mathlib

/-!
# Huber's conjecture on integer-area cube rectangles

For a cube of side 4n the rectangle constructed in OEIS A383721 has
side lengths √2(4n−x) and √(2x²+16n²). The construction in the figure
makes sense for every real edge offset 0 < x < 4n. The entry asks if
an integer area in this family forces x to be a positive integer.
Source: Felix Huber, https://oeis.org/A383721.
-/

namespace OMA.S_oeis_a383721

noncomputable def area (n : ℕ) (x : ℝ) : ℝ :=
  2 * (4 * (n : ℝ) - x) * Real.sqrt (x^2 + 8 * (n : ℝ)^2)

theorem main : ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 < x → x < 4 * (n : ℝ) →
    ∀ k : ℕ, area n x = (k : ℝ) → ∃ m : ℕ, 0 < m ∧ x = (m : ℝ) := by
  sorry

end OMA.S_oeis_a383721
