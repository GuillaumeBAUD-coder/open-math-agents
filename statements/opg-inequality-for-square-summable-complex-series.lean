import Mathlib

/-!
# Inequality for square summable complex series

Source: https://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series
Credit: @mburv

Conjecture (Z. Retkes): for all `α = (α₁, α₂, …) ∈ ℓ₂(ℂ)`,
$$\sum_{n\geq 1}|\alpha_n|^2\geq \frac{6}{\pi^2}\sum_{k\geq0}
  \bigg| \sum_{l\geq0}\frac{1}{l+1}\alpha_{2^k(2l+1)}\bigg|^2 .$$

Encoding: the sequence is indexed by the positive integers, so it is given as a function
`α : ℕ → ℂ` whose value at `0` is never used (every index `n + 1` and `2^k (2l+1)` is at least `1`).
Membership in `ℓ₂(ℂ)` is the hypothesis that `∑_{n ≥ 1} |α_n|²` converges.

Reading of the inequality: as stated in the source, both sides are series and the inequality
asserts that the right-hand side is a well-defined (finite) number bounded by the left-hand side.
In Lean an infinite sum `∑'` of a non-summable family is `0`, so the statement asserts explicitly
that every inner series `∑_l α_{2^k(2l+1)} / (l+1)` converges, that the outer series of squared
moduli converges, and that the inequality holds.

Literature note (not part of the statement): the source page records a short solution by the
Cauchy-Schwarz inequality, using that the sets `{2^k(2l+1) : l ≥ 0}` (`k ≥ 0`) partition the
positive integers and `∑_{l ≥ 0} 1/(l+1)² = π²/6`.
-/

namespace OMA.S_opg_inequality_for_square_summable_complex_series

/-- Retkes' inequality for square summable complex sequences indexed by the positive integers. -/
theorem main : ∀ α : ℕ → ℂ, (Summable fun n : ℕ => ‖α (n + 1)‖ ^ 2) →
    (∀ k : ℕ, Summable fun l : ℕ => α (2 ^ k * (2 * l + 1)) / ((l : ℂ) + 1)) ∧
    Summable (fun k : ℕ => ‖∑' l : ℕ, α (2 ^ k * (2 * l + 1)) / ((l : ℂ) + 1)‖ ^ 2) ∧
    6 / Real.pi ^ 2 * ∑' k : ℕ, ‖∑' l : ℕ, α (2 ^ k * (2 * l + 1)) / ((l : ℂ) + 1)‖ ^ 2 ≤
      ∑' n : ℕ, ‖α (n + 1)‖ ^ 2 := by
  sorry

end OMA.S_opg_inequality_for_square_summable_complex_series
