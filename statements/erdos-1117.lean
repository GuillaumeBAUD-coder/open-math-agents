import Mathlib

/-!
# Erdős Problem 1117

Source: https://www.erdosproblems.com/1117
Credit: @joshuadc11

Let `f(z)` be an entire function which is not a monomial. Let `ν(r)` count the number of `z`
with `|z| = r` such that `|f(z)| = max_{|w| = r} |f(w)|`.
The first question (whether `limsup_{r → ∞} ν(r) = ∞` is possible) was answered affirmatively by
Herzog and Piranian (1968). The remaining open question is whether `liminf_{r → ∞} ν(r) = ∞` is
possible.

Formalization notes:
- Entire functions are represented by `Differentiable ℂ f`.
- `maxModCount f r` is defined as the `ℕ∞`-cardinality (`Set.encard`) of the set of points on
  the circle `‖z‖ = r` attaining the maximum modulus of `f` on that circle.
- `liminf_{r → ∞} ν(r) = ∞` is stated as: for every `M : ℕ`, there exists `R : ℝ` such that
  `M ≤ maxModCount f r` for all `r ≥ R`.
-/

namespace OMA.S_erdos_1117

/-- The number of points `z` on the circle `‖z‖ = r` where `‖f z‖` attains its maximum
on that circle. -/
noncomputable def maxModCount (f : ℂ → ℂ) (r : ℝ) : ℕ∞ :=
  {z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}.encard

theorem main :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (¬ ∃ (c : ℂ) (n : ℕ), ∀ z : ℂ, f z = c * z ^ n) ∧
      ∀ M : ℕ, ∃ R : ℝ, ∀ r ≥ R, (M : ℕ∞) ≤ maxModCount f r := by
  sorry

end OMA.S_erdos_1117
