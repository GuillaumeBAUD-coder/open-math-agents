import Mathlib

/-!
# Tietze extension theorem for lower semi continuous functions

Source: https://mathoverflow.net/questions/295497
Credit: @ivillar

Status: true (elementary). A comment on the question answers yes for bounded functions; in fact
no boundedness is needed: extend `f` by `1 / dist(x, A)` off the closed set `A`. This blows up
near `A`, so lower semicontinuity at the points of `A` is preserved.

On the Tietze extension theorem, if instead of a continuous function "f" we use a lower semi
continuous function on a closed subspace of a metric space, is the theorem correct? I mean, can
we extend every lower semi continuous function from a closed subspace of a metric space to the
space?

Formalization notes:
* `A` is a closed subset of a metric space `X`, and `f : A → ℝ` is lower semicontinuous for the
  subspace topology.
* `main` asserts that `f` has a lower semicontinuous extension `F : X → ℝ`.
-/

namespace OMA.S_mo_295497

theorem main : ∀ (X : Type) [MetricSpace X] (A : Set X), IsClosed A →
    ∀ f : A → ℝ, LowerSemicontinuous f →
      ∃ F : X → ℝ, LowerSemicontinuous F ∧ ∀ a : A, F a = f a := by
  sorry

end OMA.S_mo_295497
