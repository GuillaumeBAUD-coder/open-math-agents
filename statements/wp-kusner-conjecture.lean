import Mathlib

/-!
# Kusner's conjecture

Source: https://lefttosolve.com/p/wp-kusner-conjecture
Kusner's conjecture: in the `d`-dimensional real vector space with the `L1` metric, at most
`2 * d` points can be pairwise equidistant.
-/

namespace OMA.S_wp_kusner_conjecture

/-- The `L1` distance between two points of `ℝ ^ d`. -/
def l1dist {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  Finset.univ.sum (fun i => |x i - y i|)

/-- Kusner's conjecture: a set of pairwise equidistant points of `ℝ ^ d` for the `L1` metric has
at most `2 * d` elements. -/
theorem main : ∀ (d : ℕ) (S : Set (Fin d → ℝ)), 1 ≤ d →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → l1dist x y = 1) → S.Finite ∧ S.ncard ≤ 2 * d := by
  sorry

end OMA.S_wp_kusner_conjecture
