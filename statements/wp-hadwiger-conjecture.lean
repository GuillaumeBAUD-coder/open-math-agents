import Mathlib

/-!
# Hadwiger's covering conjecture

Source: https://lefttosolve.com/p/wp-hadwiger-conjecture
Hadwiger's conjecture: every convex body in `n`-dimensional Euclidean space can be covered by
`2 ^ n` smaller homothetic copies of itself, that is, by copies of the form `t + c • K` with
ratio `c < 1`.
-/

namespace OMA.S_wp_hadwiger_conjecture

/-- A convex body: a compact convex set with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- The homothetic copy of `K` with centre `t` and ratio `c`. -/
def homothet {n : ℕ} (t : Fin n → ℝ) (c : ℝ) (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ y ∈ K, x = t + c • y}

/-- Hadwiger's covering conjecture: a convex body in `ℝ ^ n` is covered by `2 ^ n` smaller
homothetic copies of itself. -/
theorem main : ∀ (n : ℕ) (K : Set (Fin n → ℝ)), IsConvexBody K →
    ∃ (c : Fin (2 ^ n) → ℝ) (t : Fin (2 ^ n) → (Fin n → ℝ)),
      (∀ i, c i < 1) ∧ K ⊆ ⋃ i, homothet (t i) (c i) K := by
  sorry

end OMA.S_wp_hadwiger_conjecture
