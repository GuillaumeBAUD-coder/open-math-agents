import Mathlib

/-!
# Erdös-Szekeres conjecture

Source: https://www.openproblemgarden.org/op/erdos_szekeres_conjecture
Credit: @joshuadc11

Erdős–Szekeres (Happy Ending) conjecture: for every `n ≥ 3`, every set of `2 ^ (n - 2) + 1`
points in the plane in general position contains `n` points forming the vertices of a convex
`n`-gon.

## Encoding

* Points in the plane are elements of `ℝ × ℝ`.
* General position means no three distinct points of `S` are collinear, expressed using Mathlib's
  `Collinear ℝ`.
* A set `T` of `n` points in general position forms a convex `n`-gon (convex position) iff no
  point `p ∈ T` lies in `convexHull ℝ (T.erase p : Set (ℝ × ℝ))`.
-/

namespace OMA.S_opg_erdos_szekeres_conjecture

/-- Every set of `2 ^ (n - 2) + 1` points in `ℝ²` in general position (`n ≥ 3`) contains `n`
points in convex position (forming a convex `n`-gon). -/
theorem main : ∀ n : ℕ, 3 ≤ n → ∀ S : Finset (ℝ × ℝ),
    S.card = 2 ^ (n - 2) + 1 →
    (∀ T ⊆ S, T.card = 3 → ¬ Collinear ℝ (T : Set (ℝ × ℝ))) →
    ∃ T ⊆ S, T.card = n ∧
      ∀ p ∈ T, p ∉ convexHull ℝ ((T.erase p : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
  sorry

end OMA.S_opg_erdos_szekeres_conjecture
