import Mathlib

/-!
# Mahler's volume-product conjecture

Source: https://en.wikipedia.org/wiki/Mahler_volume
Credit: @biondadave

For every convex body `K ⊂ ℝⁿ` symmetric about the origin, `vol(K) · vol(K°) ≥ 4ⁿ / n!`, where
`K°` is the polar body. Equality holds for the cube and the cross-polytope. Known for `n = 2`
(Mahler) and `n = 3` (Iriyeh–Shibata, 2020).

Conventions:
- `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` with its standard inner product and Lebesgue measure
  `volume`.
- A convex body is a compact convex set with nonempty interior, as on the source page.
- Symmetric about the origin means `x ∈ K → -x ∈ K`.
- The polar body is `K° = {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}`, the standard definition on the source
  page.
- Volumes are compared in `ℝ≥0∞`; for a convex body both volumes are finite and positive.
- The statement is for every `n`. The case `n = 0` holds trivially (both volumes are `1`).
-/

namespace OMA.S_wpc_mahler_conjecture

open MeasureTheory

/-- The polar body of `K ⊆ ℝⁿ`. -/
def polarBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ (1 : ℝ)}

theorem main :
    ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
    IsCompact K → Convex ℝ K → (interior K).Nonempty → (∀ x ∈ K, -x ∈ K) →
    ENNReal.ofReal (4 ^ n / (n.factorial : ℝ)) ≤ volume K * volume (polarBody K) := by
  sorry

end OMA.S_wpc_mahler_conjecture
