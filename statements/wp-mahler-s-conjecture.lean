import Mathlib

/-!
# Mahler's conjecture (Mahler volume)

Source: https://en.wikipedia.org/wiki/Mahler_volume
Credit: @joshuadc11

For every `n ≥ 1` and every centrally symmetric convex body `K ⊆ ℝⁿ`, the Mahler volume
`vol(K) * vol(K°)` satisfies `vol(K) * vol(K°) ≥ 4^n / n!`, where
`K° = {y ∈ ℝⁿ | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}` is the polar body of `K`.

Formalization notes:
- `ℝⁿ` is represented as `Fin n → ℝ` with standard Lebesgue measure `MeasureTheory.volume`
  and standard inner product `∑ i : Fin n, x i * y i`.
- A centrally symmetric convex body is a compact, convex set `K` with nonempty interior
  satisfying `∀ x ∈ K, -x ∈ K`.
- The inequality is stated in `ENNReal` (`MeasureTheory.volume` takes values in `ENNReal`).
-/

namespace OMA.S_wp_mahler_s_conjecture

/-- The polar body `K° = {y ∈ ℝⁿ | ∀ x ∈ K, ∑ i, x i * y i ≤ 1}`. -/
def polarBody {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y : Fin n → ℝ | ∀ x ∈ K, (∑ i : Fin n, x i * y i) ≤ 1}

theorem main :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ K : Set (Fin n → ℝ),
        IsCompact K →
        Convex ℝ K →
        (interior K).Nonempty →
        (∀ x ∈ K, -x ∈ K) →
        ENNReal.ofReal ((4 : ℝ) ^ n / (Nat.factorial n : ℝ)) ≤
          MeasureTheory.volume K * MeasureTheory.volume (polarBody K) := by
  sorry

end OMA.S_wp_mahler_s_conjecture
