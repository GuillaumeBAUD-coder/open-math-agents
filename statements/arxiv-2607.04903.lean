import Mathlib

namespace OMA.S_arxiv_2607_04903

/-- For finitely many circle-valued completely multiplicative functions,
a single positive Pythagorean triple takes all their values in any
prescribed open neighborhood of one. -/
theorem main :
    ∀ (d : ℕ) (f : Fin d → ℕ+ →* Circle) (U : Set Circle),
      0 < d → IsOpen U → 1 ∈ U →
      ∃ x y z : ℕ+,
        (x : ℕ) ^ 2 + (y : ℕ) ^ 2 = (z : ℕ) ^ 2 ∧
        ∀ i, f i x ∈ U ∧ f i y ∈ U ∧ f i z ∈ U := by
  sorry

end OMA.S_arxiv_2607_04903
