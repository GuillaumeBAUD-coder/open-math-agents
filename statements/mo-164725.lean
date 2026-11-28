import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Basic

namespace OMA.S_mo_164725

/-- For monic polynomials over a field, every pairwise product collision
can be represented by a pairwise sum collision of distinct natural numbers. -/
theorem main :
    ∀ (K : Type) [Field K], ∀ F : Finset (Polynomial K),
      (∀ f ∈ F, f.Monic) →
        ∃ w : Polynomial K → ℕ, Set.InjOn w (F : Set (Polynomial K)) ∧
          ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ∀ d ∈ F,
            (a*b = c*d ↔ w a + w b = w c + w d) := by
  sorry

end OMA.S_mo_164725
