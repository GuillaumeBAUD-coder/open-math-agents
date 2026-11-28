import Mathlib

/-!
# MathOverflow 202568

Source: https://mathoverflow.net/questions/202568
-/

namespace OMA.S_mo_202568

open Finset

noncomputable def entropy {A : Type} [Fintype A] (P : A → ℝ) : ℝ :=
  - ∑ a, P a * Real.log (P a)

noncomputable def relativeEntropy {A : Type} [Fintype A] (P Q : A → ℝ) : ℝ :=
  ∑ a, P a * (Real.log (P a) - Real.log (Q a))

theorem main : ∀ (A : Type) [Fintype A] (P Q : A → ℝ),
      (∀ a, 0 ≤ P a) → (∀ a, 0 < Q a) → (∑ a, P a) = 1 → (∑ a, Q a) = 1 →
        entropy Q ≤ entropy P + relativeEntropy P Q := by
  sorry

end OMA.S_mo_202568
