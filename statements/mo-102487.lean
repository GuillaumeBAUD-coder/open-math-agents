import Mathlib

namespace OMA.S_mo_102487

open Filter Topology

/-- The finite kernel formed by truncating a frame and its dual. The second family can
include complex conjugation. -/
noncomputable def kernel {G : Type*} {n : ℕ}
    (a b : Fin n → G → ℂ) (x y : G) : ℂ :=
  ∑ i, a i x * b i y

/-- Each function in the finite family belongs to discrete ℓ². -/
def SquareSummable {G : Type*} {n : ℕ} (a : Fin n → G → ℂ) : Prop :=
  ∀ i, Summable fun x => ‖a i x‖ ^ 2

/-- On an infinite discrete abelian group, a square-summable finite kernel is a
convolution kernel exactly when it vanishes. A one-term truncation on ℤ can be nonzero. -/
theorem main :
    (∀ {G : Type*} [AddCommGroup G] [Infinite G] {n : ℕ}
        (a b : Fin n → G → ℂ), SquareSummable a → SquareSummable b →
      ((∃ f : G → ℂ, ∀ x y, kernel a b x y = f (x - y)) ↔
        ∀ x y, kernel a b x y = 0)) ∧
    (∃ a : Fin 1 → ℤ → ℂ, SquareSummable a ∧
      ¬ ∃ f : ℤ → ℂ, ∀ x y, kernel a a x y = f (x - y)) := by
  sorry

end OMA.S_mo_102487
