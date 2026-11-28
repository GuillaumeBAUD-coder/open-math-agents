import OMAStatements.S_mo_57550

-- Reduction mo-57550.R1 of mo-57550: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_57550_R1

open OMA.S_mo_57550
open Matrix

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ X : Finset (Vec d), unitNet δ X)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n × Fin 3) ℝ) (v : Fin n → Fin 3 → ℝ),
      ∃ R : Three, rotation R ∧ (∀ S, rotation S → objective A v S ≤ objective A v R) ∧
        (∃ x : Vec n, ∃ y : Vec m, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
          nuclear (coefficient A v x y) = objective A v R) ∧
        (∀ (x : Vec n) (y : Vec m), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          nuclear (coefficient A v x y) ≤ objective A v R ∧
          ∃ S, rotation S ∧ |(Sᵀ * coefficient A v x y).trace| = nuclear (coefficient A v x y) ∧
            nuclear (coefficient A v x y) ≤ objective A v S) ∧
        (∀ (δ : ℝ) (X : Finset (Vec n)) (Y : Finset (Vec m)), unitNet δ X → unitNet δ Y →
          ∃ x ∈ X, ∃ y ∈ Y, (1 - 2*δ) * objective A v R ≤ nuclear (coefficient A v x y))

theorem main : H1 → H2 → type_of% @OMA.S_mo_57550.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mo_57550_R1
