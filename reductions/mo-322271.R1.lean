import OMAStatements.S_mo_322271

-- Reduction mo-322271.R1 of mo-322271: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_mo_322271_R1

open OMA.S_mo_322271

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 14617 < n → (n % 4 = 1 ∨ n % 4 = 2) →
      Rep n (fun x₁ _ _ => x₁ % 2 = n % 2))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 15618 < n → (n % 4 = 1 ∨ n % 4 = 2) →
      Rep n (fun _ x₂ _ => x₂ % 2 = n % 2))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 25582 < n → (n % 4 = 1 ∨ n % 4 = 2) →
      Rep n (fun _ _ x₃ => x₃ % 2 = n % 2))

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_322271.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_mo_322271_R1
