import OMAStatements.S_oeis_a248590

-- Reduction oeis-a248590.R1 of oeis-a248590: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a248590_R1

open OMA.S_oeis_a248590

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ prime m ≡ 1 [MOD m + n])

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3 < n → ∃ m : ℕ, 0 < m ∧ m < n * (n - 1) ∧ prime m ≡ 1 [MOD m + n])

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime m + 1)

/-- Step H4 of the reduction. -/
def H4 : Prop := ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m < n * (n - 1) ∧ m + n ∣ prime m + 1

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a248590.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a248590_R1
