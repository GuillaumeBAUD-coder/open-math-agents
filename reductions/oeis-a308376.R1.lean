import OMAStatements.S_oeis_a308376

-- Reduction oeis-a308376.R1 of oeis-a308376: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a308376_R1

open OMA.S_oeis_a308376

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ p : ℕ, p.Prime → p ∉ ({2, 5, 7, 11, 43, 79} : Finset ℕ) →
      ∃ k m : ℕ, 1 ≤ k ∧ k ≤ p - 1 ∧ 1 ≤ m ∧ m ≤ p - 1 ∧ k * m ≡ 1 [MOD p] ∧
        IsSquare (k + m))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ p : ℕ, p.Prime → 18 < p →
      ∃ k m : ℕ, 1 ≤ k ∧ k ≤ p - 1 ∧ 1 ≤ m ∧ m ≤ p - 1 ∧ k * m ≡ 1 [MOD p] ∧
        ∃ t : ℕ, k + m = t * (t + 1) / 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a308376.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a308376_R1
