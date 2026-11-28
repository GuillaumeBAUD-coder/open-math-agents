import OMAStatements.S_oeis_a248007

-- Reduction oeis-a248007.R1 of oeis-a248007: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a248007_R1

open OMA.S_oeis_a248007

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ Nat.totient m * Nat.totient n)

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | 6 < n ∧ ∀ m : ℕ, 0 < m → m ≤ n → ¬ m + n ∣ Nat.totient m * Nat.totient n}.Finite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a248007.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a248007_R1
