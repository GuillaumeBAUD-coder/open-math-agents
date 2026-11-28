import OMAStatements.S_oeis_a229166

-- Reduction oeis-a229166.R1 of oeis-a229166: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a229166_R1

open OMA.S_oeis_a229166

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n →
      ∃ x y : ℕ, x * (x + 1) / 2 + y = n ∧ Nat.Prime (y * (y + 1) / 2 + 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n → n ∉ ({1, 3, 60} : Finset ℕ) →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x * (x + 1) / 2 + y = n ∧
        Nat.Prime (y * (y + 1) / 2 + 1))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a229166.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a229166_R1
