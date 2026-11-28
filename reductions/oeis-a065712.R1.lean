import OMAStatements.S_oeis_a065712

-- Reduction oeis-a065712.R1 of oeis-a065712: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a065712_R1

open OMA.S_oeis_a065712

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ x : ℕ, {n : ℕ | a n = x}.Finite)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ x : ℕ, x < N.length → Nat.card {n : ℕ | a n = x} = N.getD x 0)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ x : ℕ, x < I.length → a (I.getD x 0) = x ∧ ∀ n : ℕ, a n = x → n ≤ I.getD x 0)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a065712.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a065712_R1
