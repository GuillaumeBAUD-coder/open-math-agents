import OMAStatements.S_oeis_a326925

-- Reduction oeis-a326925.R1 of oeis-a326925: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a326925_R1

open OMA.S_oeis_a326925
open Polynomial

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, Odd (row n).natDegree → Irreducible (row n))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n k : ℕ, 0 < k → (row n).natDegree = 2*k →
      ∃ p q : ℚ[X], row n = p*q ∧ Irreducible p ∧ Irreducible q ∧
        p.natDegree = k ∧ q.natDegree = k)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a326925.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a326925_R1
