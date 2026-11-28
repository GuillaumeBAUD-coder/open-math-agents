import OMAStatements.S_oeis_a258139

-- Reduction oeis-a258139.R1 of oeis-a258139: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a258139_R1

open OMA.S_oeis_a258139

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ r p q : ℕ, r ≤ 5 ∧ p.Prime ∧ q.Prime ∧ p ^ 2 + q = n + r)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ^ 2 + q = 6 * k + 2) ↔
        k ∉ ({0, 1, 12, 28, 102, 117, 168, 4079} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a258139.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a258139_R1
