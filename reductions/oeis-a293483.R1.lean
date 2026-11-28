import OMAStatements.S_oeis_a293483

-- Reduction oeis-a293483.R1 of oeis-a293483: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a293483_R1

open OMA.S_oeis_a293483

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ e : ℕ, e ≤ 3 → a293483 (2 ^ e) = 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ e : ℕ, 3 ≤ e → a293483 (2 ^ e) = 2 ^ (e - 3))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ e : ℕ, e ≤ 2 → a293483 (3 ^ e) = 1)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ e : ℕ, 2 ≤ e → a293483 (3 ^ e) = 3 ^ (e - 2)) ∧ (∀ p e : ℕ, p.Prime → 1 ≤ e → p % 6 = 5 →
      a293483 (p ^ e) = (p - 1) * p ^ (e - 1) / 2) ∧ (∀ p e : ℕ, p.Prime → 1 ≤ e → p % 6 = 1 →
      a293483 (p ^ e) = (p - 1) * p ^ (e - 1) / 6) )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a293483.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a293483_R1
