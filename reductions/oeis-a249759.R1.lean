import OMAStatements.S_oeis_a249759

-- Reduction oeis-a249759.R1 of oeis-a249759: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a249759_R1

open OMA.S_oeis_a249759

/-- Step H1 of the reduction. -/
def H1 : Prop := S.Finite

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ p ∈ S, IsFermatPrime p)

/-- Step H3 of the reduction. -/
def H3 : Prop := S = {p | IsFermatPrime p ∧ IsMersennePrime (ArithmeticFunction.sigma 1 (p - 1))}

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ n : ℕ, Nat.nth (· ∈ A249761) n = 2 * Nat.nth (· ∈ S) n - 3) ∧ (∀ n : ℕ, (n.Prime ∧ (ArithmeticFunction.sigma 1 (n + 1)).Prime) ↔ n = 3) ∧ (∀ p ∈ S, ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 (p - 1)) = 2 * (p - 1)) ∧ (∀ p ∈ S, Odd p ∧ (Nat.divisors (p - 1)).card.Prime) ∧ S = {p | p.Prime ∧ (Nat.divisors (p - 1)).card.Prime} )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a249759.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a249759_R1
