import OMAStatements.S_oeis_a161721

-- Reduction oeis-a161721.R1 of oeis-a161721: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a161721_R1

open OMA.S_oeis_a161721

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → (digitalReverse p).Prime →
    (Nat.digits 10 (p * digitalReverse p)).Palindrome → (p ≠ 3 → ∀ d ∈ Nat.digits 10 p, d ≤ 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → (digitalReverse p).Prime →
    (Nat.digits 10 (p * digitalReverse p)).Palindrome → (Nat.digits 10 p).count 2 ≤ 1

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a161721.main := by
  intro h1 h2 x1 x2 x3 x4
  exact ⟨h1 x1 x2 x3 x4, h2 x1 x2 x3 x4⟩

end OMA.R_oeis_a161721_R1
