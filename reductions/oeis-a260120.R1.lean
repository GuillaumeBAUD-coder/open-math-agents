import OMAStatements.S_oeis_a260120

-- Reduction oeis-a260120.R1 of oeis-a260120: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a260120_R1

open OMA.S_oeis_a260120

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ k j : ℕ, 0 < k ∧ 0 < j ∧
        (Nat.nth Nat.Prime (k * n - 1) - 1) ^ 2 = Nat.nth Nat.Prime (j * n - 1) - 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ a b c m : ℤ, 0 < a → Int.gcd (Int.gcd a b) (c - m) = 1 →
        c % 2 = ((a + b + 1) * (m + 1)) % 2 → ¬ IsSquare (b ^ 2 - 4 * a * (c - m)) →
        ¬ (3 : ℤ) ∣ (Int.gcd (a * m - b) (b ^ 2 + b - a * c - 1) : ℤ) →
        ∀ n : ℕ, 1 ≤ n → ∃ x ∈ S m n, ∃ y ∈ S m n, a * x ^ 2 + b * x + c = y

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a260120.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a260120_R1
