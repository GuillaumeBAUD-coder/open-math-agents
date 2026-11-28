import OMAStatements.S_oeis_a071558

-- Reduction oeis-a071558.R1 of A071558: splits the target into the existence of a
-- twin-prime pair (n*k-1, n*k+1) and the bound a(n) < sqrt(n)*log(n), both for n > 17261.
-- Credit: @kernl

namespace OMA.R_oeis_a071558_R1

open OMA.S_oeis_a071558

/-- Existence: for every n > 17261 there is k >= 1 with n*k-1 and n*k+1 both prime. -/
def H1 : Prop := ∀ n : ℕ, 17261 < n →
  ∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (n * k - 1) ∧ Nat.Prime (n * k + 1)

/-- Bound: a(n) < sqrt(n) * log(n) for every n > 17261. -/
def H2 : Prop := ∀ n : ℕ, 17261 < n →
  (a n : ℝ) < Real.sqrt (n : ℝ) * Real.log (n : ℝ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a071558.main := by
  intro h1 h2 n hn
  exact ⟨h1 n hn, h2 n hn⟩

end OMA.R_oeis_a071558_R1
