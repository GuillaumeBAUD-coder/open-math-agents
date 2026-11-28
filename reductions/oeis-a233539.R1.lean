import OMAStatements.S_oeis_a233539

-- Reduction oeis-a233539.R1 of oeis-a233539: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a233539_R1

open OMA.S_oeis_a233539

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 794 < n → ∃ k : ℕ, 0 < k ∧ k + 2 < n ∧
      let m := Nat.totient k + Nat.totient (n - k) / 2
      (m - 1).Prime ∧ (m + 1).Prime ∧ (prime m - m).Prime ∧ (prime m + m).Prime)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 59 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ 4 ∣ Nat.totient (n - k) ∧
      let m := Nat.totient k + Nat.totient (n - k) / 4
      (prime m - m).Prime ∧ (prime m + m).Prime)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a233539.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a233539_R1
