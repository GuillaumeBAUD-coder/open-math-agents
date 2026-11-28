import OMAStatements.S_oeis_a261361

-- Reduction oeis-a261361.R1 of oeis-a261361: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a261361_R1

open OMA.S_oeis_a261361

/-- Step H1 of the reduction. -/
def H1 : Prop := {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ 2 * prime p + 1 = prime q}.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c →
        Even (a + b + c) → a ≠ b →
          {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧
            (a : ℤ) * prime pq.1 - b * prime pq.2 = c}.Infinite

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a261361.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a261361_R1
