import OMAStatements.S_oeis_a065806

-- Reduction oeis-a065806.R1 of oeis-a065806: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a065806_R1

open OMA.S_oeis_a065806
open Filter Topology

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → -1 < a n ∧ a n < n + 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → a n = n + 1 → a (n + 1) = 0)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ m : ℤ, 1 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m)

/-- Step H4 of the reduction. -/
def H4 : Prop := (∀ c : ℝ, c ∈ Set.Icc 0 1 → ∃ i : ℕ → ℕ, StrictMono i ∧ (∀ j, 1 ≤ i j) ∧
      Tendsto (fun j => ((a (i j) : ℝ) + 1) / ((i j : ℝ) + 3)) atTop (𝓝 c))

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a065806.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a065806_R1
