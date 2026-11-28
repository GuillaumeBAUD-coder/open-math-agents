import OMAStatements.S_oeis_a093811

-- Reduction oeis-a093811.R1 of oeis-a093811: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a093811_R1

open OMA.S_oeis_a093811

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 798 < n → digitProductSum n < n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ k : ℕ, 1 ≤ k → recordAt (10 ^ k - 4))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ k : ℕ, 4 < k → recordAt (10 ^ k - 2))

/-- Step H4 of the reduction. -/
def H4 : Prop := ( Filter.Tendsto (fun k : ℕ => (digitProductSum (10 ^ k - 4) : ℝ) / (9 : ℝ) ^ k)
      Filter.atTop (nhds (94 / 81 : ℝ)) ∧ Filter.Tendsto (fun k : ℕ => (digitProductSum (10 ^ k - 2) : ℝ) / (9 : ℝ) ^ k)
      Filter.atTop (nhds (4 / 3 : ℝ)) ∧ Filter.Tendsto (fun n : ℕ => (digitProductSum n : ℝ) / n)
      Filter.atTop (nhds 0) ∧ Filter.limsup (fun n : ℕ => (digitProductSum n : ℝ) / (9 : ℝ) ^ (Real.logb 10 n))
      Filter.atTop = (4 / 3 : ℝ) )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a093811.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a093811_R1
