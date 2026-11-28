import Mathlib

/-!
# The limit conjecture for the factorial triangle A140356

Source: https://oeis.org/A140356
Credit: @etaubman

The conjecture is read literally, with subtraction of the factorial entry.
-/

namespace OMA.S_oeis_a140356

open Filter Topology

def triangle (n m : ℕ) : ℕ :=
  if m ≤ n / 2 then m.factorial else (n - m).factorial

noncomputable def summand (n m : ℕ) : ℝ :=
  1 / (n.choose m : ℝ) - (triangle n m : ℝ)

noncomputable def rowSum (n : ℕ) : ℝ := ∑ m ∈ Finset.range (n + 1), summand n m

def conjecture : Prop := Tendsto rowSum atTop (𝓝 0)

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a140356
