import FormalConjectures.GreensOpenProblems.«87»

/-! # Conditioning on the cycle containing a distinguished point -/
-- Credit: @steveDOTdigital
namespace OMA.R_Green87_green_87_variants_exists_tendsto_R1
open Finset Filter
open scoped Topology

-- Cycles longer than k leave the event entirely on the remaining points.
-- Only the at most k short cycle lengths can change the count.
def H1 : Prop := ∀ k n : ℕ,
    |(n : ℝ) * Green87.i n k - ∑ j ∈ range n, Green87.i j k| ≤ k

-- Consecutive running means then differ by a summable O(1/n²) error.
def H2 : Prop := ∀ (a : ℕ → ℝ) (C : ℝ), 0 ≤ C →
    (∀ n : ℕ, |(n : ℝ) * a n - ∑ j ∈ range n, a j| ≤ C) →
    ∃ L : ℝ, Tendsto a atTop (𝓝 L)

theorem main : H1 → H2 → type_of% @Green87.green_87.variants.exists_tendsto := by
  intro condition convergence k
  exact convergence (fun n => Green87.i n k) k (Nat.cast_nonneg _) (condition k)

end OMA.R_Green87_green_87_variants_exists_tendsto_R1
