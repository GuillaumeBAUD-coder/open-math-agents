import FormalConjectures.GreensOpenProblems.«40»

-- Credit: @steveDOTdigital
namespace OMA.R_Green40_green_40_upper_bound_f_two_R1

open Green40 Filter
open scoped ENNReal

-- Davydov, Marcugini and Pambianco, arXiv:2511.02542, radius two and r ≥ 28.
-- Shorter codes can be padded by unrestricted coordinates, preserving codimension.
def H1 : Prop :=
  ∀ k : ℕ, 10 ≤ k →
    let n := 26 * 2 ^ k - 1
    ∃ V : Submodule (ZMod 2) (𝔽₂ n), IsCoveringSubspace n 2 V ∧
      Nat.card V = 2 ^ (n - 2 * (k + 4))

-- Independent numerical step: use the radius-two ball size 1 + n + n.choose 2.
-- Along these lengths the density tends to 676 / 512, below the required bound.
def H2 : Prop :=
  ∀ b : ℕ, ∃ k : ℕ, 10 ≤ k ∧
    let n := 26 * 2 ^ k - 1
    b ≤ n ∧
      ((2 ^ (n - 2 * (k + 4)) : ℕ) : ℝ≥0∞) * (Nat.card (hammingBall n 2) : ℝ≥0∞) /
        (2 ^ n : ℝ≥0∞) ≤ 1.4238

theorem main : H1 → H2 → type_of% @Green40.green_40.upper_bound_f_two := by
  intro hcodes harith
  unfold Green40.f
  apply Filter.liminf_le_of_frequently_le'
  apply Filter.frequently_atTop.2
  intro b
  obtain ⟨k, hk, hbn, hbound⟩ := harith b
  obtain ⟨V, hcover, hcard⟩ := hcodes k hk
  refine ⟨26 * 2 ^ k - 1, hbn, ?_⟩
  unfold Green40.minDensity
  refine le_trans (iInf₂_le V hcover) ?_
  rwa [hcard]

end OMA.R_Green40_green_40_upper_bound_f_two_R1
