import FormalConjectures.Paper.DeGiorgi

-- Reduction DeGiorgi.DeGiorgi_eight.R1 of De Giorgi's conjecture — DeGiorgi eight
-- Credit: @ZenimXD
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The split follows the literature for 4 ≤ n ≤ 8:
-- * H1 is Savin's theorem (Annals of Math. 169 (2009), https://doi.org/10.4007/annals.2009.169.41)
--   in dimension 8: a bounded solution of Δu + u - u^3 = 0 with ∂₁u > 0 and u → ±1 as x₁ → ±∞
--   (for every fixed other coordinates) has hyperplanes as level sets. Known, not yet formalized.
-- * H2 is the open core: in dimension 8, every bounded solution with ∂₁u > 0 has these limits.
--   (Monotone bounded solutions always have limits u^± as x₁ → ±∞, which are stable solutions in
--   one dimension less; the open question is that they are the constants ±1.)

namespace OMA.R_DeGiorgi_DeGiorgi_eight_R1

open Filter Topology

/-- Savin's theorem in dimension 8: a bounded solution with positive first partial derivative that
tends to `1` and `-1` as the first coordinate tends to `+∞` and `-∞` has hyperplane level sets. -/
def H1 : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin 8) → ℝ, DeGiorgi.IsBoundedSolution u → DeGiorgi.HasPositiveDeriv u →
    (∀ x : EuclideanSpace ℝ (Fin 8),
      Tendsto (fun t : ℝ => u (x + t • EuclideanSpace.single 0 1)) atTop (𝓝 1) ∧
      Tendsto (fun t : ℝ => u (x + t • EuclideanSpace.single 0 1)) atBot (𝓝 (-1))) →
    DeGiorgi.HasHyperplaneLevelSets u

/-- In dimension 8, every bounded solution with positive first partial derivative tends to `1` and
`-1` as the first coordinate tends to `+∞` and `-∞`. -/
def H2 : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin 8) → ℝ, DeGiorgi.IsBoundedSolution u → DeGiorgi.HasPositiveDeriv u →
    ∀ x : EuclideanSpace ℝ (Fin 8),
      Tendsto (fun t : ℝ => u (x + t • EuclideanSpace.single 0 1)) atTop (𝓝 1) ∧
      Tendsto (fun t : ℝ => u (x + t • EuclideanSpace.single 0 1)) atBot (𝓝 (-1))

theorem main : H1 → H2 → type_of% @DeGiorgi.DeGiorgi_eight := by
  intro h1 h2
  unfold DeGiorgi.DeGiorgi_conclusion
  intro u hu
  exact h1 u hu.1 hu.2 (h2 u hu.1 hu.2)

end OMA.R_DeGiorgi_DeGiorgi_eight_R1
