import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

namespace OMA.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1

open Arxiv.«2607.27197»
open scoped Gradient

/-- The limiting quartic has at least 21 distinct nondegenerate critical points. -/
def H1 : Prop :=
  ∃ s : Finset (EuclideanSpace ℝ (Fin 3)), s.card = 21 ∧
    ∀ x ∈ s, ∇ phiZero x = 0 ∧ HasNondegenerateHessianAt phiZero x

/-- Each finite collection of nondegenerate critical points of the rescaled limit
persists inside any fixed ball about the origin in the original coordinates. -/
def H2 : Prop :=
  ∀ (s : Finset (EuclideanSpace ℝ (Fin 3))),
    (∀ x ∈ s, ∇ phiZero x = 0 ∧ HasNondegenerateHessianAt phiZero x) →
    ∀ r > (0 : ℝ), ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ,
      (s.card : ℕ∞) ≤ ((nondegenerateEquilibria (counterexampleCharges ε)
        (counterexamplePositions ε)) ∩ Metric.ball 0 r).encard

/-- The three edge equilibria persist a uniformly positive distance from the origin. -/
def H3 : Prop :=
  ∃ r > (0 : ℝ), ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ,
    3 ≤ ((nondegenerateEquilibria (counterexampleCharges ε)
      (counterexamplePositions ε)) \ Metric.ball 0 r).encard

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2607.27197».maxwell_conjecture.counterexample := by
  rintro ⟨s, hcard, hs⟩ hpersist ⟨r, hr, d, hd, hedge⟩
  obtain ⟨c, hc, hcenter⟩ := hpersist s hs r hr
  refine ⟨min c d, lt_min hc hd, ?_⟩
  intro ε hε
  have inside := hcenter ε ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_left c d)⟩
  have outside := hedge ε ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_right c d)⟩
  rw [hcard] at inside
  rw [← Set.encard_sdiff_add_encard_inter _ (Metric.ball 0 r)]
  exact add_le_add outside inside

end OMA.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1
