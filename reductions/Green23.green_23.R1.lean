import FormalConjectures.GreensOpenProblems.«23»

-- Frantzikinakis, Klurman and Moreira, Partition regularity of Pythagorean
-- pairs, Section 2.1 (arXiv:2309.10636v5).

namespace OMA.R_Green23_green_23_R1

open MeasureTheory

-- The multiplicative correspondence principle and spectral representation.
-- K is the overlap of two dilates of a color class of positive density.
-- Characters live in the coordinate space ℕ → ℂ, with the unused coordinate
-- at zero free to be set to one when constructing the spectral measure.
def H1 : Prop :=
  ∀ (k : ℕ) (c : ℕ → Fin k), ∃ σ : Measure (ℕ → ℂ),
    IsFiniteMeasure σ ∧ 0 < σ {fun _ => (1 : ℂ)} ∧
    (∀ᵐ f ∂σ, (∀ r : ℕ, 0 < r → ‖f r‖ = 1) ∧
      ∀ r s : ℕ, 0 < r → 0 < s → f (r * s) = f r * f s) ∧
    ∃ K : ℕ → ℕ → ℝ,
      (∀ r s : ℕ, 0 < r → 0 < s →
        (∫ f, f r * star (f s) ∂σ) = (K r s : ℂ) ∧ 0 ≤ K r s) ∧
      ∀ r s : ℕ, 0 < r → 0 < s → 0 < K r s →
        ∃ d : ℕ, 0 < d ∧ c (d * r) = c (d * s)

-- Theorem 2.2(i), specialized to coefficients 1 and 2. Only one positive
-- correlation is needed here, a consequence of the positive limiting average.
def H2 : Prop :=
  ∀ (σ : Measure (ℕ → ℂ)), IsFiniteMeasure σ → 0 < σ {fun _ => (1 : ℂ)} →
    (∀ᵐ f ∂σ, (∀ r : ℕ, 0 < r → ‖f r‖ = 1) ∧
      ∀ r s : ℕ, 0 < r → 0 < s → f (r * s) = f r * f s) →
    ∀ K : ℕ → ℕ → ℝ,
      (∀ r s : ℕ, 0 < r → 0 < s →
        (∫ f, f r * star (f s) ∂σ) = (K r s : ℂ) ∧ 0 ≤ K r s) →
      ∃ m n : ℕ, 0 < n ∧ n < m ∧ 0 < K (m ^ 2 - n ^ 2) (2 * m * n)

theorem main : H1 → H2 → type_of% @Green23.green_23 := by
  intro correspondence recurrence k c
  obtain ⟨σ, finite, atom, characters, K, correlation, hit⟩ := correspondence k c
  obtain ⟨m, n, hn, hnm, positive⟩ := recurrence σ finite atom characters K correlation
  have hsq : n ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hnm (by decide)
  have hleft : 0 < m ^ 2 - n ^ 2 := Nat.sub_pos_of_lt hsq
  have hm : 0 < m := hn.trans hnm
  have hright : 0 < 2 * m * n := by positivity
  obtain ⟨d, hd, color⟩ := hit _ _ hleft hright positive
  refine ⟨d * (m ^ 2 - n ^ 2), d * (2 * m * n),
    Nat.mul_pos hd hleft, Nat.mul_pos hd hright, color, d * (m ^ 2 + n ^ 2), ?_⟩
  zify [hsq.le]
  ring

end OMA.R_Green23_green_23_R1
