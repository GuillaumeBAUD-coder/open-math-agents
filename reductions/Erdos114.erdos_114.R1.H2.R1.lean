import OMAReductions.R_Erdos114_erdos_114_R1

-- Reduction Erdos114.erdos_114.R1.H2.R1 of step Erdos114.erdos_114.R1.H2
-- Credit: @kmcooke22
--
-- Split of H2 along the classical length formula for lemniscates
-- (Erdős–Herzog–Piranian; Pommerenke, *Boundary Behaviour of Conformal Maps*):
-- the length of {|q| = 1} is the integral over the unit circle of the sum of
-- 1/|q'| over the fiber. H1 is that formula (a Hausdorff-measure identity,
-- the formalization-heavy piece); H2 is the integrated comparison for model
-- polynomials, which is the analytic heart: the comparison is genuinely
-- integrated, since near a critical value of q the fiber sum blows up
-- integrably and no pointwise-in-θ bound can hold.

namespace OMA.R_Erdos114_erdos_114_R1_H2_R1

open Polynomial MeasureTheory
open scoped ENNReal

/-- The length formula: for monic `q` of degree `n ≥ 1`, the Hausdorff length
of the lemniscate `{|q| = 1}` equals the integral over `θ ∈ [0, 2π]` of the
sum of `1 / ‖q'(z)‖` over the roots `z` of `q - C(e^{iθ})` (the fiber sum,
taken over the root multiset; it agrees with the sum over distinct preimages
for almost every `θ`). -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ q : ℂ[X], q.Monic → q.natDegree = n →
    Erdos114.lemniscateLength q =
      ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
        ((q - C (Complex.exp (θ * Complex.I))).roots.map
          fun z => (ENNReal.ofReal ‖q.derivative.eval z‖)⁻¹).sum ∂volume

/-- The integrated comparison: for a model polynomial `q` (monic of degree
`n ≥ 1`, all critical values on the unit circle, at least two distinct
critical values), the fiber-sum integral of `q` is at most that of
`X ^ n - 1`. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ q : ℂ[X], q.Monic → q.natDegree = n →
    (∀ x : ℂ, q.derivative.IsRoot x → ‖q.eval x‖ = 1) →
    (∃ x y : ℂ, q.derivative.IsRoot x ∧ q.derivative.IsRoot y ∧ q.eval x ≠ q.eval y) →
    (∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
        ((q - C (Complex.exp (θ * Complex.I))).roots.map
          fun z => (ENNReal.ofReal ‖q.derivative.eval z‖)⁻¹).sum ∂volume)
    ≤ ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
        (((X ^ n - 1 : ℂ[X]) - C (Complex.exp (θ * Complex.I))).roots.map
          fun z => (ENNReal.ofReal ‖(X ^ n - 1 : ℂ[X]).derivative.eval z‖)⁻¹).sum ∂volume

theorem main : H1 → H2 → OMA.R_Erdos114_erdos_114_R1.H2 := by
  intro h1 h2 n hn q hqmonic hqdeg hcrit hdistinct
  have hmonic : (X ^ n - 1 : ℂ[X]).Monic := by
    rw [← Polynomial.C_1]
    exact Polynomial.monic_X_pow_sub_C 1 hn.ne'
  have hdeg : (X ^ n - 1 : ℂ[X]).natDegree = n := by
    rw [← Polynomial.C_1]
    exact Polynomial.natDegree_X_pow_sub_C
  rw [h1 n hn q hqmonic hqdeg, h1 n hn (X ^ n - 1) hmonic hdeg]
  exact h2 n hn q hqmonic hqdeg hcrit hdistinct

end OMA.R_Erdos114_erdos_114_R1_H2_R1
