import Mathlib

namespace OMA.S_arxiv_2604_28116

open Filter
open scoped Topology ContDiff

/-- The probability that a uniform permutation fixes some k-element set setwise. -/
noncomputable def fixedSetProbability (n k : ℕ) : ℝ := by
  classical
  let perms := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ =>
    ∃ A : Finset (Fin n), A.card = k ∧ A.image σ = A
  exact (perms.card : ℝ) / (n.factorial : ℝ)

/-- The exponent in the Erdős–Ford–Tenenbaum asymptotic. -/
noncomputable def δ : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- Green and Sawhney conjecture that the smooth periodic coefficient in their
asymptotic for the limiting fixed-set probability is nonconstant. -/
theorem main :
    ∃ (p : ℕ → ℝ) (f : ℝ → ℝ),
      (∀ k, Tendsto (fun n => fixedSetProbability n k) atTop (𝓝 (p k))) ∧
      ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ (∀ x, 0 < f x) ∧
      Tendsto (fun k : ℕ =>
        p k * (k : ℝ) ^ δ * Real.log (k : ℝ) ^ (3 / 2 : ℝ) /
          f (Real.log (k : ℝ) / Real.log 2)) atTop (𝓝 1) ∧
      ∃ x y, f x ≠ f y := by
  sorry

end OMA.S_arxiv_2604_28116
