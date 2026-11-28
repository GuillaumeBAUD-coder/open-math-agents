import Mathlib

namespace OMA.S_opg_covering_designs

open Filter
open scoped Topology

/-- A family of k-subsets covering all t-subsets of a v-element ground set. -/
def IsCovering (v k t : ℕ) (blocks : Finset (Finset (Fin v))) : Prop :=
  (∀ B ∈ blocks, B.card = k) ∧
    ∀ T : Finset (Fin v), T.card = t → ∃ B ∈ blocks, T ⊆ B

noncomputable def coveringNumber (v k t : ℕ) : ℕ :=
  sInf {size : ℕ | ∃ blocks : Finset (Finset (Fin v)),
    blocks.card = size ∧ IsCovering v k t blocks}

noncomputable def coveringDensity (v k t : ℕ) : ℝ :=
  (coveringNumber v k t : ℝ) * (k.choose t : ℝ) / (v.choose t : ℝ)

/-- The minimum covering density tends to one. For 1 ≤ t < k, the
Gordon–Kuperberg–Patashnik–Spencer bound also controls its excess over one. -/
theorem main :
    (∀ k t : ℕ, 1 ≤ t → t ≤ k →
      Tendsto (fun v : ℕ => coveringDensity v k t) atTop (𝓝 1)) ∧
    (∀ k t : ℕ, 1 ≤ t → t < k →
      ∃ (C : ℝ) (N : ℕ), 0 < C ∧ max k 2 ≤ N ∧
        ∀ v : ℕ, N ≤ v →
          coveringDensity v k t ≤
            1 + C * Real.rpow (Real.log (v : ℝ)) (-(1 / ((k.choose t : ℝ) - 1)))) := by
  sorry

end OMA.S_opg_covering_designs
