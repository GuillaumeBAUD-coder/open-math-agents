import FormalConjectures.GreensOpenProblems.«40»

/-! Reduction to divergence along even radii and a one-step density bound. -/

namespace OMA.R_Green40_green_40_variants_arbitrary_subsets_R1

open Filter Topology
open scoped ENNReal

def H1 : Prop :=
  Tendsto (fun j : ℕ => Green40.f_tilde (2 * j)) atTop (𝓝 ⊤)

def H2 : Prop :=
  ∀ r : ℕ, 0 < r → Green40.f_tilde (r + 1) ≤ 6 * Green40.f_tilde r

theorem main : H1 → H2 → type_of% @Green40.green_40.variants.arbitrary_subsets := by
  intro hEven hStep
  change Tendsto (fun j : ℕ => Green40.f_tilde (2 * j)) atTop (𝓝 ⊤) at hEven
  change ∀ r : ℕ, 0 < r → Green40.f_tilde (r + 1) ≤ 6 * Green40.f_tilde r at hStep
  refine ENNReal.tendsto_nhds_top_iff_nat.mpr fun bound => ?_
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp
    (ENNReal.tendsto_nhds_top_iff_nat.mp hEven (6 * bound))
  refine eventually_atTop.mpr ⟨2 * threshold + 1, fun r hr => ?_⟩
  have cast_mul : (↑(6 * bound) : ℝ≥0∞) = 6 * (bound : ℝ≥0∞) := by
    simp
  by_cases parity : r = 2 * (r / 2)
  · have hlarge := hthreshold (r / 2) (by omega)
    rw [← parity] at hlarge
    exact lt_of_le_of_lt (by exact_mod_cast (show bound ≤ 6 * bound by omega)) hlarge
  · have next_even : r + 1 = 2 * (r / 2 + 1) := by omega
    have hlarge := hthreshold (r / 2 + 1) (by omega)
    rw [← next_even, cast_mul] at hlarge
    exact (ENNReal.mul_lt_mul_iff_right (by simp) (by simp)).mp
      (lt_of_lt_of_le hlarge (hStep r (by omega)))

end OMA.R_Green40_green_40_variants_arbitrary_subsets_R1
