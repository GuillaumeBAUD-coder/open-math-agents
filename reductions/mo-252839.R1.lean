import OMAStatements.S_mo_252839
import Mathlib

open MeasureTheory Set Metric OMA.S_mo_252839
open scoped ENNReal NNReal

namespace OMA.R_mo_252839_R1

/-- A doubling reference measure has uniformly small density on a compact set of positive
length. The periodic four-adic measure with weights (1,3,3,1)/8 gives such data. -/
def H1 : Prop :=
  ∃ (ν : Measure ℝ) (K : Set ℝ), IsCompact K ∧ 0 < volume K ∧ ν K = 0 ∧
    IsLocallyFiniteMeasure ν ∧
    (∀ x r : ℝ, 0 < r → 0 < ν (closedBall x r)) ∧
    (∃ D : ℝ≥0, ∀ x r : ℝ, 0 < r →
      ν (closedBall x (2*r)) ≤ (D : ℝ≥0∞) * ν (closedBall x r)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ r : ℝ, 0 < r → r < δ →
      ν (closedBall z r) ≤ ENNReal.ofReal (ε*r))

/-- Continuity and vanishing for the explicitly normalized triangular kernel with
radius dist(y,K)/32. Lean's zero division convention sets the kernel to zero on K. -/
def H2 : Prop :=
  ∀ (ν : Measure ℝ) (K : Set ℝ), IsCompact K → K.Nonempty →
    IsLocallyFiniteMeasure ν →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ r : ℝ, 0 < r → r < δ →
      ν (closedBall z r) ≤ ENNReal.ofReal (ε*r)) →
  let w (x : ℝ) : ℝ≥0 := (∫ y, (32 / infDist y K) *
    max 0 (1 - 32 * |x - y| / infDist y K) ∂ν).toNNReal
  Continuous w ∧ ∀ z ∈ K, w z = 0

/-- Two local estimates for the same explicit kernel. Near K they compare masses with the
reference measure. Far from K they compare the pointwise density with one constant on a ball. -/
def H3 : Prop :=
  ∀ (ν : Measure ℝ) (K : Set ℝ) (D : ℝ≥0), IsCompact K → K.Nonempty →
    IsLocallyFiniteMeasure ν → ν K = 0 →
    (∀ x r : ℝ, 0 < r →
      ν (closedBall x (2*r)) ≤ (D : ℝ≥0∞) * ν (closedBall x r)) →
  let w (x : ℝ) : ℝ≥0 := (∫ y, (32 / infDist y K) *
    max 0 (1 - 32 * |x - y| / infDist y K) ∂ν).toNNReal
  ∃ A : ℝ≥0,
    (∀ x r : ℝ, 0 < r → infDist x K ≤ 8*r →
      ν (closedBall x (r/2)) ≤ weightedVolume w (closedBall x r) ∧
      weightedVolume w (closedBall x (2*r)) ≤ ν (closedBall x (3*r))) ∧
    (∀ x r : ℝ, 0 < r → 8*r < infDist x K → ∃ m : ℝ≥0,
      (∀ y ∈ closedBall x r, m ≤ w y) ∧
      (∀ y ∈ closedBall x (2*r), w y ≤ A*m))

lemma weight_mass_upper {w : ℝ → ℝ≥0} {s : Set ℝ} {a : ℝ≥0}
    (hs : MeasurableSet s) (ha : ∀ y ∈ s, w y ≤ a) :
    weightedVolume w s ≤ (a : ℝ≥0∞) * volume s := by
  rw [weightedVolume, withDensity_apply _ hs, ← setLIntegral_const s (a : ℝ≥0∞)]
  exact setLIntegral_mono' hs fun y hy => ENNReal.coe_le_coe.mpr (ha y hy)

lemma weight_mass_lower {w : ℝ → ℝ≥0} {s : Set ℝ} {a : ℝ≥0}
    (hs : MeasurableSet s) (ha : ∀ y ∈ s, a ≤ w y) :
    (a : ℝ≥0∞) * volume s ≤ weightedVolume w s := by
  rw [weightedVolume, withDensity_apply _ hs, ← setLIntegral_const s (a : ℝ≥0∞)]
  exact setLIntegral_mono' hs fun y hy => ENNReal.coe_le_coe.mpr (ha y hy)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_252839.main := by
  intro href hcontinuous hestimates
  obtain ⟨ν, K, hK, hlen, hnull, hlocal, hpositive, ⟨D, hD⟩, hthin⟩ := href
  have hne : K.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn] at hlen
    simpa using hlen
  let w (x : ℝ) : ℝ≥0 := (∫ y, (32 / infDist y K) *
    max 0 (1 - 32 * |x - y| / infDist y K) ∂ν).toNNReal
  obtain ⟨hw, hzero⟩ := hcontinuous ν K hK hne hlocal hthin
  obtain ⟨A, hnear, hfar⟩ := hestimates ν K D hK hne hlocal hnull hD
  change Continuous w at hw
  change ∀ z ∈ K, w z = 0 at hzero
  refine ⟨w, hw, ?_, hlen.trans_le (measure_mono hzero)⟩
  have hnonzero : weightedVolume w ≠ 0 := by
    obtain ⟨z, hz⟩ := hne
    have hn := (hnear z 1 zero_lt_one (by rw [infDist_zero_of_mem hz]; norm_num)).1
    have hp := (hpositive z (1/2) (by norm_num)).trans_le hn
    intro he
    change 0 < weightedVolume w (closedBall z 1) at hp
    simpa [he] using hp
  refine ⟨hnonzero, IsLocallyFiniteMeasure.withDensity_coe hw, max (2*A) (D^3), ?_⟩
  intro x r hr
  simp only [← Real.closedBall_eq_Icc]
  by_cases hn : infDist x K ≤ 8*r
  · obtain ⟨hin, hout⟩ := hnear x r hr hn
    have hhalf := hD x (r/2) (by linarith)
    rw [show 2 * (r/2) = r by ring] at hhalf
    calc
      weightedVolume w (closedBall x (2*r)) ≤ ν (closedBall x (3*r)) := hout
      _ ≤ ν (closedBall x (2*(2*r))) :=
        measure_mono (closedBall_subset_closedBall (by linarith))
      _ ≤ (D : ℝ≥0∞) * ν (closedBall x (2*r)) := hD x (2*r) (by linarith)
      _ ≤ (D : ℝ≥0∞) * ((D : ℝ≥0∞) * ν (closedBall x r)) :=
        mul_le_mul_right (hD x r hr) _
      _ ≤ (D : ℝ≥0∞) * ((D : ℝ≥0∞) * ((D : ℝ≥0∞) * ν (closedBall x (r/2)))) :=
        mul_le_mul_right (mul_le_mul_right hhalf _) _
      _ = ((D^3 : ℝ≥0) : ℝ≥0∞) * ν (closedBall x (r/2)) := by
        rw [ENNReal.coe_pow]; ring
      _ ≤ ((D^3 : ℝ≥0) : ℝ≥0∞) * weightedVolume w (closedBall x r) :=
        mul_le_mul_right hin _
      _ ≤ _ := mul_le_mul_left (ENNReal.coe_le_coe.mpr (le_max_right (2*A) (D^3))) _
  · obtain ⟨m, hlo, hhi⟩ := hfar x r hr (lt_of_not_ge hn)
    have hvol : volume (closedBall x (2*r)) = 2 * volume (closedBall x r) := by
      simp only [Real.volume_closedBall]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc
      weightedVolume w (closedBall x (2*r)) ≤ ((A*m : ℝ≥0) : ℝ≥0∞) *
          volume (closedBall x (2*r)) := weight_mass_upper isClosed_closedBall.measurableSet hhi
      _ = ((2*A : ℝ≥0) : ℝ≥0∞) * ((m : ℝ≥0∞) * volume (closedBall x r)) := by
        rw [hvol]; simp only [ENNReal.coe_mul, ENNReal.coe_two]; ring
      _ ≤ ((2*A : ℝ≥0) : ℝ≥0∞) * weightedVolume w (closedBall x r) :=
        mul_le_mul_right (weight_mass_lower isClosed_closedBall.measurableSet hlo) _
      _ ≤ _ := mul_le_mul_left (ENNReal.coe_le_coe.mpr (le_max_left (2*A) (D^3))) _

end OMA.R_mo_252839_R1
