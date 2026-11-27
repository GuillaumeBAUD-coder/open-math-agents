import FormalConjectures.ErdosProblems.«994»

-- Credit: @steveDOTdigital
namespace OMA.R_Erdos994_erdos_994_R1

open Filter MeasureTheory Set Erdos994
open scoped ENNReal

-- The finite maximal estimate: a small target has a large visit average
-- somewhere in a finite window for a set of parameters of measure at least 1/2.
def H1 : Prop :=
  ∀ j : ℕ, ∃ E B : Set ℝ, ∃ M : ℕ,
    E ⊆ Ioo 0 1 ∧ MeasurableSet E ∧
    volume E ≤ (8 : ℝ≥0∞)⁻¹ * (2⁻¹ : ℝ≥0∞)^j ∧
    B ⊆ Ioo 0 1 ∧ MeasurableSet B ∧ (2 : ℝ≥0∞)⁻¹ ≤ volume B ∧
    ∀ α ∈ B, ∃ n ∈ Finset.Icc j M, (1/2 : ℝ) ≤ visitAverage E α n

-- In a finite interval, sets of uniformly positive measure cannot
-- disappear pointwise almost everywhere.
def H2 : Prop :=
  ∀ B : ℕ → Set ℝ, (∀ j, B j ⊆ Ioo 0 1) → (∀ j, MeasurableSet (B j)) →
    (∀ j, (2 : ℝ≥0∞)⁻¹ ≤ volume (B j)) →
    ¬ ∀ᵐ α : ℝ, ∀ᶠ j in atTop, α ∉ B j

theorem main : H1 → H2 → type_of% @Erdos994.erdos_994 := by
  classical
  intro blocks recurrent universal
  choose E B M hsub hmeas hsmall hBsub hBmeas hBmass hvisit using blocks
  let U := ⋃ j, E j
  have small : volume U ≤ (8 : ℝ≥0∞)⁻¹ * 2 := calc
    volume U ≤ ∑' j, volume (E j) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum hsmall
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
  have gap : (volume U).toReal < 1/2 := by
    have hp := ENNReal.toReal_mono (by finiteness : (8 : ℝ≥0∞)⁻¹ * 2 ≠ ⊤) small
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv] at hp
    linarith
  have conv := universal U (iUnion_subset hsub) (MeasurableSet.iUnion hmeas)
  apply recurrent B hBsub hBmeas hBmass
  filter_upwards [conv] with α hα
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hα.eventually_lt_const gap)
  filter_upwards [eventually_ge_atTop J] with j hj
  intro hmem
  obtain ⟨n, hn, hit⟩ := hvisit j α hmem
  have mono : visitAverage (E j) α n ≤ visitAverage U α n := by
    unfold visitAverage
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply Finset.sum_le_sum
    intro k _
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact (h₂ (mem_iUnion.2 ⟨j, h₁⟩)).elim
    · norm_num
    · rfl
  exact (hJ n (hj.trans (Finset.mem_Icc.1 hn).1)).not_ge (hit.trans mono)

end OMA.R_Erdos994_erdos_994_R1
