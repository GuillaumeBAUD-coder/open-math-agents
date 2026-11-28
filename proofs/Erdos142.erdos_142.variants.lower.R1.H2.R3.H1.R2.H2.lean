import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R2.H2
-- Credit: @mijuny

namespace Pre37261H2

theorem prove_H2 :
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2 := by
  classical
  intro N hN A U hA hU
  let P := U ×ˢ A
  let D := Finset.range (2 * N)
  let diff (z : ℕ × ℕ) := z.1 + N - z.2
  let fiber (j : ℕ) := P.filter fun z => diff z = j
  have hxy {z : ℕ × ℕ} (hz : z ∈ P) :
      (1 ≤ z.1 ∧ z.1 ≤ N) ∧ 1 ≤ z.2 ∧ z.2 ≤ N :=
    ⟨Finset.mem_Icc.mp (hU (Finset.mem_product.mp hz).1),
     Finset.mem_Icc.mp (hA (Finset.mem_product.mp hz).2)⟩
  have hmap : (P : Set (ℕ × ℕ)).MapsTo diff D := by
    intro z hz
    have hh := hxy hz
    apply Finset.mem_range.mpr
    dsimp [diff]
    omega
  obtain ⟨j, _, hmax⟩ := D.exists_max_image (fun i => (fiber i).card)
    (show D.Nonempty from ⟨0, Finset.mem_range.mpr (by omega)⟩)
  have hmass : U.card * A.card ≤ (2 * N) * (fiber j).card := by
    calc U.card * A.card = P.card := (Finset.card_product U A).symm
      _ = ∑ i ∈ D, (fiber i).card := Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _i ∈ D, (fiber j).card := Finset.sum_le_sum hmax
      _ = _ := by simp [D]
  let E := (fiber j).image Prod.fst
  have heq {z : ℕ × ℕ} (hz : z ∈ fiber j) : z.1 + N = z.2 + j := by
    obtain ⟨hzP, hj'⟩ := Finset.mem_filter.mp hz
    have hh := hxy hzP
    change z.1 + N - z.2 = j at hj'
    omega
  have hcard : E.card = (fiber j).card := by
    apply Finset.card_image_of_injOn
    intro z hz w hw h
    apply Prod.ext h
    have h1 := heq hz
    have h2 := heq hw
    change z.1 = w.1 at h
    omega
  have hEU : E ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  refine ⟨N, j, U \ E, Finset.sdiff_subset, ?_, ?_⟩
  · have hNpos : 0 < (2 * (N : ℝ)) := by exact_mod_cast (show 0 < 2 * N by omega)
    have hm : (U.card : ℝ) * A.card ≤ (2 * (N : ℝ)) * E.card := by
      rw [hcard]; exact_mod_cast hmass
    have hfrac : (A.card : ℝ) / (2 * N) * U.card ≤ E.card := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
      nlinarith only [hm]
    rw [Finset.card_sdiff_of_subset hEU, Nat.cast_sub (Finset.card_mono hEU)]
    linarith
  · intro x hx hn
    have hxE : x ∈ E := by
      by_contra h
      exact hn (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hxE
    exact ⟨z.2, (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2, heq hz⟩

end Pre37261H2

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2 :=
  Pre37261H2.prove_H2
