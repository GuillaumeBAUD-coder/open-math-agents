import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R2.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R2
-- Credit: @LAPRAI
-- Averaging over the 2N - 1 shifts j: the points x ∈ U with x + N - j ∈ A number |U| |A| in
-- total, so one shift covers at least |U| |A| / (2N) of them; V is the rest of U.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2 := by
  classical
  intro N hN A U hA hU
  set J := Finset.Icc 1 (2 * N - 1) with hJ
  set W : ℕ → Finset ℕ := fun j => U.filter (fun x => ∃ y ∈ A, x + N = y + j) with hW
  have hfib : ∀ x ∈ U, (J.filter (fun j => ∃ y ∈ A, x + N = y + j)).card = A.card := by
    intro x hx
    have hx' := Finset.mem_Icc.mp (hU hx)
    have e : J.filter (fun j => ∃ y ∈ A, x + N = y + j) = A.image (fun y => x + N - y) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_image, hJ, Finset.mem_Icc]
      constructor
      · rintro ⟨_, y, hy, hyj⟩
        exact ⟨y, hy, by omega⟩
      · rintro ⟨y, hy, rfl⟩
        have hy' := Finset.mem_Icc.mp (hA hy)
        exact ⟨⟨by omega, by omega⟩, y, hy, by omega⟩
    rw [e, Finset.card_image_of_injOn]
    intro y hy z hz hyz
    have hy' := Finset.mem_Icc.mp (hA (Finset.mem_coe.mp hy))
    have hz' := Finset.mem_Icc.mp (hA (Finset.mem_coe.mp hz))
    have h' : x + N - y = x + N - z := hyz
    omega
  have hsumW : ∑ j ∈ J, (W j).card = U.card * A.card := by
    simp only [hW, Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun x hx => (Finset.card_filter _ _).symm.trans (hfib x hx)]
    simp [mul_comm]
  have hJne : J.Nonempty := ⟨1, by rw [hJ, Finset.mem_Icc]; omega⟩
  have hJcard : (J.card : ℝ) ≤ 2 * N := by
    rw [hJ, Nat.card_Icc]
    have : 2 * N - 1 + 1 - 1 ≤ 2 * N := by omega
    exact_mod_cast this
  have hN0 : (2 * (N : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  obtain ⟨j, -, hjW⟩ : ∃ j ∈ J, (U.card : ℝ) * A.card / (2 * N) ≤ (W j).card := by
    refine Finset.exists_le_of_sum_le (f := fun _ => (U.card : ℝ) * A.card / (2 * N))
      (g := fun j => ((W j).card : ℝ)) hJne ?_
    show ∑ _i ∈ J, (U.card : ℝ) * A.card / (2 * N) ≤ ∑ j ∈ J, ((W j).card : ℝ)
    rw [Finset.sum_const, nsmul_eq_mul, ← Nat.cast_sum, hsumW]
    push_cast
    calc (J.card : ℝ) * (U.card * A.card / (2 * N))
        ≤ (2 * N) * (U.card * A.card / (2 * N)) := by gcongr
      _ = U.card * A.card := by field_simp
  have hWU : W j ⊆ U := Finset.filter_subset _ _
  refine ⟨N, j, U \ W j, Finset.sdiff_subset, ?_, ?_⟩
  · have h := Finset.card_sdiff_add_card_eq_card hWU
    have hR : ((U \ W j).card : ℝ) + (W j).card = U.card := by exact_mod_cast h
    have e : (1 - (A.card : ℝ) / (2 * N)) * U.card = U.card - U.card * A.card / (2 * N) := by
      ring
    rw [e]
    linarith
  · intro x hx hxV
    have hxW : x ∈ W j := by
      by_contra h
      exact hxV (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    exact (Finset.mem_filter.mp hxW).2

