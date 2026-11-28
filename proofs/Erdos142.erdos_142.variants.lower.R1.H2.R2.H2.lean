import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

-- Credit: @midnitefox. Shortens the proof in #37537.
-- Credits: @596050 (#37537), @0xa2d (#38387), @npnelson (#36899), @weizj99 (#32350), @Salofe (#5279).
-- Their shift-count and logarithm arguments are retained.
open Finset Real in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  have hs : S.card ≤ N := by simpa using card_le_card hS
  have hlt : N * (2 * N - S.card) ^ q < (2 * N) ^ q := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hsr : (S.card : ℝ) ≤ N := by exact_mod_cast hs
    have hm : (0 : ℝ) < 2 * N := by positivity
    have hd : (0 : ℝ) < 2 * N - S.card := by linarith
    rw [← Nat.cast_lt (α := ℝ)]
    push_cast [Nat.cast_sub (by omega : S.card ≤ 2*N)]
    apply (log_lt_log_iff (by positivity) (by positivity)).mp
    rw [log_mul hNr.ne' (pow_pos hd q).ne', log_pow, log_pow]
    apply (mul_lt_mul_iff_right₀ hm).mp
    have hb := log_le_sub_one_of_pos (div_pos hd hm)
    rw [log_div hd.ne' hm.ne', le_sub_iff_add_le, le_div_iff₀ hm] at hb
    nlinarith [mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q)]
  let A x := range (2 * N) \ S.image (x + N - ·)
  let P (B : Finset ℕ) := Fintype.piFinset fun _ : Fin q => B
  have hU : ((Icc 1 N).biUnion (P ∘ A)).card < (P (range (2 * N))).card := calc
    _ ≤ (Icc 1 N).card * (2 * N - S.card) ^ q :=
      card_biUnion_le_card_mul _ _ _ fun x hx => by
        have := mem_Icc.mp hx
        have hsub : S.image (x + N - ·) ⊆ range (2 * N) :=
          image_subset_iff.mpr fun b hb => by
            have := mem_Icc.mp (hS hb)
            exact mem_range.mpr (by omega)
        have hcard : (S.image (x + N - ·)).card = S.card :=
          card_image_of_injOn fun b hb b' hb' e => by
            have := mem_Icc.mp (hS hb); have := mem_Icc.mp (hS hb'); omega
        simp [P, A, card_sdiff_of_subset hsub, hcard]
    _ < _ := by simpa [P] using hlt
  obtain ⟨f, hf, hfu⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨f, fun x hx => ?_⟩
  have B b (hb : b ∈ S) := mem_Icc.mp (hS hb)
  simp [P, A, Fintype.mem_piFinset, mem_image, not_forall] at hf hfu
  grind [mem_Icc]
