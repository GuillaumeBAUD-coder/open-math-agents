import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-! Each target x+N has exactly |S| covering shifts: they form the reflected
copy x+N−S inside [0,2N). Count the tuples missing a point by taking a union
of Cartesian powers of these complements.
The reflected-shift argument is adapted from PR #36899. The logarithmic
count estimate uses log x ≤ x−1 directly. -/

open Finset

private theorem union_threshold (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2*(N:ℝ)*Real.log N < q*s) : N*(2*N-s)^q < (2*N)^q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hM : (0 : ℝ) < 2 * N := by positivity
  have hd : (0 : ℝ) < 2 * N - s := by linarith
  have hbound := Real.log_le_sub_one_of_pos (div_pos hd hM)
  rw [Real.log_div hd.ne' hM.ne', le_sub_iff_add_le, le_div_iff₀ hM] at hbound
  have hlt : (N : ℝ) * (2 * N - s) ^ q < (2 * N) ^ q := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul hNr.ne' (pow_pos hd q).ne', Real.log_pow, Real.log_pow]
    apply (mul_lt_mul_iff_right₀ hM).mp
    nlinarith [mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg q)]
  have hsub : (((2 * N - s : ℕ)) : ℝ) = 2 * N - s := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [← hsub] at hlt
  exact_mod_cast hlt

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  let shifts := range (2*N)
  let good (x : ℕ) := S.image (fun b => x+N-b)
  let bad (x : ℕ) := Fintype.piFinset (fun _ : Fin q => shifts \ good x)
  let allShifts := Fintype.piFinset (fun _ : Fin q => shifts)
  have hcard (x) (hx : x ∈ Icc 1 N) : (bad x).card = (2*N-S.card)^q := by
    have hsub : good x ⊆ shifts := by
      rintro _ hu
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hu
      have := mem_Icc.mp (hS hb)
      have := mem_Icc.mp hx
      exact mem_range.mpr (by omega)
    have hgood : (good x).card = S.card := by
      apply card_image_of_injOn
      intro b hb c hc he
      have := mem_Icc.mp (hS hb)
      have := mem_Icc.mp (hS hc)
      dsimp at he
      omega
    simp [bad, card_sdiff_of_subset hsub, hgood, shifts]
  have hfewer : ((Icc 1 N).biUnion bad).card < allShifts.card := calc
    _ ≤ ∑ x ∈ Icc 1 N, (bad x).card := card_biUnion_le
    _ = N*(2*N-S.card)^q := by rw [sum_const_nat hcard]; simp
    _ < (2*N)^q := union_threshold N q _ hN (by simpa using card_le_card hS) h
    _ = _ := by simp [allShifts, shifts]
  obtain ⟨f, hf, hnot⟩ := exists_mem_notMem_of_card_lt_card hfewer
  refine ⟨f, fun x hx => ?_⟩
  have hmiss : f ∉ bad x := fun hfx => hnot (mem_biUnion.mpr ⟨x, hx, hfx⟩)
  simp only [bad, Fintype.mem_piFinset, mem_sdiff,
    Fintype.mem_piFinset.mp hf, true_and, not_forall, not_not, good, mem_image] at hmiss
  obtain ⟨i, b, hb, he⟩ := hmiss
  have := mem_Icc.mp (hS hb)
  exact ⟨i, b, hb, by omega⟩
