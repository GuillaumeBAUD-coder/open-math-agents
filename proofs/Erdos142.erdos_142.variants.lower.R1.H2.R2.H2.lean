import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

open Finset Real in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  let s := S.card
  let M : ℝ := 2 * N
  have hs : s ≤ N := (card_le_card hS).trans_eq (Nat.card_Icc 1 N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 0 < M := by positivity
  have hlt : N * (2 * N - s) ^ q < (2 * N) ^ q := by
    have b : ((2 * N - s : ℕ) : ℝ) ≤ M * exp (-(s / M)) := by
      rw [Nat.cast_sub (by omega)]; push_cast
      linarith [mul_le_mul_of_nonneg_left (add_one_le_exp (-(s / M))) hM.le,
        div_mul_cancel₀ (s : ℝ) hM.ne']
    have c : ((N * (2 * N - s) ^ q : ℕ) : ℝ) < ((2 * N) ^ q : ℕ) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      calc (N : ℝ) * ((2 * N - s : ℕ) : ℝ) ^ q
        _ ≤ N * (M * exp (-(s / M))) ^ q :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) b q) hN0.le
        _ = N * (M ^ q * exp (-(q * (s / M)))) := by rw [mul_pow, ← exp_nat_mul]; ring_nf
        _ < N * (M ^ q * exp (-log N)) := by
            gcongr; rw [mul_div_assoc', lt_div_iff₀ hM]; linarith
        _ = ((2 * N : ℕ) : ℝ) ^ q := by
            rw [exp_neg, exp_log hN0]; dsimp [M]; push_cast; field_simp
    exact_mod_cast c
  let G x := S.image (x + N - ·)
  let B x := Fintype.piFinset fun _ : Fin q => range (2 * N) \ G x
  have hc x (hx : x ∈ Icc 1 N) : (B x).card = (2 * N - s) ^ q := by
    have sub : G x ⊆ range (2 * N) := fun _ u => by
      obtain ⟨b, hb, rfl⟩ := mem_image.1 u
      have := mem_Icc.1 (hS hb); have := mem_Icc.1 hx; exact mem_range.2 (by omega)
    have inj : Set.InjOn (x + N - ·) S := fun b hb c hc e => by
      have := mem_Icc.1 (hS hb); have := mem_Icc.1 (hS hc); dsimp at e; omega
    simp [B, card_sdiff_of_subset sub, G, card_image_of_injOn inj, s]
  have hU : ((Icc 1 N).biUnion B).card < (Fintype.piFinset fun _ : Fin q => range (2 * N)).card :=
    calc _ ≤ ∑ x ∈ Icc 1 N, (B x).card := card_biUnion_le
      _ = N * (2 * N - s) ^ q := by rw [sum_const_nat hc]; simp
      _ < _ := by simpa using hlt
  obtain ⟨f, hf, hn⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨f, fun x hx => ?_⟩
  have hm : f ∉ B x := fun u => hn (mem_biUnion.2 ⟨x, hx, u⟩)
  simp only [B, Fintype.mem_piFinset, mem_sdiff, Fintype.mem_piFinset.1 hf,
    true_and, not_forall, not_not, G, mem_image] at hm
  obtain ⟨t, b, hb, e⟩ := hm
  have := mem_Icc.1 (hS hb)
  exact ⟨t, b, hb, by omega⟩
