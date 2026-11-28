import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-! Shorter proof of step H2 of Erdos142.erdos_142.variants.lower.R1.H2.R2:
for each x in [1, N], the shifts in [0, 2N) missing x + N are [0, 2N) \ (x + N - S),
of size 2N - |S|. A union bound over q-tuples of shifts yields a covering tuple. -/

open Finset Real in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  have hs : S.card ≤ N := by simpa using card_le_card hS
  have h2 : (0 : ℝ) < 2 * N := by positivity
  have hlt : N * (2 * N - S.card) ^ q < (2 * N) ^ q := by
    have h3 : (N : ℝ) * (2 * N - S.card : ℝ) ^ q < (2 * N) ^ q := by
      rw [← div_lt_one (pow_pos h2 q), mul_div_assoc, ← div_pow]
      calc _ ≤ N * exp (-(S.card / (2 * N))) ^ q := by
            gcongr
            · exact div_nonneg (by linarith [show (S.card : ℝ) ≤ N by exact_mod_cast hs]) h2.le
            · rw [sub_div, div_self h2.ne']; linarith [add_one_le_exp (-(S.card / (2 * N)))]
        _ = exp (log N - q * S.card / (2 * N)) := by
            rw [sub_eq_add_neg, exp_add, exp_log (by positivity), ← exp_nat_mul]; congr; ring
        _ < 1 := exp_lt_one_iff.mpr <| sub_neg.mpr <| (lt_div_iff₀ h2).mpr (by linarith)
    have hcast : ((2 * N - S.card : ℕ) : ℝ) = 2 * N - S.card := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    rw [← hcast] at h3
    exact_mod_cast h3
  let A x := range (2 * N) \ S.image (x + N - ·)
  let P (B : Finset ℕ) := Fintype.piFinset fun _ : Fin q => B
  have hU : ((Icc 1 N).biUnion (P ∘ A)).card < (P (range (2 * N))).card := calc
    _ ≤ ∑ x ∈ Icc 1 N, (P (A x)).card := card_biUnion_le
    _ = ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := sum_congr rfl fun x hx => by
        have := mem_Icc.mp hx
        have hsub : S.image (x + N - ·) ⊆ range (2 * N) := fun _ hy => by
          obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
          have := mem_Icc.mp (hS hb); exact mem_range.mpr (by omega)
        have hcard : (S.image (x + N - ·)).card = S.card :=
          card_image_of_injOn fun b hb b' hb' e => by
            have := mem_Icc.mp (hS hb); have := mem_Icc.mp (hS hb'); omega
        simp [P, A, card_sdiff_of_subset hsub, hcard]
    _ = N * (2 * N - S.card) ^ q := by simp
    _ < _ := by simpa [P] using hlt
  obtain ⟨f, hf, hfu⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨f, fun x hx => ?_⟩
  simp only [P, mem_biUnion, Function.comp_apply, Fintype.mem_piFinset,
    not_exists, not_and, not_forall] at hf hfu
  obtain ⟨t, ht⟩ := hfu x hx
  obtain ⟨b, hb, e⟩ := mem_image.mp (by simpa [A, hf t] using ht)
  have := mem_Icc.mp (hS hb)
  exact ⟨t, b, hb, by omega⟩
