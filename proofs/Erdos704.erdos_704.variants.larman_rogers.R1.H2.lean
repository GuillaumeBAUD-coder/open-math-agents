import OMAReductions.R_Erdos704_erdos_704_variants_larman_rogers_R1

-- Step Erdos704.erdos_704.variants.larman_rogers.R1.H2: hypothesis H2 of reduction Erdos704.erdos_704.variants.larman_rogers.R1
-- Credit: @dk8827
-- H2 := ∀ (A : Type) [AddCommGroup A] [Fintype A] (S : Finset A), S.Nonempty →     ∃ T : Finset A,       (T.card : ℝ) ≤         1 + (1 + Real.log (Fintype.card A : ℝ)) * ((Fintype.card A : ℝ) / S.card) ∧       ∀ x : A, ∃ t ∈ T, x - t ∈ S

theorem OMA.solution : OMA.R_Erdos704_erdos_704_variants_larman_rogers_R1.H2 := by
  intro A _ _ S hS
  classical
  have hs : 0 < S.card := Finset.card_pos.mpr hS
  have hsN : S.card ≤ Fintype.card A := Finset.card_le_univ S
  let N : ℝ := Fintype.card A
  let s : ℝ := S.card
  have hs_pos : 0 < s := by
    dsimp [s]
    exact_mod_cast hs
  have hs_le_N : s ≤ N := by
    dsimp [s, N]
    exact_mod_cast hsN
  have hN_pos : 0 < N := hs_pos.trans_le hs_le_N
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (show 1 ≤ Fintype.card A by omega)
  let bound := (1 + Real.log N) * (N / s)
  let k := ⌈bound⌉₊
  have hbound : 0 ≤ bound :=
    mul_nonneg (by linarith [Real.log_nonneg hN_one]) (div_nonneg hN_pos.le hs_pos.le)
  have hexponent : 1 + Real.log N ≤ (k : ℝ) * (s / N) := by
    calc
      1 + Real.log N = bound * (s / N) := by
        dsimp [bound]
        field_simp
      _ ≤ (k : ℝ) * (s / N) :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil bound) (div_nonneg hs_pos.le hN_pos.le)
  -- The total fraction of bad samples is less than one.
  have hprob : N * (1 - s / N) ^ k < 1 := by
    calc
      _ ≤ N * (Real.exp (-(s / N))) ^ k := by
        apply mul_le_mul_of_nonneg_left _ hN_pos.le
        apply pow_le_pow_left₀ (sub_nonneg.mpr ((div_le_iff₀ hN_pos).mpr (by simpa using hs_le_N)))
        simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(s / N))
      _ = N * Real.exp (-(k * (s / N))) := by rw [← Real.exp_nat_mul, mul_neg]
      _ ≤ N * Real.exp (-(1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hexponent)) hN_pos.le
      _ = Real.exp (-1) := by
        rw [neg_add, Real.exp_add, Real.exp_neg (Real.log N), Real.exp_log hN_pos]
        field_simp
      _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hcount : Fintype.card A * (Fintype.card A - S.card) ^ k < Fintype.card A ^ k := by
    have hd : 1 - s / N = (N - s) / N := by field_simp
    rw [hd, div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos hN_pos _), one_mul] at hprob
    have hcast : ((Fintype.card A - S.card : ℕ) : ℝ) = N - s := Nat.cast_sub hsN
    rw [← hcast] at hprob
    dsimp [N] at hprob
    exact_mod_cast hprob
  let good (x : A) := S.image (fun a => x - a)
  have hgood (x t : A) : t ∈ good x ↔ x - t ∈ S := by
    constructor
    · intro ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
      simpa only [sub_sub_cancel] using ha
    · intro ht
      exact Finset.mem_image.mpr ⟨x - t, ht, sub_sub_cancel _ _⟩
  have good_card (x : A) : (good x).card = S.card :=
    Finset.card_image_of_injective _ (sub_right_injective : Function.Injective (x - ·))
  -- Count the ordered samples whose translates miss a given point.
  let bad (x : A) := Fintype.piFinset (fun _ : Fin k => (good x)ᶜ)
  have hbad (x : A) : (bad x).card = (Fintype.card A - S.card) ^ k := by
    simp only [bad, Fintype.card_piFinset_const, Finset.card_compl, good_card]
  let badAll := Finset.univ.biUnion bad
  have hbadAll : badAll.card < (Finset.univ : Finset (Fin k → A)).card := by
    calc
      _ ≤ Fintype.card A * (Fintype.card A - S.card) ^ k :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun x _ => (hbad x).le)
      _ < _ := by simpa only [Finset.card_univ, Fintype.card_pi_const] using hcount
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadAll
  refine ⟨Finset.univ.image w, ?_, ?_⟩
  · have hc : (Finset.univ.image w).card ≤ k := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (s := Finset.univ) (f := w))
    exact (Nat.cast_le.mpr hc).trans (by simpa only [add_comm] using (Nat.ceil_lt_add_one hbound).le)
  · intro x
    have hwb : w ∉ bad x := fun hx => hw (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, hx⟩)
    have hi : ∃ i, w i ∈ good x := by
      by_contra! h
      exact hwb (Fintype.mem_piFinset.mpr (fun i => Finset.mem_compl.mpr (h i)))
    obtain ⟨i, hi⟩ := hi
    exact ⟨w i, Finset.mem_image_of_mem w (Finset.mem_univ i), (hgood _ _).mp hi⟩
