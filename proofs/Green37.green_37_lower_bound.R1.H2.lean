import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H2: hypothesis H2 of reduction Green37.green_37_lower_bound.R1
-- Credit: @DeepDuke
-- H2 := ∀ N k₁ k₂ : ℕ, k₁ ≤ k₂ → Green37.m N k₁ ≤ Green37.m N k₂

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  have hex : {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₂}.Nonempty := by
    refine ⟨k₂*N+1, Finset.range (k₂*N+1), Finset.card_range _, ?_⟩
    intro d hd
    refine ⟨0, ((Finset.range k₂).image (fun i => i*d) : Set ℕ), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
      exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_right hd.1 h),
        Finset.card_range]
    · ext x
      simp
  obtain ⟨A, hcard, hcover⟩ := Nat.sInf_mem hex
  change A.card = Green37.m N k₂ at hcard
  rw [← hcard]
  apply Nat.sInf_le
  refine ⟨A, rfl, ?_⟩
  intro d hd
  obtain ⟨a, s, hsA, hcard, hs⟩ := hcover d hd
  let t := (Finset.range k₁).image (fun i => a+i*d)
  refine ⟨a, (t : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply hsA
    rw [hs]
    refine ⟨i, ?_, by simp [nsmul_eq_mul]⟩
    exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd.1 (Nat.add_left_cancel hij)
  · ext x
    simp [t, nsmul_eq_mul]

