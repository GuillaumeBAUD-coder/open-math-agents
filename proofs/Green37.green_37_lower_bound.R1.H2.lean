import OMAReductions.R_Green37_green_37_lower_bound_R1

-- A cover for longer progressions also covers every shorter length.
lemma OMA.cover_mono (A : Finset ℕ) (N k₁ k₂ : ℕ) (hk : k₁ ≤ k₂)
    (hcover : Green37.IsAPCover (A : Set ℕ) N k₂) :
    Green37.IsAPCover (A : Set ℕ) N k₁ := by
  intro d hd
  obtain ⟨a, s, hs, hAP⟩ := hcover d hd
  refine ⟨a, ((Finset.range k₁).image (fun i ↦ a + i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply hs
    rw [hAP.2]
    refine ⟨i, ?_, ?_⟩
    · exact_mod_cast (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    · simp
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 (Nat.add_left_cancel h)), Finset.card_range]
  · ext x
    simp

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  let S : Set ℕ := {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₂}
  have hne : S.Nonempty := by
    refine ⟨k₂ * N + 1, Finset.range (k₂ * N + 1), Finset.card_range _, ?_⟩
    intro d hd
    refine ⟨0, ((Finset.range k₂).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
      exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _
          (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
    · ext x; simp
  obtain ⟨A, hcard, hcover⟩ := Nat.sInf_mem hne
  change sInf {m : ℕ | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₁} ≤ sInf S
  apply Nat.sInf_le
  exact ⟨A, hcard, OMA.cover_mono A N k₁ k₂ hk hcover⟩
