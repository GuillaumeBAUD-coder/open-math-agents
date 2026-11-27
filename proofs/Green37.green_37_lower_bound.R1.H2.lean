import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Credit: Hanan Beer (@hananzlt)
-- Monotonicity of the minimum AP-cover size in progression length.

namespace OMA.Green37Monotonicity

lemma cover_mono {A : Set ℕ} {N k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (hA : Green37.IsAPCover A N k₂) : Green37.IsAPCover A N k₁ := by
  intro d hd
  obtain ⟨a, s, hsA, hcard, hs⟩ := hA d hd
  refine ⟨a, ((Finset.range k₁).image (fun i ↦ a + i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply hsA
    rw [hs]
    exact ⟨i, by exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hi) hk, by simp⟩
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ (fun i j h ↦ Nat.eq_of_mul_eq_mul_right hd.1 (Nat.add_left_cancel h)), Finset.card_range]
  · ext x
    simp

lemma covers_nonempty (N k : ℕ) :
    {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}.Nonempty := by
  refine ⟨k * N + 1, Finset.range (k * N + 1), Finset.card_range _, ?_⟩
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x; simp

end OMA.Green37Monotonicity

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  unfold Green37.m
  apply csInf_le_csInf' (OMA.Green37Monotonicity.covers_nonempty N k₂)
  rintro m ⟨A, hcard, hA⟩
  exact ⟨A, hcard, OMA.Green37Monotonicity.cover_mono hk hA⟩
