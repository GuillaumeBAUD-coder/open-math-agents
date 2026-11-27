import OMAReductions.R_Green37_green_37_lower_bound_R1

open Finset

lemma green37_containsAP_mono {A : Set ℕ} {k₁ k₂ d : ℕ} (hd : 1 ≤ d) (hk : k₁ ≤ k₂)
    (h : A.ContainsAP k₂ d) : A.ContainsAP k₁ d := by
  obtain ⟨a, s, hsA, hsLen⟩ := h
  let T : Finset ℕ := (Finset.range k₁).image fun n => a + n * d
  refine ⟨a, (T : Set ℕ), ?_, ?_⟩
  · intro x hx
    apply hsA
    rw [hsLen.eq]
    simp only [T, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    refine ⟨n, ?_, by simp⟩
    exact_mod_cast lt_of_lt_of_le hn hk
  · constructor
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _ ?_, Finset.card_range]
      intro x y hxy
      have hmul : x * d = y * d := Nat.add_left_cancel hxy
      exact Nat.eq_of_mul_eq_mul_right hd hmul
    · ext x
      simp [T]

lemma green37_isAPCover_mono {A : Set ℕ} {N k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : Green37.IsAPCover A N k₂) : Green37.IsAPCover A N k₁ := by
  intro d hd
  exact green37_containsAP_mono hd.1 hk (h d hd)

lemma green37_isAPCover_range (N k : ℕ) :
    Green37.IsAPCover ((Finset.range (k * N + 1)) : Set ℕ) N k := by
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_right hd.1 hxy
  · ext x
    simp

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  unfold Green37.m
  let S₂ : Set ℕ := {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₂}
  have hne : S₂.Nonempty := by
    refine ⟨k₂ * N + 1, ?_⟩
    exact ⟨Finset.range (k₂ * N + 1), Finset.card_range _, green37_isAPCover_range N k₂⟩
  change sInf {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₁} ≤ sInf S₂
  obtain ⟨A, hAcard, hAcover⟩ := Nat.sInf_mem hne
  exact Nat.sInf_le ⟨A, hAcard, green37_isAPCover_mono hk hAcover⟩
