import OMAReductions.R_Green37_green_37_lower_bound_R1

/-! Initial segments of progressions give monotonicity of the minimum cover size. -/

open Finset Green37

namespace OMA.Green37Cover

lemma contains_initial_segment {A : Set ℕ} {a d k : ℕ} (hd : 0 < d)
    (h : ∀ i < k, a + i * d ∈ A) : A.ContainsAP k d := by
  let S := (Finset.range k).image fun i => a + i * d
  refine ⟨a, (S : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact h i (Finset.mem_range.mp hi)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard]
    dsimp [S]
    rw [Finset.card_image_of_injective _ (fun _ _ he =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel he)), Finset.card_range]
  · ext x
    simp [S]

lemma attained (N k : ℕ) :
    ∃ A : Finset ℕ, A.card = m N k ∧ IsAPCover (A : Set ℕ) N k := by
  change m N k ∈ {n | ∃ A : Finset ℕ, A.card = n ∧ IsAPCover (A : Set ℕ) N k}
  unfold m
  apply Nat.sInf_mem
  refine ⟨_, Finset.range (k * N + 1), Finset.card_range _, ?_⟩
  intro d hd
  refine contains_initial_segment (a := 0) hd.1 (fun i hi => ?_)
  simpa only [zero_add, Finset.mem_coe, Finset.mem_range] using
    (Nat.lt_succ_of_le (Nat.mul_le_mul hi.le hd.2))

end OMA.Green37Cover

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  obtain ⟨A, hA, hcover⟩ := OMA.Green37Cover.attained N k₂
  apply Nat.sInf_le
  refine ⟨A, hA, fun d hd => ?_⟩
  obtain ⟨a, S, hsub, _, heq⟩ := hcover d hd
  apply OMA.Green37Cover.contains_initial_segment (a := a) hd.1
  intro i hi
  apply hsub
  rw [heq]
  exact ⟨i, by exact_mod_cast hi.trans_le hk, by simp⟩
