import OMAReductions.R_Green37_green_37_lower_bound_R1

namespace OMA.GreenPrefix

open Finset

theorem containsPrefix {A : Set ℕ} (k a d : ℕ) (hd : 1 ≤ d)
    (h : ∀ i < k, a + i * d ∈ A) : Set.ContainsAP A k d := by
  refine ⟨a, ((range k).image (fun i ↦ a + i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact h i (mem_range.mp hi)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      card_image_of_injective _ (fun _ _ he =>
        Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel he)), card_range]
  · ext x
    simp [nsmul_eq_mul]

theorem coverExists (N k : ℕ) : ∃ A : Finset ℕ, Green37.IsAPCover (A : Set ℕ) N k := by
  refine ⟨range (k * N + 1), ?_⟩
  intro d hd
  apply containsPrefix k 0 d hd.1
  intro i hi
  simp only [zero_add, mem_coe, mem_range]
  exact Nat.lt_succ_of_le (Nat.mul_le_mul hi.le hd.2)

end OMA.GreenPrefix

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k l hkl
  let S : Set ℕ := {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N l}
  have hne : S.Nonempty := by
    obtain ⟨A, hA⟩ := OMA.GreenPrefix.coverExists N l
    exact ⟨A.card, A, rfl, hA⟩
  have hmin : Green37.m N l ∈ S := Nat.sInf_mem hne
  obtain ⟨A, hc, hA⟩ := hmin
  apply Nat.sInf_le
  refine ⟨A, hc, ?_⟩
  intro d hd
  obtain ⟨a, T, hT, _, heq⟩ := hA d hd
  apply OMA.GreenPrefix.containsPrefix k a d hd.1
  intro i hi
  apply hT
  rw [heq]
  exact ⟨i, by exact_mod_cast lt_of_lt_of_le hi hkl, by simp [nsmul_eq_mul]⟩
