import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step H2 of Green37.green_37_lower_bound.R1.
-- Credit: @sennemmi

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N shorter longer hlength
  have containsPrefix (A : Set ℕ) (a d k : ℕ) (hd : 0 < d)
      (hmem : ∀ i < k, a + i * d ∈ A) : Set.ContainsAP A k d := by
    refine ⟨a, ((Finset.range k).image (fun i ↦ a + i * d) : Set ℕ), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hmem i (Finset.mem_range.mp hi)
    · have hinj : Function.Injective (fun i : ℕ ↦ a + i * d) := by
        intro i j hij
        exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
      rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _ hinj, Finset.card_range]
    · ext x
      simp
  let covers : Set ℕ := {s | ∃ A : Finset ℕ, A.card = s ∧ Green37.IsAPCover (A : Set ℕ) N longer}
  have hnonempty : covers.Nonempty := by
    refine ⟨longer * N + 1, Finset.range (longer * N + 1), Finset.card_range _, ?_⟩
    intro d hd
    apply containsPrefix _ 0 d longer hd.1
    intro i hi
    simp only [zero_add, Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  change Green37.m N shorter ≤ sInf covers
  obtain ⟨A, hcard, hcover⟩ := Nat.sInf_mem hnonempty
  apply Nat.sInf_le
  refine ⟨A, hcard, ?_⟩
  intro d hd
  obtain ⟨a, S, hsubset, hprogression⟩ := hcover d hd
  apply containsPrefix _ a d shorter hd.1
  intro i hi
  apply hsubset
  rw [hprogression.eq]
  refine ⟨i, ?_, by simp⟩
  exact_mod_cast hi.trans_le hlength
