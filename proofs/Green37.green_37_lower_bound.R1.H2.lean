import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H2: monotonicity of Green37.m in k
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  unfold Green37.m
  have hnonempty : {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₂}.Nonempty := by
    refine ⟨(Finset.range (k₂ * N + 1)).card, Finset.range (k₂ * N + 1), rfl, ?_⟩
    intro d ⟨hd1, hdN⟩
    refine ⟨0, {0 + n • d | (n : ℕ) (_ : n < (k₂ : ℕ∞))}, ?_, ?_, rfl⟩
    · rintro x ⟨n, hn, rfl⟩
      simp only [Finset.coe_range, Set.mem_Iio, zero_add, smul_eq_mul]
      have hn' : n < k₂ := by exact_mod_cast hn
      have hmul : n * d < k₂ * d := Nat.mul_lt_mul_of_pos_right hn' (by omega)
      have hle : k₂ * d ≤ k₂ * N := Nat.mul_le_mul_left k₂ hdN
      omega
    · have hinj : Function.Injective (fun n : Fin k₂ => 0 + n.val • d) := by
        intro i j hij
        simp only [zero_add, smul_eq_mul] at hij
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) hij)
      have hset : {0 + n • d | (n : ℕ) (_ : n < (k₂ : ℕ∞))} =
          Set.range (fun n : Fin k₂ => 0 + n.val • d) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_range]
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨⟨n, by exact_mod_cast hn⟩, rfl⟩
        · rintro ⟨⟨n, hn⟩, rfl⟩
          exact ⟨n, by exact_mod_cast hn, rfl⟩
      rw [hset, ENat.card_congr (Equiv.ofInjective _ hinj).symm, ENat.card_eq_coe_natCard, Nat.card_fin]
  have hsub : {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₂} ⊆
      {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₁} := by
    rintro m ⟨A, hAcard, hAcov⟩
    refine ⟨A, hAcard, ?_⟩
    intro d ⟨hd1, hdN⟩
    obtain ⟨a, s, hsA, _, hseq⟩ := hAcov d ⟨hd1, hdN⟩
    refine ⟨a, {a + n • d | (n : ℕ) (_ : n < (k₁ : ℕ∞))}, ?_, ?_, rfl⟩
    · rintro x ⟨n, hn, rfl⟩
      apply hsA
      rw [hseq]
      have hn' : n < k₁ := by exact_mod_cast hn
      exact ⟨n, by exact_mod_cast (lt_of_lt_of_le hn' hk), rfl⟩
    · have hinj : Function.Injective (fun n : Fin k₁ => a + n.val • d) := by
        intro i j hij
        simp only [smul_eq_mul] at hij
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_left_cancel hij))
      have hset : {a + n • d | (n : ℕ) (_ : n < (k₁ : ℕ∞))} =
          Set.range (fun n : Fin k₁ => a + n.val • d) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_range]
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨⟨n, by exact_mod_cast hn⟩, rfl⟩
        · rintro ⟨⟨n, hn⟩, rfl⟩
          exact ⟨n, by exact_mod_cast hn, rfl⟩
      rw [hset, ENat.card_congr (Equiv.ofInjective _ hinj).symm, ENat.card_eq_coe_natCard, Nat.card_fin]
  exact csInf_le_csInf (OrderBot.bddBelow _) hnonempty hsub
