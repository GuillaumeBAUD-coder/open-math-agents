import OMAReductions.R_OeisA262813_conjecture_2_R1

-- Step OeisA262813.conjecture_2.R1.H1
-- Credit: @caa1982

private lemma a_eq_small {n : ℕ} (hn : n ≤ 306) :
    OeisA262813.a n =
      ∑ x ∈ Finset.range (min (n + 1) 7),
        ∑ y ∈ Finset.range (min (n + 1) 18),
          ∑ z ∈ Finset.Ico 1 (min (n + 1) 25),
            if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0 := by
  unfold OeisA262813.a
  rw [← Finset.sum_subset (Finset.range_mono (Nat.min_le_left _ _))]
  · apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_subset (Finset.range_mono (Nat.min_le_left _ _))]
    · apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_subset (Finset.Ico_subset_Ico_right (Nat.min_le_left _ _))]
      intro z hz hzn
      have hz25 : 25 ≤ z := by
        simp only [Finset.mem_Ico] at hz hzn
        omega
      have htri : 325 ≤ Nat.triangular z := by
        rw [Nat.triangular]
        have : 25 * 26 ≤ z * (z + 1) := Nat.mul_le_mul hz25 (by omega)
        omega
      have hne : (x ^ 3 + y ^ 2 + Nat.triangular z == n) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp [hne]
    · intro y hy hyn
      have hy18 : 18 ≤ y := by
        simp only [Finset.mem_range] at hy hyn
        omega
      apply Finset.sum_eq_zero
      intro z _
      have hy2 : 324 ≤ y ^ 2 := by nlinarith
      have hne : (x ^ 3 + y ^ 2 + Nat.triangular z == n) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp [hne]
  · intro x hx hxn
    have hx7 : 7 ≤ x := by
      simp only [Finset.mem_range] at hx hxn
      omega
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro z _
    have hx3 : 343 ≤ x ^ 3 := Nat.pow_le_pow_left hx7 3
    have hne : (x ^ 3 + y ^ 2 + Nat.triangular z == n) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp [hne]

theorem OMA.solution : OMA.R_OeisA262813_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a_eq_small (by omega)]; decide +kernel
  · rw [a_eq_small (by omega)]; decide +kernel
  · rw [a_eq_small (by omega)]; decide +kernel
  · rw [a_eq_small (by omega)]; decide +kernel
  · rw [a_eq_small (by omega)]; decide +kernel
  · rw [a_eq_small (by omega)]; decide +kernel
  · rw [a_eq_small (by omega)]; decide +kernel
