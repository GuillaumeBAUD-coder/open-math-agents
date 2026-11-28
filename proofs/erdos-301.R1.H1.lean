import OMAReductions.R_erdos_301_R1

/-! A = (N/2, N] is admissible: for a in A and B ⊆ A not containing a, B = ∅ gives sum 0, a single
element b gives 1/b ≠ 1/a, and two or more elements give a sum of at least 2/N > 1/a. So
f N ≥ #A = N - N/2, and N ≤ 2 f N. -/

theorem OMA.solution : OMA.R_erdos_301_R1.H1 := by
  intro N
  have hadm : OMA.S_erdos_301.NoUnitFractionSolution (Finset.Ioc (N / 2) N) := by
    intro a ha B hB haB heq
    rw [Finset.mem_Ioc] at ha
    have ha0 : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    rcases Nat.lt_or_ge B.card 2 with hc | hc
    · have hc' : B.card = 0 ∨ B.card = 1 := by omega
      rcases hc' with h0 | h1
      · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty] at heq
        have : (0 : ℚ) < 1 / a := by positivity
        linarith
      · obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 h1
        rw [Finset.sum_singleton, one_div, one_div, inv_inj, Nat.cast_inj] at heq
        exact haB (by rw [heq]; exact Finset.mem_singleton_self b)
    · have hN : (0 : ℚ) < N := by exact_mod_cast (show 0 < N by omega)
      have hle : ∀ b ∈ B, (1 : ℚ) / N ≤ 1 / b := by
        intro b hb
        have hb' := Finset.mem_Ioc.1 (hB hb)
        exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < b by omega))
          (by exact_mod_cast hb'.2)
      have hsum : (B.card : ℚ) * (1 / N) ≤ ∑ b ∈ B, 1 / (b : ℚ) := by
        have := Finset.sum_le_sum hle
        rwa [Finset.sum_const, nsmul_eq_mul] at this
      have h2 : (2 : ℚ) * (1 / N) ≤ (B.card : ℚ) * (1 / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      have h3 : (1 : ℚ) / a < 2 * (1 / N) := by
        rw [show (2 : ℚ) * (1 / N) = 2 / N by ring, div_lt_div_iff₀ ha0 hN]
        have : (N : ℚ) < 2 * a := by exact_mod_cast (show N < 2 * a by omega)
        linarith
      linarith
  have hmem : Finset.Ioc (N / 2) N ∈
      (Finset.Icc 1 N).powerset.filter OMA.S_erdos_301.NoUnitFractionSolution := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun x hx => ?_, hadm⟩
    rw [Finset.mem_Ioc] at hx
    rw [Finset.mem_Icc]
    omega
  have hle : (Finset.Ioc (N / 2) N).card ≤ OMA.S_erdos_301.f N := Finset.le_sup hmem
  rw [Nat.card_Ioc] at hle
  omega
