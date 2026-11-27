import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1

-- Step Erdos969.erdos_969.variants.evelyn_linfoot.R1.H1.R1.H2: hypothesis H2 of reduction Erdos969.erdos_969.variants.evelyn_linfoot.R1.H1.R1

/-!
The functional equation `ζ(1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ(s) * cos(π s / 2) * ζ(s)` holds for
`s ≠ 1` not a non-positive integer, which covers the open critical strip. So a zero `w` there
gives a zero `1 - w`.
-/

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1.H2
  intro w h0 h1 _ hz
  have hn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    have hre : w.re = -(n : ℝ) := by
      rw [h]
      simp
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h1' : w ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  rw [riemannZeta_one_sub hn h1', hz, mul_zero]
