import FormalConjectures.ErdosProblems.«395»

theorem OMA.solution : type_of% @Erdos395.erdos_395.variants.one := by
  rintro ⟨c, hc, h⟩
  let z : Fin 2 → ℂ := ![1, Complex.I]
  have hz : ∀ i, ‖z i‖ = 1 := by
    intro i
    fin_cases i <;> simp [z]
  have hempty : {ε : Fin 2 → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧
      ‖∑ i, (ε i : ℂ) * z i‖ ≤ 1} = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro ε ⟨hs, hb⟩
    let w : ℂ := ∑ i, (ε i : ℂ) * z i
    have hsq : ‖w‖ ^ 2 = (ε 0 : ℝ) ^ 2 + (ε 1 : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [w, z, Fin.sum_univ_two, pow_two]
    change ‖w‖ ≤ 1 at hb
    rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;>
      norm_num [h0, h1] at hsq <;> nlinarith [norm_nonneg w]
  have hcount : Erdos395.signedSumCount z 1 = 0 := by
    rw [Erdos395.signedSumCount, hempty, Set.ncard_empty]
  have key := h 2 (by norm_num) z hz
  rw [hcount] at key
  norm_num at key
  linarith
