import FormalConjectures.ErdosProblems.«395»

-- Problem: Erdős Problem 395 — one
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/395.lean:70 (declaration Erdos395.erdos_395.variants.one)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos395.erdos_395.variants.one := by
  rintro ⟨c, hc, h⟩
  have hz : ∀ i, ‖(![(1:ℂ), Complex.I] : Fin 2 → ℂ) i‖ = 1 := by
    intro i
    fin_cases i <;> simp
  have hempty : {ε : Fin 2 → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧
      ‖∑ i, (ε i : ℂ) * (![(1:ℂ), Complex.I] : Fin 2 → ℂ) i‖ ≤ 1} = ∅ := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hε, hle⟩
    have hεsq (i : Fin 2) : (ε i : ℝ) ^ 2 = 1 := by
      exact_mod_cast (sq_eq_one_iff.mpr (Or.symm (hε i)))
    have hsq : ‖∑ i, (ε i : ℂ) * (![(1:ℂ), Complex.I] : Fin 2 → ℂ) i‖ ^ 2 = 2 := by
      norm_num [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply, ← sq, hεsq]
    have hn : ‖∑ i, (ε i : ℂ) * (![(1:ℂ), Complex.I] : Fin 2 → ℂ) i‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (∑ i, (ε i : ℂ) * (![(1:ℂ), Complex.I] : Fin 2 → ℂ) i)]
    linarith
  have hcount : Erdos395.signedSumCount (![(1:ℂ), Complex.I] : Fin 2 → ℂ) 1 = 0 := by
    unfold Erdos395.signedSumCount
    rw [hempty, Set.ncard_empty]
  have key := h 2 (by norm_num) ![(1:ℂ), Complex.I] hz
  rw [hcount] at key
  norm_num at key
  linarith
