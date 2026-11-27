import FormalConjectures.ErdosProblems.«395»

-- Original counterexample (1,I) due to the prior proof by @ldy985.
-- New proof: compute the square of the norm after the two sign choices.
open Complex

theorem OMA.solution : type_of% @Erdos395.erdos_395.variants.one := by
  rintro ⟨c, hc, h⟩
  let z : Fin 2 → ℂ := ![1, I]
  have hz : ∀ i, ‖z i‖ = 1 := by
    intro i
    fin_cases i <;> simp [z]
  have hempty : {e : Fin 2 → ℤ | (∀ i, e i = -1 ∨ e i = 1) ∧
      ‖∑ i, (e i : ℂ) * z i‖ ≤ 1} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨he, hl⟩
    have hs : ‖∑ i, (e i : ℂ) * z i‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (∑ i, (e i : ℂ) * z i)]
    rw [Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_two] at hs
    rcases he 0 with h0 | h0 <;> rcases he 1 with h1 | h1 <;>
      norm_num [z, h0, h1, Complex.mul_re, Complex.mul_im] at hs
  have key := h 2 (by norm_num) z hz
  have hcount : Erdos395.signedSumCount z 1 = 0 := by
    unfold Erdos395.signedSumCount
    rw [hempty, Set.ncard_empty]
  rw [hcount] at key
  norm_num at key
  linarith

-- Original proof from the upstream repository, last author @Witek-ops.
