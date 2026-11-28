import OMAStatements.S_oeis_a137560

namespace OMA.P_oeis_a137560

open Polynomial Finset OMA.S_oeis_a137560

private theorem constant_zero (n : ℕ) : (P n).coeff 0 = 0 := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [coeff_zero_eq_eval_zero] at ih ⊢
    simp [P, ih]

private theorem stable (k : ℕ) :
    1 ≤ k → ∀ n ≥ k, (P n).coeff k = (catalan (k - 1) : ℤ) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [P, pow_two, coeff_add, coeff_mul]
    by_cases h1 : k = 1
    · subst k
      have hz : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 1, (P m).coeff p.1 * (P m).coeff p.2 = 0 := by
        apply sum_eq_zero
        intro p hp
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have hzero : p.1 = 0 ∨ p.2 = 0 := by omega
        rcases hzero with he | he <;> simp [he, constant_zero]
      rw [hz]
      simp
    · have hX : (X : ℤ[X]).coeff k = 0 := by simp [coeff_X, Ne.symm h1]
      rw [hX, add_zero]
      let A := (Finset.HasAntidiagonal.antidiagonal k).filter fun p => 0 < p.1 ∧ 0 < p.2
      have hA :
          ∑ p ∈ A, (P m).coeff p.1 * (P m).coeff p.2 =
            ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (P m).coeff p.1 * (P m).coeff p.2 := by
        apply sum_subset (filter_subset _ _)
        intro p hmem hp
        have hzero : p.1 = 0 ∨ p.2 = 0 := by
          simp only [mem_filter] at hp
          by_contra! hz
          exact hp ⟨hmem, by omega, by omega⟩
        rcases hzero with he | he <;> simp [he, constant_zero]
      rw [← hA, show k - 1 = (k - 2) + 1 by omega, catalan_succ', Nat.cast_sum]
      simp only [Nat.cast_mul]
      refine sum_bij (fun p _ => (p.1 - 1, p.2 - 1)) ?_ ?_ ?_ ?_
      · intro p hp
        obtain ⟨hs, hx, hy⟩ := mem_filter.mp hp
        simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hs ⊢
        omega
      · intro p hp q hq he
        obtain ⟨_, hp1, hp2⟩ := mem_filter.mp hp
        obtain ⟨_, hq1, hq2⟩ := mem_filter.mp hq
        have e1 := congrArg Prod.fst he
        have e2 := congrArg Prod.snd he
        exact Prod.ext (by dsimp at e1; omega) (by dsimp at e2; omega)
      · intro q hq
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
        refine ⟨(q.1 + 1, q.2 + 1), mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr ?_, ?_⟩, ?_⟩
        · dsimp
          omega
        · simp
        · simp
      · intro p hp
        obtain ⟨hs, hx, hy⟩ := mem_filter.mp hp
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hs
        rw [ih p.1 (by omega) (by omega) m (by omega), ih p.2 (by omega) (by omega) m (by omega)]

end OMA.P_oeis_a137560

open OMA.P_oeis_a137560 in
theorem OMA.solution : type_of% @OMA.S_oeis_a137560.main := by
  intro k hk
  exact ⟨k, stable k hk⟩