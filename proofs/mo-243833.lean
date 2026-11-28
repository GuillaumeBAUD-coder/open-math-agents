import OMAStatements.S_mo_243833

-- Problem: MathOverflow 243833. adj(A) i j is the determinant of A with row j replaced by e_i; in each
-- term of the Leibniz expansion one factor comes from that row (degree 0) and the other n from A
-- (degree <= d), so the total degree is <= n d. Sharpness: A = diag(X_0^d, ..., X_0^d), whose
-- adjugate has (0, 0) entry X_0^(n d).

open Matrix MvPolynomial in
theorem OMA.solution : type_of% @OMA.S_mo_243833.main := by
  refine ⟨fun m n d A hA i j => ?_, fun m n d => ?_⟩
  · rw [adjugate_apply, det_apply']
    apply totalDegree_finsetSum_le
    intro σ _
    refine (totalDegree_mul _ _).trans ?_
    have hε : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin m) ℝ).totalDegree = 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, totalDegree_neg]
    rw [hε, zero_add]
    refine (totalDegree_finsetProd _ _).trans ?_
    have hle : ∀ k, (A.updateRow j (Pi.single i 1) (σ k) k).totalDegree
        ≤ if σ k = j then 0 else d := by
      intro k
      split_ifs with h
      · rw [h, updateRow_self]
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · rw [updateRow_ne h]; exact hA _ _
    calc ∑ k, (A.updateRow j (Pi.single i 1) (σ k) k).totalDegree
        ≤ ∑ k, (if σ k = j then 0 else d) := Finset.sum_le_sum fun k _ => hle k
      _ = ∑ k, (if k = j then 0 else d) := Equiv.sum_comp σ (fun k => if k = j then 0 else d)
      _ = n * d := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), if_pos rfl, add_zero,
          Finset.sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk)),
          Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel]
  · refine ⟨diagonal (fun _ => X 0 ^ d), ?_, ?_, ?_⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp [totalDegree_X_pow]
      · simp [diagonal_apply_ne _ h]
    · simp [totalDegree_X_pow]
    · rw [adjugate_diagonal, diagonal_apply_eq, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        Nat.add_sub_cancel, ← pow_mul, totalDegree_X_pow, mul_comm]
