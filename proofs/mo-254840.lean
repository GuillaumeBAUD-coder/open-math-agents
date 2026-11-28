import OMAStatements.S_mo_254840
import Mathlib

-- Problem mo-254840: the statement claims that for some n >= 1 there are more than n pairwise orthogonal
-- vectors with all entries 1 or -1 in dimension n.
-- Upstream: statements/mo-254840.lean (declaration OMA.S_mo_254840.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: this is impossible. Let M be the rational matrix whose rows are the vectors of S. Each row has
-- squared length n and distinct rows are orthogonal, so M M^T = n I, an invertible |S| x |S| matrix of rank
-- |S|. But rank (M M^T) <= rank M <= n, the number of columns. Hence |S| <= n.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_254840.main) := by
  rintro ⟨n, hn, S, hpm, horth, hcard⟩
  have hnq : (n : ℚ) ≠ 0 := by
    have h0 : n ≠ 0 := by omega
    exact_mod_cast h0
  obtain ⟨M, hM⟩ : ∃ M : Matrix S (Fin n) ℚ, ∀ a i, M a i = (((a : Fin n → ℤ) i : ℤ) : ℚ) :=
    ⟨Matrix.of fun a i => (((a : Fin n → ℤ) i : ℤ) : ℚ), fun a i => rfl⟩
  have hprod : M * M.transpose = (n : ℚ) • (1 : Matrix S S ℚ) := by
    ext a b
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp only [Matrix.transpose_apply, hM]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, mul_one]
      have hsq : ∀ i : Fin n, (((a : Fin n → ℤ) i : ℤ) : ℚ) * (((a : Fin n → ℤ) i : ℤ) : ℚ) = 1 := by
        intro i
        rcases hpm (a : Fin n → ℤ) a.2 i with h | h <;> rw [h] <;> norm_num
      rw [Finset.sum_congr rfl (fun i _ => hsq i)]
      simp
    · rw [if_neg hab, mul_zero]
      have h0 := horth (a : Fin n → ℤ) a.2 (b : Fin n → ℤ) b.2 (fun h => hab (Subtype.ext h))
      have h1 : ((∑ i, (a : Fin n → ℤ) i * (b : Fin n → ℤ) i : ℤ) : ℚ) = 0 := by
        rw [h0]
        norm_num
      push_cast at h1
      exact h1
  have hunit : IsUnit ((n : ℚ) • (1 : Matrix S S ℚ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr hnq).pow _
  have hr1 : ((n : ℚ) • (1 : Matrix S S ℚ)).rank = Fintype.card S := Matrix.rank_of_isUnit _ hunit
  have hr2 : (M * M.transpose).rank ≤ M.rank := Matrix.rank_mul_le_left _ _
  have hr3 : M.rank ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width M
  rw [hprod, hr1] at hr2
  rw [Fintype.card_fin] at hr3
  have hc : Fintype.card S = S.card := Fintype.card_coe S
  omega
