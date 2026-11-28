import OMAStatements.S_mo_503562

open scoped BigOperators

namespace OMA.UnionDeterminant

open MvPolynomial

private theorem row_factors {n q : ℕ} (A : Fin n → Finset (Fin q)) :
    (∏ i : Fin n, ∏ k ∈ A i, (X k : MvPolynomial (Fin q) ℤ)) =
      ∏ k : Fin q, X k ^ OMA.S_mo_503562.frequency A k := by
  calc
    _ = ∏ i : Fin n, ∏ k : Fin q, if k ∈ A i then X k else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Finset.prod_ite_mem_eq (A i) X).symm
    _ = ∏ k : Fin q, ∏ i : Fin n, if k ∈ A i then X k else 1 :=
      Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k _
      simp only [← Finset.prod_filter, Finset.prod_const, OMA.S_mo_503562.frequency]

private theorem det_constant {n q : ℕ} (A : Fin n → Finset (Fin q))
    (hA : Function.Injective A) (B : Matrix (Fin n) (Fin n) (MvPolynomial (Fin q) ℤ))
    (hB : ∀ i j, B i j = ∏ k ∈ A j \ A i, X k) :
    constantCoeff B.det = 1 := by
  classical
  have entry (i j : Fin n) :
      (constantCoeff.mapMatrix B) i j = if A j ⊆ A i then 1 else 0 := by
    change constantCoeff (B i j) = _
    rw [hB, map_prod]
    by_cases h : A j ⊆ A i
    · simp [h, Finset.sdiff_eq_empty_iff_subset.mpr h]
    · obtain ⟨k, hj, hi⟩ : ∃ k, k ∈ A j ∧ k ∉ A i := by
        simpa [Finset.subset_iff] using h
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hj, hi⟩) (by simp)
  rw [RingHom.map_det, Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp [entry]
  · intro σ _ hσ
    have hnot : ¬ ∀ i, A i ⊆ A (σ i) := by
      intro hall
      apply hσ
      apply Equiv.ext
      intro j
      have leCard (i : Fin n) : (A i).card ≤ (A (σ i)).card :=
        Finset.card_le_card (hall i)
      have rle : (A (σ j)).card ≤ (A j).card := by
        by_contra! hlt
        have lt := Finset.sum_lt_sum (fun i _ => leCard i) ⟨j, Finset.mem_univ j, hlt⟩
        exact (ne_of_lt lt) (Equiv.sum_comp σ (fun i => (A i).card)).symm
      exact hA (Finset.eq_of_subset_of_card_le (hall j) rle).symm
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have zero : (∏ j, (constantCoeff.mapMatrix B) (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [entry, if_neg hi])
    rw [zero, smul_zero]
  · simp

theorem factor {n q : ℕ} (A : Fin n → Finset (Fin q)) (hA : Function.Injective A) :
    ∃ P : MvPolynomial (Fin q) ℤ,
      (OMA.S_mo_503562.unionMatrix A).det =
        P * (∏ k, X k ^ OMA.S_mo_503562.frequency A k) ∧
      ∀ k : Fin q, ¬ X k ∣ P := by
  let B : Matrix (Fin n) (Fin n) (MvPolynomial (Fin q) ℤ) :=
    fun i j => ∏ k ∈ A j \ A i, X k
  let v : Fin n → MvPolynomial (Fin q) ℤ := fun i => ∏ k ∈ A i, X k
  have hmatrix : OMA.S_mo_503562.unionMatrix A = Matrix.of (fun i j => v i * B i j) := by
    apply Matrix.ext
    intro i j
    symm
    change (∏ k ∈ A i, (X k : MvPolynomial (Fin q) ℤ)) * (∏ k ∈ A j \ A i, X k) = ∏ k ∈ A i ∪ A j, X k
    rw [mul_comm, ← Finset.union_sdiff_left]
    exact Finset.prod_sdiff (Finset.subset_union_left (s₁ := A i) (s₂ := A j))
  refine ⟨B.det, ?_, ?_⟩
  · rw [hmatrix, Matrix.det_mul_column]
    change (∏ i : Fin n, ∏ k ∈ A i, X k) * B.det = _
    rw [row_factors, mul_comm]
  · intro k hk
    obtain ⟨P, hp⟩ := hk
    have hc := det_constant A hA B (by intro i j; rfl)
    rw [hp, map_mul, constantCoeff_X, zero_mul] at hc
    exact zero_ne_one hc

end OMA.UnionDeterminant

theorem OMA.solution : type_of% @OMA.S_mo_503562.main := by
  intro n q A hA _ _
  exact OMA.UnionDeterminant.factor A hA