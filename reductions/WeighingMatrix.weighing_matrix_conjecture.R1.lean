import FormalConjectures.Wikipedia.WeighingMatrix

/-! Direct sums and Sylvester doubling reduce existence to two dense families. -/

-- Credit: @desenyon
open WeighingMatrix Matrix
namespace OMA.R_WeighingMatrix_weighing_matrix_conjecture_R1

/-- Dense weights at orders congruent to four modulo eight. -/
def H1 : Prop := ∀ m w : ℕ, m % 2 = 1 → 4 * (m / 2) < w → w ≤ 4 * m →
  ∃ W, IsWeighingMatrix (n := 4 * m) w W

/-- Dense odd weights at orders divisible by eight. -/
def H2 : Prop := ∀ m w : ℕ, m % 2 = 0 → w % 2 = 1 → 4 * (m / 2) < w → w ≤ 4 * m →
  ∃ W, IsWeighingMatrix (n := 4 * m) w W

private theorem pack {ι : Type} [Fintype ι] [DecidableEq ι] {n w : ℕ}
    (e : Fin n ≃ ι) (M : Matrix ι ι ℤ)
    (entries : ∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1)
    (gram : M * M.transpose = (w : ℤ) • 1) :
    ∃ W, IsWeighingMatrix (n := n) w W := by
  refine ⟨M.submatrix e e, fun i j => entries (e i) (e j), ?_⟩
  change M.submatrix e e * M.transpose.submatrix e e = _
  rw [submatrix_mul_equiv, gram]
  change (w : ℤ) • (1 : Matrix ι ι ℤ).submatrix e e = _
  rw [submatrix_one_equiv]

private theorem addOrders {a b w : ℕ} {A : Matrix (Fin a) (Fin a) ℤ}
    {B : Matrix (Fin b) (Fin b) ℤ} (ha : IsWeighingMatrix w A) (hb : IsWeighingMatrix w B) :
    ∃ W, IsWeighingMatrix (n := a + b) w W := by
  apply pack finSumFinEquiv.symm (fromBlocks A 0 0 B)
  · rintro (i|i) (j|j)
    exacts [ha.1 i j, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), hb.1 i j]
  · simp [fromBlocks_transpose, fromBlocks_multiply, ha.2, hb.2,
      ← fromBlocks_one, fromBlocks_smul]

private theorem doubleWeight {a w : ℕ} {A : Matrix (Fin a) (Fin a) ℤ}
    (ha : IsWeighingMatrix w A) :
    ∃ W, IsWeighingMatrix (n := a + a) (w + w) W := by
  apply pack finSumFinEquiv.symm (fromBlocks A A A (-A))
  · rintro (i|i) (j|j)
    exacts [ha.1 i j, ha.1 i j, ha.1 i j, ha.neg.1 i j]
  · simp [fromBlocks_transpose, fromBlocks_multiply, ha.2,
      ← fromBlocks_one, fromBlocks_smul]

private theorem transport {n k targetN targetK : ℕ} (hn : n = targetN) (hk : k = targetK)
    (h : ∃ W, IsWeighingMatrix (n := n) k W) : ∃ W, IsWeighingMatrix (n := targetN) targetK W := by
  subst targetN targetK
  exact h

theorem main : H1 → H2 → type_of% @WeighingMatrix.weighing_matrix_conjecture := by
  intro oddOrder oddWeight m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro w hm hw
    by_cases hz : w = 0
    · subst w
      exact ⟨0, isWeighingMatrix_zero _⟩
    by_cases sparse : w ≤ 4 * (m / 2)
    · obtain ⟨A, hA⟩ := ih (m / 2) (by omega) w (by omega) sparse
      obtain ⟨B, hB⟩ := ih (m - m / 2) (by omega) w (by omega) (by omega)
      exact transport (by omega) rfl (addOrders hA hB)
    by_cases ho : m % 2 = 1
    · exact oddOrder m w ho (by omega) hw
    by_cases hwo : w % 2 = 1
    · exact oddWeight m w (by omega) hwo (by omega) hw
    obtain ⟨A, hA⟩ := ih (m / 2) (by omega) (w / 2) (by omega) (by omega)
    have hn : 4 * m = 4 * (m / 2) + 4 * (m / 2) := by omega
    have hk : w = w / 2 + w / 2 := by omega
    exact transport hn.symm hk.symm (doubleWeight hA)

end OMA.R_WeighingMatrix_weighing_matrix_conjecture_R1
