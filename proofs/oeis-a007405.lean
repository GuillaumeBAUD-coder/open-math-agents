import OMAStatements.S_oeis_a007405

-- Problem: OEIS A007405
-- Upstream: formal-conjectures statements/oeis-a007405.lean:0 (declaration OMA.S_oeis_a007405.main)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Irwin's determinant formula for the Dowling numbers.  The statement file records that this was
proved by Sela Fried (arXiv 2606.09913, Theorem 2); what follows is a formal proof of that known
result, by a route worked out for this file.

Sketch.  Reversing rows and columns and transposing turns the matrix into
`T p q = C(p, q)` for `q ≤ p`, `-1` for `q = p + 1`, `1` for `q > p + 1`, which does not depend
on the size.  Subtracting from every row the row above leaves the first column equal to
`(1, 0, ..., 0)` and, after deleting the first row and column, the lower Hessenberg matrix
`h p q = C(p, q)` for `q < p`, `2` for `q = p`, `-2` for `q = p + 1`, `0` beyond.
The recurrence of the Dowling numbers says exactly that the vector `w q = 2 ^ (m - q) * a q`
is sent by the `(m + 1)`-square matrix `h` to `(0, ..., 0, a (m + 1))`.  Replacing the first
column by that image multiplies the determinant by `w 0 = 2 ^ m` (Cramer), and the new
determinant is `(-1) ^ m * a (m + 1)` times a triangular determinant equal to `(-2) ^ m`.
-/

namespace OMA007405

open Matrix Finset
open OMA.S_oeis_a007405

/-- The Hessenberg array. -/
def h (p q : ℕ) : ℤ :=
  if q < p then (p.choose q : ℤ) else if q = p then 2 else if q = p + 1 then -2 else 0

/-- Its leading principal submatrices. -/
def H (m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun p q => h p.val q.val

theorem a_zero : a 0 = 1 := by
  rw [a]

theorem a_succ (m : ℕ) :
    a (m + 1) = a m + ∑ k ∈ range (m + 1), (m.choose k : ℤ) * 2 ^ k * a (m - k) := by
  rw [a, Fin.sum_univ_eq_sum_range (fun k => (m.choose k : ℤ) * 2 ^ k * a (m - k)) (m + 1)]

theorem rowsum (p : ℕ) : ∑ q ∈ range (p + 1), h p q * 2 ^ (p - q) * a q = a (p + 1) := by
  have e2 : ∑ k ∈ range (p + 1), (p.choose k : ℤ) * 2 ^ k * a (p - k) =
      ∑ q ∈ range (p + 1), (p.choose q : ℤ) * 2 ^ (p - q) * a q := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q ≤ p := by
      have := Finset.mem_range.mp hq
      omega
    have h1 : p + 1 - 1 - q = p - q := by omega
    have h2 : p - (p - q) = q := by omega
    rw [h1, h2, Nat.choose_symm hq']
  have e1 : ∑ q ∈ range p, h p q * 2 ^ (p - q) * a q =
      ∑ q ∈ range p, (p.choose q : ℤ) * 2 ^ (p - q) * a q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [h, if_pos (Finset.mem_range.mp hq)]
  have hpp : h p p = 2 := by
    unfold h
    rw [if_neg (lt_irrefl p), if_pos rfl]
  rw [a_succ, e2, Finset.sum_range_succ, Finset.sum_range_succ, e1, hpp, Nat.sub_self, pow_zero,
    Nat.choose_self]
  push_cast
  ring

theorem mulVec_row (m p : ℕ) (hp : p ≤ m) :
    ∑ q ∈ range (m + 1), h p q * (2 ^ (m - q) * a q) = if p = m then a (m + 1) else 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, m = p + d := ⟨m - p, by omega⟩
  have hsplit : p + d + 1 = (p + 1) + d := by ring
  rw [hsplit, Finset.sum_range_add]
  have e1 : ∑ q ∈ range (p + 1), h p q * (2 ^ (p + d - q) * a q) = 2 ^ d * a (p + 1) := by
    rw [← rowsum p, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q ≤ p := by
      have := Finset.mem_range.mp hq
      omega
    have h1 : p + d - q = d + (p - q) := by omega
    rw [h1, pow_add]
    ring
  rw [e1]
  cases d with
  | zero => simp
  | succ e =>
    rw [Finset.sum_eq_single 0]
    · have h1 : h p (p + 1 + 0) = -2 := by
        unfold h
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      have h2 : p + (e + 1) - (p + 1 + 0) = e := by omega
      rw [h1, h2, if_neg (by omega), pow_succ]
      simp only [add_zero]
      ring
    · intro x _ hx
      have h0 : h p (p + 1 + x) = 0 := by
        unfold h
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [h0, zero_mul]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos e)) h0

theorem det_H (m : ℕ) : (H m).det = a m := by
  cases m with
  | zero => simp [a_zero]
  | succ m =>
    obtain ⟨A, hA⟩ : ∃ A, A = H (m + 1) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : Fin (m + 1) → ℤ, w = fun q => 2 ^ (m - q.val) * a q.val := ⟨_, rfl⟩
    have hmul : A *ᵥ w = fun p => if p = Fin.last m then a (m + 1) else 0 := by
      funext p
      have hp : p.val ≤ m := by
        have := p.isLt
        omega
      have hsum : (A *ᵥ w) p = ∑ q ∈ range (m + 1), h p.val q * (2 ^ (m - q) * a q) := by
        rw [← Fin.sum_univ_eq_sum_range (fun q => h p.val q * (2 ^ (m - q) * a q)) (m + 1)]
        simp [Matrix.mulVec, dotProduct, hA, hw, H]
      rw [hsum, mulVec_row m p.val hp]
      by_cases hpl : p = Fin.last m
      · rw [if_pos hpl, if_pos (by rw [hpl]; rfl)]
      · rw [if_neg hpl, if_neg (fun h' => hpl (Fin.ext (by simpa using h')))]
    have hcr : (A.updateCol 0 (A *ᵥ w)).det = A.det * w 0 := by
      have h1 : A.cramer (A *ᵥ w) = A.det • w := by
        rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
          Matrix.smul_mulVec, Matrix.one_mulVec]
      have h2 := congrFun h1 0
      rw [Matrix.cramer_apply] at h2
      simpa using h2
    have hw0 : w 0 = 2 ^ m := by
      rw [hw]
      simp [a_zero]
    have hexp : (A.updateCol 0 (A *ᵥ w)).det =
        (-1) ^ m * a (m + 1) * (A.submatrix Fin.castSucc Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (Fin.last m)]
      · have hsub : (A.updateCol 0 (A *ᵥ w)).submatrix (Fin.last m).succAbove Fin.succ =
            A.submatrix Fin.castSucc Fin.succ := by
          ext i j
          simp [Fin.succ_ne_zero]
        rw [hsub]
        simp [hmul]
      · intro i _ hi
        have hz : (A.updateCol 0 (A *ᵥ w)) i 0 = 0 := by
          simp [hmul, hi]
        rw [hz]
        ring
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    have htri : (A.submatrix Fin.castSucc Fin.succ).det = (-2) ^ m := by
      have hLT : (A.submatrix Fin.castSucc Fin.succ).BlockTriangular OrderDual.toDual := by
        intro i j hij
        have hij' : i.val < j.val := hij
        show A (Fin.castSucc i) (Fin.succ j) = 0
        rw [hA]
        show h (Fin.castSucc i).val (Fin.succ j).val = 0
        simp only [Fin.val_castSucc, Fin.val_succ]
        unfold h
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [Matrix.det_of_lowerTriangular _ hLT]
      have hdiag : ∀ i : Fin m, (A.submatrix Fin.castSucc Fin.succ) i i = -2 := by
        intro i
        show A (Fin.castSucc i) (Fin.succ i) = -2
        rw [hA]
        show h (Fin.castSucc i).val (Fin.succ i).val = -2
        simp only [Fin.val_castSucc, Fin.val_succ]
        unfold h
        rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      have hdiag' : ∀ i : Fin m, A i.castSucc i.succ = -2 := hdiag
      simp [hdiag']
    rw [hcr, hw0, htri] at hexp
    have hfin : A.det * 2 ^ m = a (m + 1) * 2 ^ m := by
      rw [hexp]
      have hs : ((-1 : ℤ)) ^ m * (-2) ^ m = 2 ^ m := by
        rw [← mul_pow]
        norm_num
      calc (-1 : ℤ) ^ m * a (m + 1) * (-2) ^ m = a (m + 1) * ((-1) ^ m * (-2) ^ m) := by ring
        _ = a (m + 1) * 2 ^ m := by rw [hs]
    rw [← hA]
    exact mul_right_cancel₀ (pow_ne_zero m (by norm_num)) hfin

/-- The matrix after reversing rows and columns and transposing. -/
def t (p q : ℕ) : ℤ :=
  if q ≤ p then (p.choose q : ℤ) else if q = p + 1 then -1 else 1

def T (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ := fun p q => t p.val q.val

/-- The matrix after subtracting from each row the row above. -/
def U (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun p q => if p.val = 0 then t 0 q.val else t p.val q.val - t (p.val - 1) q.val

theorem det_T_eq_det_U (k : ℕ) : (T k).det = (U k).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
  · intro j
    simp [T, U]
  · intro i j
    simp [T, U]

theorem U_sub (k : ℕ) : (U k).submatrix Fin.succ Fin.succ = H k := by
  ext s q
  show (if (Fin.succ s).val = 0 then t 0 (Fin.succ q).val
    else t (Fin.succ s).val (Fin.succ q).val - t ((Fin.succ s).val - 1) (Fin.succ q).val) =
      h s.val q.val
  simp only [Fin.val_succ]
  rw [if_neg (by omega)]
  have e : s.val + 1 - 1 = s.val := by omega
  rw [e]
  unfold t h
  by_cases h1 : q.val < s.val
  · rw [if_pos (by omega), if_pos (by omega), if_pos h1, Nat.choose_succ_succ]
    push_cast
    ring
  · by_cases h2 : q.val = s.val
    · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg h1, if_pos h2, h2,
        Nat.choose_self]
      norm_num
    · by_cases h3 : q.val = s.val + 1
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
          if_neg h1, if_neg h2, if_pos h3]
        norm_num
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg h1, if_neg h2, if_neg h3]
        norm_num

theorem det_U (k : ℕ) : (U k).det = (H k).det := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · have h00 : (U k) 0 0 = 1 := by
      simp [U, t]
    rw [h00, Fin.succAbove_zero, U_sub]
    simp
  · intro i _ hi
    have hi' : i.val ≠ 0 := fun h0 => hi (Fin.ext h0)
    have hz : (U k) i 0 = 0 := by
      show (if i.val = 0 then t 0 (0 : Fin (k + 1)).val
        else t i.val (0 : Fin (k + 1)).val - t (i.val - 1) (0 : Fin (k + 1)).val) = 0
      rw [if_neg hi']
      simp [t]
    rw [hz]
    ring
  · intro h0
    exact absurd (Finset.mem_univ _) h0

theorem binomialMatrix_eq (k : ℕ) :
    binomialMatrix (k + 1) = ((T k).transpose).submatrix Fin.revPerm Fin.revPerm := by
  ext i j
  show (if i.val + 1 < j.val then (1 : ℤ) else if i.val + 1 = j.val then -1 else
    ((k + 1 - 1 - j.val).choose (i.val - j.val) : ℤ)) = t (Fin.rev j).val (Fin.rev i).val
  have hi := i.isLt
  have hj := j.isLt
  have ri : (Fin.rev i).val = k - i.val := by
    rw [Fin.val_rev]
    omega
  have rj : (Fin.rev j).val = k - j.val := by
    rw [Fin.val_rev]
    omega
  rw [ri, rj]
  unfold t
  by_cases h1 : i.val + 1 < j.val
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
  · by_cases h2 : i.val + 1 = j.val
    · rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1, if_neg h2, if_pos (by omega)]
      have e1 : k + 1 - 1 - j.val = k - j.val := by omega
      have e2 : k - i.val = (k - j.val) - (i.val - j.val) := by omega
      rw [e1, e2, Nat.choose_symm (by omega)]

theorem det_binomialMatrix (k : ℕ) : (binomialMatrix (k + 1)).det = a k := by
  rw [binomialMatrix_eq, Matrix.det_submatrix_equiv_self, Matrix.det_transpose, det_T_eq_det_U,
    det_U, det_H]

end OMA007405

theorem OMA.solution : type_of% @OMA.S_oeis_a007405.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [OMA007405.det_binomialMatrix]
  rfl
