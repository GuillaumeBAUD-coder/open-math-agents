import OMAStatements.S_oeis_a085799
import Mathlib

namespace A085799

open OMA.S_oeis_a085799

/-- The matrix entry as a function of natural-number indices. -/
def SD (i j : ℕ) : ℚ := |((i:ℚ) + 1) ^ 2 - ((j:ℚ) + 1) ^ 2|

lemma SD_le (i j : ℕ) (h : i ≤ j) : SD i j = ((j:ℚ) + 1) ^ 2 - ((i:ℚ) + 1) ^ 2 := by
  have h' : (i:ℚ) ≤ j := by exact_mod_cast h
  have hi : (0:ℚ) ≤ i := Nat.cast_nonneg i
  unfold SD
  rw [abs_of_nonpos (by nlinarith)]
  ring

lemma SD_ge (i j : ℕ) (h : j ≤ i) : SD i j = ((i:ℚ) + 1) ^ 2 - ((j:ℚ) + 1) ^ 2 := by
  have h' : (j:ℚ) ≤ i := by exact_mod_cast h
  have hj : (0:ℚ) ≤ j := Nat.cast_nonneg j
  unfold SD
  rw [abs_of_nonneg (by nlinarith)]

lemma sq_apply (n : ℕ) (i j : Fin n) : squareDistance n i j = SD i.val j.val := rfl

def F1 (i j : ℕ) : ℚ :=
  if i = 0 then ((j:ℚ) + 1) ^ 2 - 1 else if j < i then 2 * (i:ℚ) + 1 else -(2 * (i:ℚ) + 1)

def F2 (i j : ℕ) : ℚ :=
  if i = 0 then ((j:ℚ) + 1) ^ 2 - 1 else if j < i then 1 else -1

def F3 (i j : ℕ) : ℚ :=
  if i = 0 then ((j:ℚ) + 1) ^ 2 - 1 else
    if i = 1 then (if j < 1 then 1 else -1) else if j + 1 = i then 2 else 0

def F4 (i j : ℕ) : ℚ :=
  if i = 0 then ((j:ℚ) + 1) ^ 2 - 1 else
    if i = 1 then (if j = 0 then 1 else 0) else if j + 1 = i then 2 else 0

def V (i : ℕ) : ℚ := if i = 0 then 1 else 2 * (i:ℚ) + 1

lemma step1 (p : ℕ) :
    (squareDistance (p+2)).det = (Matrix.of fun i j : Fin (p+2) => F1 i.val j.val).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
  · intro j
    rw [sq_apply, Matrix.of_apply, SD_le _ _ (by simp)]
    simp only [Fin.val_zero]
    unfold F1
    rw [if_pos rfl]
    push_cast
    ring
  · intro i j
    rw [sq_apply, sq_apply, Matrix.of_apply]
    simp only [Fin.val_succ, Fin.val_castSucc]
    unfold F1
    rw [if_neg (by omega)]
    by_cases h : j.val < i.val + 1
    · rw [if_pos h, SD_ge _ _ (by omega), SD_ge _ _ (by omega)]
      push_cast
      ring
    · rw [if_neg h, SD_le _ _ (by omega), SD_le _ _ (by omega)]
      push_cast
      ring

lemma step2 (p : ℕ) :
    (Matrix.of fun i j : Fin (p+2) => F1 i.val j.val).det =
      (∏ i : Fin (p+2), V i.val) * (Matrix.of fun i j : Fin (p+2) => F2 i.val j.val).det := by
  rw [← Matrix.det_mul_column]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  unfold F1 F2 V
  split_ifs <;> ring

lemma step3 (p : ℕ) :
    (Matrix.of fun i j : Fin (p+2) => F2 i.val j.val).det =
      (Matrix.of fun i j : Fin (p+2) => F3 i.val j.val).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred
    (fun i : Fin (p+1) => if i.val = 0 then 0 else 1)
  · intro j
    simp only [Matrix.of_apply, Fin.val_zero]
    unfold F2 F3
    rw [if_pos rfl, if_pos rfl]
  · intro i j
    simp only [Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
    unfold F2 F3
    split_ifs <;> first | (exfalso; omega) | ring1

lemma step4 (p : ℕ) :
    (Matrix.of fun i j : Fin (p+2) => F3 i.val j.val).det =
      (Matrix.of fun i j : Fin (p+2) => F4 i.val j.val).det := by
  rw [← Matrix.det_transpose (Matrix.of fun i j : Fin (p+2) => F3 i.val j.val),
    ← Matrix.det_transpose (Matrix.of fun i j : Fin (p+2) => F4 i.val j.val)]
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (fun j : Fin (p+2) => if j.val = 0 then 0 else -1) 0
  · simp
  · intro j i
    simp only [Matrix.transpose_apply, Matrix.of_apply, Fin.val_zero]
    unfold F3 F4
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring1)

lemma rot_val (p : ℕ) (i : Fin (p+2)) :
    ((finRotate (p+2)) i).val = if i.val = p + 1 then 0 else i.val + 1 := by
  rw [coe_finRotate]
  by_cases h : i = Fin.last (p+1)
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · have h' : i.val ≠ p + 1 := fun hh => h (Fin.ext hh)
    rw [if_neg h, if_neg h']

lemma step5 (p : ℕ) :
    (Matrix.of fun i j : Fin (p+2) => F4 i.val j.val).det =
      (-1 : ℚ) ^ (p + 1) * ((2:ℚ) ^ p * (((p:ℚ) + 2) ^ 2 - 1)) := by
  have hperm := Matrix.det_permute (finRotate (p+2))
    (Matrix.of fun i j : Fin (p+2) => F4 i.val j.val)
  have e : p + 2 - 1 = p + 1 := by omega
  rw [sign_finRotate, e] at hperm
  have htri : ((Matrix.of fun i j : Fin (p+2) => F4 i.val j.val).submatrix
      (finRotate (p+2)) id).IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hj := j.isLt
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    have hs := rot_val p i
    generalize ((finRotate (p+2)) i).val = s at hs
    simp only [id]
    rw [if_neg (by omega)] at hs
    subst hs
    unfold F4
    split_ifs <;> first | (exfalso; omega) | rfl
  have hdet := Matrix.det_of_isLowerTriangular _ htri
  have h0 : ((Matrix.of fun i j : Fin (p+2) => F4 i.val j.val).submatrix
      (finRotate (p+2)) id) 0 0 = 1 := by
    have hr : ((finRotate (p+2)) 0).val = 1 := by
      rw [rot_val]
      simp
    show F4 ((finRotate (p+2)) 0).val (0 : Fin (p+2)).val = 1
    rw [hr]
    show F4 1 0 = 1
    simp [F4]
  have hl : ((Matrix.of fun i j : Fin (p+2) => F4 i.val j.val).submatrix
      (finRotate (p+2)) id) (Fin.last p).succ (Fin.last p).succ = ((p:ℚ) + 2) ^ 2 - 1 := by
    have hr : ((finRotate (p+2)) (Fin.last p).succ).val = 0 := by
      rw [rot_val]
      simp
    show F4 ((finRotate (p+2)) (Fin.last p).succ).val (Fin.last p).succ.val = ((p:ℚ) + 2) ^ 2 - 1
    rw [hr]
    show F4 0 (p + 1) = ((p:ℚ) + 2) ^ 2 - 1
    unfold F4
    rw [if_pos rfl]
    push_cast
    ring
  have hm : ∀ i : Fin p, ((Matrix.of fun i j : Fin (p+2) => F4 i.val j.val).submatrix
      (finRotate (p+2)) id) i.castSucc.succ i.castSucc.succ = 2 := by
    intro i
    have hi := i.isLt
    show F4 ((finRotate (p+2)) i.castSucc.succ).val i.castSucc.succ.val = 2
    rw [rot_val]
    simp only [Fin.val_succ, Fin.val_castSucc]
    rw [if_neg (show ¬ (i.val + 1 = p + 1) by omega)]
    unfold F4
    rw [if_neg (show ¬ (i.val + 1 + 1 = 0) by omega),
      if_neg (show ¬ (i.val + 1 + 1 = 1) by omega), if_pos rfl]
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc, h0, hl,
    Finset.prod_congr rfl (fun i _ => hm i)] at hdet
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul] at hdet
  rw [hdet] at hperm
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg,
    Int.cast_one] at hperm
  have hs : ((-1:ℚ) ^ (p + 1)) * ((-1:ℚ) ^ (p + 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  linear_combination
    (-((Matrix.of fun i j : Fin (p+2) => F4 i.val j.val).det)) * hs - ((-1:ℚ) ^ (p + 1)) * hperm

lemma prodV (p : ℕ) :
    (∏ i : Fin (p+2), V i.val) * (2:ℚ) ^ (p + 1) * ((p + 1).factorial : ℚ) =
      ((2 * p + 3).factorial : ℚ) := by
  induction p with
  | zero =>
    rw [Fin.prod_univ_two]
    simp [V, Nat.factorial]
    norm_num
  | succ p ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hV : V (p + 1 + 1) = 2 * ((p:ℚ) + 2) + 1 := by
      unfold V
      rw [if_neg (by omega)]
      push_cast
      ring
    have hf : ((2 * (p + 1) + 3).factorial : ℚ) =
        (2 * (p:ℚ) + 5) * (2 * (p:ℚ) + 4) * (2 * p + 3).factorial := by
      rw [show 2 * (p + 1) + 3 = (2 * p + 3) + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      ring
    have hg : ((p + 1 + 1).factorial : ℚ) = ((p:ℚ) + 2) * (p + 1).factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hV, hf, hg, ← ih]
    ring

lemma det_main (p : ℕ) :
    (squareDistance (p+2)).det =
      (-1:ℚ) ^ (p + 1) * (((p:ℚ) + 3) / 2) * ((2 * p + 3).factorial : ℚ) / (p.factorial : ℚ) := by
  rw [step1, step2, step3, step4, step5]
  have h := prodV p
  have hf : ((p + 1).factorial : ℚ) = ((p:ℚ) + 1) * p.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hp : (p.factorial : ℚ) ≠ 0 := by positivity
  rw [← h, hf]
  field_simp
  ring

lemma permCount (m r : ℕ) : permutationCount m r = m.descFactorial r := by
  unfold permutationCount
  rw [Fintype.card_embedding_eq]
  simp

end A085799

theorem OMA.solution : type_of% @OMA.S_oeis_a085799.main := by
  constructor
  · intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    unfold OMA.S_oeis_a085799.a
    rw [A085799.det_main]
    have e1 : p + 2 - 1 = p + 1 := by omega
    have e2 : 2 * (p + 2) - 1 = 2 * p + 3 := by omega
    have e3 : p + 2 - 2 = p := by omega
    rw [e1, e2, e3]
    push_cast
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rcases m with _ | p
    · have h0 : OMA.S_oeis_a085799.a (0 + 1) = 0 := by
        unfold OMA.S_oeis_a085799.a
        rw [Matrix.det_fin_one]
        simp [OMA.S_oeis_a085799.squareDistance]
      have h1 : (2 * (0 + 1) - 1).descFactorial (0 + 1 + 1) = 0 := by decide
      rw [h0, A085799.permCount, h1]
      simp
    · unfold OMA.S_oeis_a085799.a
      rw [A085799.det_main, A085799.permCount]
      have e2 : 2 * (p + 1 + 1) - 1 = 2 * p + 3 := by omega
      have e3 : p + 1 + 1 + 1 = p + 3 := by omega
      rw [e2, e3]
      have hp : (p.factorial : ℚ) ≠ 0 := by positivity
      have hdF : ((2 * p + 3).descFactorial (p + 3) : ℚ) =
          ((2 * p + 3).factorial : ℚ) / (p.factorial : ℚ) := by
        have h := Nat.factorial_mul_descFactorial (show p + 3 ≤ 2 * p + 3 by omega)
        have e : 2 * p + 3 - (p + 3) = p := by omega
        rw [e] at h
        have h' : (p.factorial : ℚ) * ((2 * p + 3).descFactorial (p + 3) : ℚ) =
            ((2 * p + 3).factorial : ℚ) := by exact_mod_cast h
        rw [eq_div_iff hp]
        linarith
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hdF]
      have e4 : (-1:ℚ) ^ (p + 1) * (((p:ℚ) + 3) / 2) * ((2 * p + 3).factorial : ℚ) /
          (p.factorial : ℚ) = (-1:ℚ) ^ (p + 1) *
            ((((p:ℚ) + 3) / 2) * ((2 * p + 3).factorial : ℚ) / (p.factorial : ℚ)) := by ring
      rw [e4, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]
      push_cast
      ring
