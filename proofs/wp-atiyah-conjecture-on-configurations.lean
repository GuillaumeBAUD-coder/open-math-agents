import OMAStatements.S_wp_atiyah_conjecture_on_configurations
import Mathlib

-- Problem: Atiyah conjecture on configurations.
-- A planar specialization of Jan Eickhoff's singular configuration construction.
namespace AC
open Polynomial Matrix OMA.S_wp_atiyah_conjecture_on_configurations
abbrev Ix := Fin 80 ⊕ (Fin 2 ⊕ Fin 32)
def idx : Ix ≃ Fin 114 := (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
@[simp] lemma idxL (i : Fin 80) : (idx (.inl i)).val = i.val := rfl
@[simp] lemma idxM (i : Fin 2) : (idx (.inr (.inl i))).val = 80+i.val := rfl
@[simp] lemma idxU (i : Fin 32) : (idx (.inr (.inr i))).val = 82+i.val := by change 80+(2+i.val)=_; omega
abbrev a : ℚ := 1/100
abbrev x : ℚ := 1/3
abbrev y : ℚ := 1/2
abbrev z : ℚ := 99/101

-- Exact coefficient lists at the coalescing endpoint.
def scan (c d p : ℚ) : List ℚ → List ℚ
  | [] => [p]
  | h :: l => (c*h+p) :: scan c d (d*h) l

def coeffA : List ℚ := scan 1 (-1) 0 (Nat.iterate (scan 1 y 0) 32 (Nat.iterate (scan a 1 0) 80 [1]))
def coeffB : List ℚ := scan 1 1 0 (Nat.iterate (scan 1 z 0) 32 (Nat.iterate (scan x 1 0) 80 [1]))
def weights (s : ℚ) : List ℚ :=
  Nat.iterate (fun l => ((a + x) * l[0]! - (a * x) * l[1]!) :: l) 80
    ((List.range 34).map (fun k => s ^ k))
def rows : Ix → List ℚ
  | .inl i => List.replicate i.val 0 ++ [1, -(a+x), a*x]
  | .inr (.inl i) => if i = 0 then coeffA else coeffB
  | .inr (.inr i) => List.replicate (80 + i.val) 0 ++ [y*z, -(y+z), 1]
def dot (l : List ℚ) (s : ℚ) : ℚ := ((weights s).zipWith (· * ·) l).sum

def Q : Matrix Ix Ix ℚ := fun i j => (rows i)[(idx j).val]?.getD 0

-- The two new columns annihilate the axial rows and leave a two-by-two block.
def T : Matrix Ix Ix ℚ := fun i j => match j with
  | .inr (.inl k) => (weights (if k = 0 then y else z))[(idx i).val]?.getD 0
  | _ => if i = j then 1 else 0

def E : Matrix Ix Ix ℚ := fun i j => match j with
  | .inr (.inl k) => dot (rows i) (if k = 0 then y else z)
  | _ => Q i j

set_option maxRecDepth 9000 in
set_option maxHeartbeats 4000000 in
lemma cert : dot coeffA y * dot coeffB z < dot coeffA z * dot coeffB y := by decide +kernel

set_option maxRecDepth 9000 in
set_option maxHeartbeats 4000000 in
lemma zerosL : ∀ i : Fin 80, dot (rows (.inl i)) y = 0 ∧ dot (rows (.inl i)) z = 0 := by decide +kernel

set_option maxRecDepth 9000 in
set_option maxHeartbeats 4000000 in
lemma zerosU : ∀ i : Fin 32, dot (rows (.inr (.inr i))) y = 0 ∧ dot (rows (.inr (.inr i))) z = 0 := by decide +kernel

lemma sum_zip (l w : List ℚ) (n : ℕ) (hl : l.length ≤ n) (hw : n ≤ w.length) :
    (w.zipWith (· * ·) l).sum = ∑ j : Fin n, l[j.val]?.getD 0 * w[j.val]?.getD 0 := by
  induction n generalizing l w with
  | zero => have : l = [] := List.length_eq_zero_iff.mp (by omega); simp [this]
  | succ n ih =>
    cases l with
    | nil => simp
    | cons v l =>
      cases w with
      | nil => simp at hw
      | cons u w =>
        rw [Fin.sum_univ_succ]
        simp only [List.zipWith_cons_cons, List.sum_cons, Fin.val_zero, List.getElem?_cons_zero,
          Option.getD_some, Fin.val_succ, List.getElem?_cons_succ]
        rw [ih l w (by simpa using hl) (by simpa using hw), mul_comm u v]

set_option maxRecDepth 7000 in
lemma lens : ∀ i, (rows i).length ≤ 114 := by decide +kernel
set_option maxRecDepth 7000 in
lemma wlen : 114 ≤ (weights y).length ∧ 114 ≤ (weights z).length := by decide +kernel

lemma mult : Q * T = E := by
  ext i j
  rcases j with j | (j | j)
  · simp [Matrix.mul_apply, T, E]
  · change (∑ k : Ix, Q i k * (weights (if j = 0 then y else z))[(idx k).val]?.getD 0) = _
    rw [show E i (.inr (.inl j)) = dot (rows i) (if j = 0 then y else z) from rfl,
      dot, sum_zip _ _ 114 (lens i) (by split; exact wlen.1; exact wlen.2)]
    exact Equiv.sum_comp idx (fun k : Fin 114 => (rows i)[k.val]?.getD 0 * (weights (if j = 0 then y else z))[k.val]?.getD 0)
  · simp [Matrix.mul_apply, T, E]

lemma blocks12 {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix (m ⊕ n) (m ⊕ n) ℚ) (h : ∀ i j, M (.inl i) (.inr j) = 0) :
    M.det = (M.submatrix Sum.inl Sum.inl).det * (M.submatrix Sum.inr Sum.inr).det := by
  have hh : M = fromBlocks (M.submatrix Sum.inl Sum.inl) 0 (M.submatrix Sum.inr Sum.inl) (M.submatrix Sum.inr Sum.inr) := by
    ext (i|i) (j|j) <;> simp [h]
  nth_rw 1 [hh]
  exact det_fromBlocks_zero₁₂ ..

lemma blocks21 {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix (m ⊕ n) (m ⊕ n) ℚ) (h : ∀ i j, M (.inr i) (.inl j) = 0) :
    M.det = (M.submatrix Sum.inl Sum.inl).det * (M.submatrix Sum.inr Sum.inr).det := by
  have hh : M = fromBlocks (M.submatrix Sum.inl Sum.inl) (M.submatrix Sum.inl Sum.inr) 0 (M.submatrix Sum.inr Sum.inr) := by
    ext (i|i) (j|j) <;> simp [h]
  nth_rw 1 [hh]
  exact det_fromBlocks_zero₂₁ ..

set_option maxRecDepth 9000 in
set_option maxHeartbeats 4000000 in
lemma sparse : (∀ (i : Fin 80) (j : Fin 32), Q (.inl i) (.inr (.inr j)) = 0 ∧ Q (.inr (.inr j)) (.inl i) = 0) ∧
    (∀ i j : Fin 80, (j < i → Q (.inl i) (.inl j) = 0) ∧ Q (.inl i) (.inl i) = 1) ∧
    (∀ i j : Fin 32, (i < j → Q (.inr (.inr i)) (.inr (.inr j)) = 0) ∧ Q (.inr (.inr i)) (.inr (.inr i)) = 1) := by
  decide +kernel

set_option maxRecDepth 9000 in
lemma T_pos : 0 < T.det := by
  rw [blocks21 T (by intro i j; simp [T]), blocks12 _ (by intro i j; simp [T, submatrix])]
  have hl : T.submatrix Sum.inl Sum.inl = 1 := by ext i j; simp [T, Matrix.one_apply]
  have hu : (T.submatrix Sum.inr Sum.inr).submatrix Sum.inr Sum.inr = 1 := by ext i j; simp [T, Matrix.one_apply]
  have hm : (T.submatrix Sum.inr Sum.inr).submatrix Sum.inl Sum.inl = !![1, 1; y, z] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  rw [hl, hu, hm, det_one, det_one, one_mul, mul_one, det_fin_two]
  norm_num [y, z]

set_option maxRecDepth 9000 in
lemma E_neg : E.det < 0 := by
  have h₁ : ∀ i j, E (.inl i) (.inr j) = 0 := by
    intro i j
    rcases j with j | j
    · change dot (rows (.inl i)) (if j = 0 then y else z) = 0
      split; exact (zerosL i).1; exact (zerosL i).2
    · exact (sparse.1 i j).1
  rw [blocks12 E h₁, blocks21 _ (by
    intro i j
    change dot (rows (.inr (.inr i))) (if j = 0 then y else z) = 0
    split; exact (zerosU i).1; exact (zerosU i).2)]
  have hl : (E.submatrix Sum.inl Sum.inl).det = 1 := by
    rw [det_of_isUpperTriangular (by intro i j h; exact (sparse.2.1 i j).1 h)]
    exact Finset.prod_eq_one fun i _ => (sparse.2.1 i i).2
  have hu : ((E.submatrix Sum.inr Sum.inr).submatrix Sum.inr Sum.inr).det = 1 := by
    rw [det_of_isLowerTriangular _ (by intro i j h; exact (sparse.2.2 i j).1 h)]
    exact Finset.prod_eq_one fun i _ => (sparse.2.2 i i).2
  rw [hl, hu, one_mul, mul_one, det_fin_two]
  change dot coeffA y * dot coeffB z - dot coeffA z * dot coeffB y < 0
  exact sub_neg.mpr cert

lemma Q_neg : Q.det < 0 := by
  have h := E_neg
  rw [← mult, det_mul] at h
  by_contra! hn
  exact (not_lt_of_ge (mul_nonneg hn T_pos.le)) h

noncomputable def pol : List ℚ → ℚ[X]
  | [] => 0
  | h :: l => C h + X * pol l

lemma pol_scan (c d p : ℚ) (l : List ℚ) :
    pol (scan c d p l) = (C c + C d * X) * pol l + C p := by
  induction l generalizing p with
  | nil => simp [scan, pol]
  | cons h l ih =>
    rw [scan, pol, ih, pol]
    simp only [map_add, map_mul]
    ring

lemma pol_iter (c d : ℚ) (l : List ℚ) (n : ℕ) :
    pol (Nat.iterate (scan c d 0) n l) = (C c + C d * X)^n * pol l := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', pol_scan, ih, pow_succ']; simp [mul_assoc]

lemma polA : pol coeffA = (X + C a)^80 * (1 + C y * X)^32 * (1 - X) := by
  rw [coeffA, pol_scan, pol_iter, pol_iter]
  simp [pol]; ring

lemma polB : pol coeffB = (X + C x)^80 * (1 + C z * X)^32 * (X + 1) := by
  rw [coeffB, pol_scan, pol_iter, pol_iter]
  simp [pol]; ring

lemma pol_repl (n : ℕ) (l : List ℚ) : pol (List.replicate n 0 ++ l) = X^n * pol l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, pol, ih, pow_succ', mul_assoc]

lemma pol_coeff (l : List ℚ) (n : ℕ) : (pol l).coeff n = l[n]?.getD 0 := by
  induction l generalizing n with
  | nil => simp [pol]
  | cons h l ih =>
    cases n with
    | zero => simp [pol]
    | succ n => simp [pol, Polynomial.coeff_X_mul, ih]

-- Interpolate from distinct collinear points to two clusters and two off-axis points.
noncomputable abbrev u : ℝ := 9999/200
noncomputable abbrev v : ℝ := 3/4
noncomputable abbrev R : ℝ := 29997/800
noncomputable def eh : Ix → ℝ
  | .inl _ => 0
  | .inr (.inl _) => u
  | .inr (.inr _) => u+v
noncomputable def ew : Ix → ℝ
  | .inl _ => 0
  | .inr (.inl i) => if i = 0 then 1 else R
  | .inr (.inr _) => 0
noncomputable def ht (t : ℝ) (i : Ix) : ℝ := (1-t)*(idx i).val + t*eh i
noncomputable def ho (t : ℝ) (i : Ix) : ℝ := t*ew i

lemma eh_le {i j : Ix} (h : idx i < idx j) : eh i ≤ eh j := by
  change (idx i).val < (idx j).val at h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp only [idxL, idxM, idxU] at h
  all_goals first | omega | norm_num [eh, u, v]

lemma ht_lt {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) {i j : Ix} (h : idx i < idx j) : ht t i < ht t j := by
  have hc : ((idx i).val : ℝ) < (idx j).val := by exact_mod_cast (show (idx i).val < (idx j).val from h)
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hc (sub_pos.mpr h1))
    (mul_le_mul_of_nonneg_left (eh_le h) h0)

noncomputable def slope (w d : ℝ) := w / (d + Real.sqrt (w^2 + d^2))
noncomputable def sl (t : ℝ) (i j : Ix) := slope (ho t j - ho t i) (ht t j - ht t i)

lemma sl_cont (i j : Ix) (h : idx i < idx j) : ContinuousOn (fun t => sl t i j) (Set.Icc 0 1) := by
  by_cases H : ew j = ew i
  · have he : (fun t => sl t i j) = fun _ => 0 := by funext t; simp [sl, slope, ho, H]
    rw [he]; exact continuousOn_const
  unfold sl slope
  refine (by unfold ho; fun_prop : Continuous (fun t => ho t j - ho t i)).continuousOn.div
    (by unfold ht ho; fun_prop : Continuous (fun t => ht t j - ht t i + Real.sqrt ((ho t j-ho t i)^2+(ht t j-ht t i)^2))).continuousOn ?_
  intro t htmem
  by_cases h1 : t = 1
  · subst t
    have hd : 0 ≤ ht 1 j - ht 1 i := by simpa [ht] using sub_nonneg.mpr (eh_le h)
    have hw : ho 1 j - ho 1 i ≠ 0 := by simpa [ho] using sub_ne_zero.mpr H
    exact ne_of_gt (add_pos_of_nonneg_of_pos hd (Real.sqrt_pos_of_pos
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hw) (sq_nonneg _))))
  have hd : 0 < ht t j - ht t i := sub_pos.mpr (ht_lt htmem.1 (lt_of_le_of_ne htmem.2 h1) h)
  exact ne_of_gt (add_pos_of_pos_of_nonneg hd (Real.sqrt_nonneg _))

noncomputable def fac (t : ℝ) (i j : Ix) : ℝ[X] :=
  if i = j then 1 else if (idx i).val < (idx j).val then 1 - C (sl t i j) * X else X + C (sl t j i)
noncomputable def rp (t : ℝ) (i : Ix) : ℝ[X] := ∏ j : Ix, fac t i j
noncomputable def M (t : ℝ) : Matrix Ix Ix ℝ := fun i j => (rp t i).coeff (idx j).val

lemma coeff_cont_prod {J : Type} (s : Finset J) (f : ℝ → J → ℝ[X])
    (hf : ∀ j k, ContinuousOn (fun t => (f t j).coeff k) (Set.Icc 0 1)) (k : ℕ) :
    ContinuousOn (fun t => (∏ j ∈ s, f t j).coeff k) (Set.Icc 0 1) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simp; exact continuousOn_const
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj, Polynomial.coeff_mul]
    exact continuousOn_finsetSum _ (fun q _ => (hf j q.1).mul (ih q.2))

lemma contM : ContinuousOn (fun t => (M t).det) (Set.Icc 0 1) := by
  apply (Continuous.matrix_det continuous_id : Continuous (fun m : Matrix Ix Ix ℝ => m.det)).comp_continuousOn
  refine continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j => ?_))
  change ContinuousOn (fun t => (∏ l : Ix, fac t i l).coeff (idx j).val) (Set.Icc 0 1)
  apply coeff_cont_prod
  intro l k
  unfold fac
  split
  · exact continuousOn_const
  split
  · rename_i hh
    simp only [coeff_sub, coeff_C_mul]
    exact continuousOn_const.sub ((sl_cont _ _ hh).mul continuousOn_const)
  · rename_i hne hn
    have hh : idx l < idx i := show (idx l).val < (idx i).val by
      have he : (idx l).val ≠ (idx i).val := fun e => hne ((idx.injective (Fin.ext e)).symm)
      omega
    simp only [coeff_add, coeff_C]
    split
    · exact continuousOn_const.add (sl_cont _ _ hh)
    · exact continuousOn_const

lemma prodAx {n : ℕ} (i : Fin n) : (∏ j : Fin n, if j.val < i.val then (X : ℝ[X]) else 1) = X^i.val := by
  simp only [Finset.prod_ite, Finset.prod_const, Fin.card_filter_val_lt,
    Nat.min_eq_right (Nat.le_of_lt i.isLt), one_pow, mul_one]

lemma rp0 (i : Ix) : rp 0 i = X ^ (idx i).val := by
  have hf (j : Ix) : fac 0 i j = if (idx j).val < (idx i).val then X else 1 := by
    have hs (k l : Ix) : sl 0 k l = 0 := by simp [sl, ho, slope]
    rw [fac, hs, hs]
    by_cases hij : i = j
    · subst j; simp
    · have hne : (idx i).val ≠ (idx j).val := fun e => hij (idx.injective (Fin.ext e))
      by_cases hh : (idx i).val < (idx j).val
      · simp [hij, hh, Nat.not_lt_of_ge hh.le]
      · have h' : (idx j).val < (idx i).val := by omega
        simp [hij, hh, h']
  simp only [rp, hf]
  rw [← Equiv.prod_comp idx.symm (fun j : Ix => if (idx j).val < (idx i).val then (X : ℝ[X]) else 1)]
  simpa only [Equiv.apply_symm_apply] using prodAx (idx i)

lemma M0 : M 0 = 1 := by
  ext i j
  simp [M, rp0, coeff_X_pow, Matrix.one_apply, Fin.val_inj, idx.injective.eq_iff, eq_comm]

lemma sl1 (i j : Ix) : sl 1 i j = slope (ew j - ew i) (eh j - eh i) := by simp [sl, ho, ht]

lemma slope_rat (w d r : ℝ) (h : w^2+d^2=r^2) (hr : 0 ≤ r) : slope w d = w / (d+r) := by
  simp [slope,h,Real.sqrt_sq hr]

@[simp] lemma sLAB (i : Fin 80) (k : Fin 2) : sl 1 (.inl i) (.inr (.inl k)) = if k = 0 then 1/100 else 1/3 := by
  fin_cases k
  · have h : slope 1 u = 1/100 := by rw [slope_rat _ _ (10001/200) (by norm_num [u]) (by norm_num)]; norm_num [u]
    simpa [sl1, ew, eh] using h
  · have h : slope R u = 1/3 := by rw [slope_rat _ _ (49995/800) (by norm_num [u,R]) (by norm_num)]; norm_num [u,R]
    simpa [sl1, ew, eh] using h

@[simp] lemma sABU (k : Fin 2) (j : Fin 32) : sl 1 (.inr (.inl k)) (.inr (.inr j)) = if k = 0 then -(1/2) else -(99/101) := by
  fin_cases k
  · have h : slope (-1) v = -(1/2) := by rw [slope_rat _ _ (5/4) (by norm_num [v]) (by norm_num)]; norm_num [v]
    simpa [sl1, ew, eh] using h
  · have h : slope (-R) v = -(99/101) := by rw [slope_rat _ _ (30003/800) (by norm_num [v,R]) (by norm_num)]; norm_num [v,R]
    simpa [sl1, ew, eh] using h

@[simp] lemma sAB : sl 1 (.inr (.inl 0)) (.inr (.inl 1)) = 1 := by
  have hp : 0 ≤ R - 1 := by norm_num [R]
  have hn : R - 1 ≠ 0 := by norm_num [R]
  simpa [sl1, ew, eh, slope, Real.sqrt_sq hp] using div_self hn

lemma rp1L (i : Fin 80) : rp 1 (.inl i) = X^i.val * (1-C (1/100) * X) * (1-C (1/3)*X) := by
  have hL (j : Fin 80) : fac 1 (.inl i) (.inl j) = if j.val < i.val then X else 1 := by
    simp only [fac, idxL, Sum.inl.injEq, sl1, ew, sub_self, slope, zero_div, map_zero, zero_mul, sub_zero, add_zero]
    split <;> rename_i h
    · subst j; simp
    · have : i.val ≠ j.val := fun e => h (Fin.ext e)
      split <;> simp_all [show j.val < i.val ↔ ¬ i.val < j.val by omega]
  have hM (j : Fin 2) : fac 1 (.inl i) (.inr (.inl j)) = 1 - C (if j = 0 then 1/100 else 1/3) * X := by
    have h : i.val < 80 + j.val := by omega
    simp [fac, h]
  have hU (j : Fin 32) : fac 1 (.inl i) (.inr (.inr j)) = 1 := by
    have h : i.val < 82 + j.val := by omega
    simp [fac, h, sl1, ew, slope]
  simp only [rp, Fintype.prod_sum_type, hL, hM, hU, prodAx, Finset.prod_const_one, mul_one, Fin.prod_univ_two]
  simp [mul_assoc]

lemma rp1U (i : Fin 32) : rp 1 (.inr (.inr i)) = X^(80+i.val) * (X-C (1/2)) * (X-C (99/101)) := by
  have hL (j : Fin 80) : fac 1 (.inr (.inr i)) (.inl j) = X := by
    have h : ¬ 82+i.val < j.val := by omega
    simp [fac, h, sl1, ew, slope]
  have hM (j : Fin 2) : fac 1 (.inr (.inr i)) (.inr (.inl j)) = X + C (if j = 0 then -(1/2) else -(99/101)) := by
    have h : ¬ 82+i.val < 80+j.val := by omega
    simp [fac, h]
  have hU (j : Fin 32) : fac 1 (.inr (.inr i)) (.inr (.inr j)) = if j.val < i.val then X else 1 := by
    simp only [fac, idxU, Sum.inr.injEq, sl1, ew, sub_self, slope, zero_div, map_zero, zero_mul, sub_zero, add_zero]
    split <;> rename_i h
    · subst j; simp
    · have : i.val ≠ j.val := fun e => h (Fin.ext e)
      split <;> simp_all [show j.val < i.val ↔ ¬ 82+i.val < 82+j.val by omega]
  simp only [rp, Fintype.prod_sum_type, hL, hM, hU, prodAx, Finset.prod_const, Fin.prod_univ_two]
  simp [pow_add, sub_eq_add_neg]
  ring

lemma rp1M (i : Fin 2) : rp 1 (.inr (.inl i)) = if i = 0 then
    (X+C (1/100))^80 * (1+C (1/2)*X)^32 * (1-X) else
    (X+C (1/3))^80 * (1+C (99/101)*X)^32 * (X+1) := by
  have hL (j : Fin 80) : fac 1 (.inr (.inl i)) (.inl j) = X + C (if i = 0 then 1/100 else 1/3) := by
    have h : ¬ 80+i.val < j.val := by omega
    simp [fac, h]
  have hU (j : Fin 32) : fac 1 (.inr (.inl i)) (.inr (.inr j)) = 1 - C (if i = 0 then -(1/2) else -(99/101)) * X := by
    have h : 80+i.val < 82+j.val := by omega
    simp [fac, h]
  have h01 : fac 1 (.inr (.inl 0)) (.inr (.inl 1)) = 1-X := by
    rw [fac, if_neg (by decide), if_pos (by decide), sAB, map_one, one_mul]
  have h10 : fac 1 (.inr (.inl 1)) (.inr (.inl 0)) = X+1 := by
    rw [fac, if_neg (by decide), if_neg (by decide), sAB, map_one]
  simp only [rp, Fintype.prod_sum_type, hL, hU, Finset.prod_const, Fin.prod_univ_two]
  fin_cases i
  · simp [h01, h10, fac, sub_eq_add_neg]; ring
  · simp [h01, h10, fac, sub_eq_add_neg]; ring

lemma row_poly (i : Ix) : rp 1 i = (pol (rows i)).map (Rat.castHom ℝ) := by
  rcases i with i | (i | i)
  · rw [rp1L, rows, pol_repl]
    simp [pol, a, x]
    ring
  · rw [rp1M, rows]
    split <;> simp [polA, polB, a, x, y, z]
  · rw [rp1U, rows, pol_repl]
    simp [pol, y, z]
    ring

lemma M1 : M 1 = Q.map (Rat.castHom ℝ) := by
  ext i j
  simp [M, Q, row_poly, pol_coeff]

lemma castneg (q : ℚ) (h : q < 0) : Rat.castHom ℝ q < 0 := by
  change (q : ℝ) < 0
  exact_mod_cast h

lemma negM1 : (M 1).det < 0 := by
  rw [M1]
  change ((Rat.castHom ℝ).mapMatrix Q).det < 0
  rw [← RingHom.map_det]
  exact castneg _ Q_neg

lemma iv (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 1)) (hp : 0 < f 0) (hn : f 1 < 0) :
    ∃ t, 0 < t ∧ t < 1 ∧ f t = 0 := by
  obtain ⟨t, htm, ht⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hc (show (0:ℝ) ∈ Set.Icc (f 1) (f 0) from ⟨hn.le,hp.le⟩)
  exact ⟨t, lt_of_le_of_ne htm.1 (by rintro rfl; linarith), lt_of_le_of_ne htm.2 (by rintro rfl; linarith), ht⟩

-- Compare the normalized factors with the direction factors of the target.
noncomputable def planar (w d : ℝ) (k : Fin 3) : ℝ := if k = 0 then w else if k = 1 then 0 else d
@[simp] lemma planar0 (w d : ℝ) : planar w d 0 = w := by simp [planar]
@[simp] lemma planar1 (w d : ℝ) : planar w d 1 = 0 := by
  rw [planar, if_neg (by decide), if_pos rfl]
@[simp] lemma planar2 (w d : ℝ) : planar w d 2 = d := by
  rw [planar, if_neg (by decide), if_neg (by decide)]

lemma df_planar (w d : ℝ) : directionFactor (planar w d) =
    if Real.sqrt (w^2+d^2) = d then 1 else C (((Real.sqrt (w^2+d^2)-d : ℝ) : ℂ)) * X - C (w : ℂ) := by
  simp only [directionFactor, planar0, planar1, planar2, zero_pow (by decide : 2 ≠ 0), add_zero, Complex.ofReal_zero, zero_mul]

lemma df_up (w d : ℝ) (hd : 0 < d) : ∃ c : ℂ,
    directionFactor (planar w d) = C c * (1 - C ((slope w d : ℝ) : ℂ) * X) := by
  have hh : d + Real.sqrt (w^2+d^2) ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hd (Real.sqrt_nonneg _))
  have hr := Real.sq_sqrt (show 0 ≤ w^2+d^2 by positivity)
  rw [df_planar]
  by_cases hw : w = 0
  · subst w
    refine ⟨1, ?_⟩
    simp [slope, Real.sqrt_sq hd.le]
  have hne : Real.sqrt (w^2+d^2) ≠ d := by
    intro e
    rw [e] at hr
    nlinarith [sq_pos_of_ne_zero hw]
  have ha : Real.sqrt (w^2+d^2)-d = w * slope w d := by
    unfold slope
    field_simp
    nlinarith
  refine ⟨(-w : ℂ), ?_⟩
  rw [if_neg hne, ha, Complex.ofReal_mul, map_mul, map_neg]
  ring

lemma df_down (w d : ℝ) (hd : 0 < d) : ∃ c : ℂ,
    directionFactor (planar (-w) (-d)) = C c * (X + C ((slope w d : ℝ) : ℂ)) := by
  let r := Real.sqrt (w^2+d^2)
  have hpos : 0 < r+d := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hd
  have hn : r ≠ -d := by
    have : 0 ≤ r := Real.sqrt_nonneg _
    linarith
  have hmul : (r+d) * slope w d = w := by
    unfold slope
    change (r+d)*(w/(d+r)) = w
    rw [add_comm d r]
    field_simp
  refine ⟨(r+d : ℝ), ?_⟩
  rw [df_planar, neg_sq, neg_sq]
  change (if r = -d then _ else _) = _
  rw [if_neg hn, sub_neg_eq_add, Complex.ofReal_neg, map_neg, mul_add, ← map_mul, ← Complex.ofReal_mul, hmul]
  ring

lemma normalization {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} (e : J ≃ Fin n)
    (w d : J → ℝ) (hh : ∀ i j, e i < e j → d i < d j) :
    let p := fun i : Fin n => planar (w (e.symm i)) (d (e.symm i))
    let f : J → J → ℝ[X] := fun i j => if i = j then 1 else
      if (e i).val < (e j).val then 1 - C (slope (w j-w i) (d j-d i))*X else X + C (slope (w i-w j) (d i-d j))
    let A : Matrix J J ℝ := fun i j => (∏ k : J, f i k).coeff (e j).val
    Function.Injective p ∧ (A.det = 0 → (configurationMatrix p).det = 0) := by
  classical
  intro p f A
  have p_at (i : J) : p (e i) = planar (w i) (d i) := by simp [p]
  have p_diff (i j : J) : p (e j) - p (e i) = planar (w j - w i) (d j - d i) := by
    rw [p_at, p_at]
    funext k
    fin_cases k
    · change planar (w j) (d j) 0 - planar (w i) (d i) 0 = planar (w j - w i) (d j - d i) 0
      simp
    · change planar (w j) (d j) 1 - planar (w i) (d i) 1 = planar (w j - w i) (d j - d i) 1
      simp
    · change planar (w j) (d j) 2 - planar (w i) (d i) 2 = planar (w j - w i) (d j - d i) 2
      simp
  constructor
  · intro i j h
    by_contra hne
    have he : d (e.symm i) = d (e.symm j) := by simpa [p] using congrFun h (2 : Fin 3)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ne_of_lt (hh _ _ (by simpa using hlt))) he
    · exact (ne_of_lt (hh _ _ (by simpa using hlt))) he.symm
  intro hA
  let g := fun i j : J => if i = j then (1 : ℂ[X]) else directionFactor (p (e j) - p (e i))
  have H (i j : J) : ∃ c : ℂ, g i j = C c * (f i j).map Complex.ofRealHom := by
    by_cases eij : i = j
    · exact ⟨1, by simp [g, f, eij]⟩
    rw [show g i j = directionFactor (p (e j) - p (e i)) by simp [g,eij], p_diff]
    by_cases hij : (e i).val < (e j).val
    · have hfi : f i j = 1 - C (slope (w j-w i) (d j-d i))*X := by
        dsimp only [f]
        rw [if_neg eij, if_pos hij]
      simpa [hfi] using df_up (w j-w i) (d j-d i) (sub_pos.mpr (hh i j hij))
    have hji : (e j).val < (e i).val := by
      have hne : (e i).val ≠ (e j).val := fun ee => eij (e.injective (Fin.ext ee))
      omega
    have hfi : f i j = X + C (slope (w i-w j) (d i-d j)) := by
      dsimp only [f]
      rw [if_neg eij, if_neg hij]
    rw [← neg_sub (w i) (w j), ← neg_sub (d i) (d j)]
    simpa [hfi] using df_down (w i-w j) (d i-d j) (sub_pos.mpr (hh j i hji))
  choose c hc using H
  let D : Matrix J J ℂ := diagonal (fun i => ∏ j : J, c i j)
  let B : Matrix J J ℂ := Complex.ofRealHom.mapMatrix A
  have hg (i : J) : (∏ j : J, g i j) = ∏ k ∈ Finset.univ.erase (e i), directionFactor (p k - p (e i)) := by
    rw [← Equiv.prod_comp e.symm (g i)]
    have he (j : Fin n) : i = e.symm j ↔ j = e i := by rw [eq_comm, Equiv.symm_apply_eq]
    simp only [g, he, Equiv.apply_symm_apply]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul]
    congr 1
    ext k
    simp
  have hmat : (configurationMatrix p).submatrix e e = Bᵀ * D := by
    ext j i
    change (∏ k ∈ Finset.univ.erase (e i), directionFactor (p k - p (e i))).coeff (e j).val = _
    rw [← hg, show (∏ k : J, g i k) = (∏ k : J, C (c i k) * (f i k).map Complex.ofRealHom) by simp only [hc], Finset.prod_mul_distrib, ← map_prod, ← Polynomial.map_prod, coeff_C_mul, coeff_map, Matrix.mul_diagonal]
    change _ = Complex.ofRealHom (A i j) * _
    exact mul_comm _ _
  have hb : B.det = 0 := by rw [show B = Complex.ofRealHom.mapMatrix A from rfl, ← RingHom.map_det, hA, map_zero]
  rw [← Matrix.det_submatrix_equiv_self e, hmat, det_mul, det_transpose, hb, zero_mul]

end AC

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_atiyah_conjecture_on_configurations.main) := by
  intro h
  obtain ⟨t, h0, h1, hz⟩ := AC.iv _ AC.contM (by simp [AC.M0]) AC.negM1
  have hn := AC.normalization AC.idx (AC.ho t) (AC.ht t) (fun _ _ hij => AC.ht_lt h0.le h1 hij)
  exact h 114 _ hn.1 (hn.2 hz)
