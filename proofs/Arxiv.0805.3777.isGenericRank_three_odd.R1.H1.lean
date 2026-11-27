import OMAReductions.R_Arxiv_0805_3777_isGenericRank_three_odd_R1
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
The three-slice Koszul flattening lower bound. The rank-subadditivity argument
follows the project's matrix-rank proof by David Ganz, PR 530. The polynomial
zero-locus argument follows the project's cubic tensor lower-bound proof
in proofs/Arxiv.0805.3777.isGenericRank_cube.R1.H1.lean.
-/

open Filter Topology Matrix Set
open scoped Arxiv.«0805.3777»

namespace OMA.KoszulThree

def idx {n : ℕ} (a : Fin 3) (i j : Fin n) : HolorIndex [3, n, n] :=
  ⟨[a.val, i.val, j.val], List.Forall₂.cons a.isLt
    (List.Forall₂.cons i.isLt (List.Forall₂.cons j.isLt List.Forall₂.nil))⟩

def idxOne {n : ℕ} (i : Fin n) : HolorIndex [n] :=
  ⟨[i.val], List.Forall₂.cons i.isLt List.Forall₂.nil⟩

def cross {R : Type*} [Ring R] (a : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, -a 2, a 1; a 2, 0, -a 0; -a 1, a 0, 0]

def flatten {n : ℕ} {R : Type*} [Ring R] (T : Holor R [3,n,n]) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) R :=
  of fun ai bj => cross (fun c => T (idx c ai.2 bj.2)) ai.1 bj.1

lemma cross_rank_le_two (a : Fin 3 → ℂ) : (cross a).rank ≤ 2 := by
  by_cases ha : a = 0
  · have h0 : cross a = 0 := by
      rw [ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cross]
    simp [h0]
  let B : Matrix (Fin 3) (Fin 1) ℂ := of fun i _ => a i
  have hpos : 0 < B.rank := by
    rw [Matrix.rank]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    have hB : B.mulVecLin (fun _ => 1) = a := by
      funext i
      simp [B, Matrix.mulVecLin, Matrix.mulVec, dotProduct]
    exact ⟨⟨a, ⟨fun _ => 1, hB⟩⟩, fun he => ha (congrArg Subtype.val he)⟩
  have hzero : cross a * B = 0 := by
    ext i j
    fin_cases i <;>
      simp [cross, B, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  simp only [Fintype.card_fin] at hle
  omega

lemma rank_add_le {m n : Type*} [Fintype n] (A B : Matrix m n ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  classical
  have hr : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨v, rfl⟩
    have h : (A + B).mulVecLin v = A.mulVecLin v + B.mulVecLin v := by
      simp [Matrix.mulVecLin]
    rw [h]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hr).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

@[simp] lemma holor_add_apply {n : ℕ} (T S : Holor ℂ [3,n,n]) (i : HolorIndex [3,n,n]) :
    (T + S) i = T i + S i := rfl

@[simp] lemma holor_zero_apply {n : ℕ} (i : HolorIndex [3,n,n]) :
    (0 : Holor ℂ [3,n,n]) i = 0 := rfl

lemma flatten_add {n : ℕ} (T S : Holor ℂ [3,n,n]) :
    flatten (T + S) = flatten T + flatten S := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> simp [flatten, cross, add_comm]

lemma flatten_zero {n : ℕ} : flatten (0 : Holor ℂ [3,n,n]) = 0 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> simp [flatten, cross]

lemma simple_flatten_rank {n : ℕ} {T : Holor ℂ [3,n,n]} (hT : Holor.CPRankMax1 T) :
    (flatten T).rank ≤ 2 := by
  cases hT with
  | cons u y hy =>
    cases hy with
    | cons v z hz =>
      cases hz with
      | cons w t _ =>
        let a (i : Fin 3) := u (idxOne i)
        let b (i : Fin n) := v (idxOne i)
        let c (j : Fin n) := w (idxOne j) * t ⟨[], List.Forall₂.nil⟩
        let L : Matrix (Fin 3 × Fin n) (Fin 3) ℂ :=
          of fun i k => if i.1 = k then b i.2 else 0
        let R : Matrix (Fin 3) (Fin 3 × Fin n) ℂ :=
          of fun k j => if k = j.1 then c j.2 else 0
        have hL (i : Fin 3 × Fin n) (k : Fin 3) :
            (L * cross a) i k = b i.2 * cross a i.1 k := by
          simp [Matrix.mul_apply, L, ite_mul]
        have hLR (i j : Fin 3 × Fin n) :
            (L * cross a * R) i j = b i.2 * cross a i.1 j.1 * c j.2 := by
          simp [Matrix.mul_apply, R, mul_ite, hL]
        have hEval (i : Fin 3) (x y : Fin n) :
            Holor.mul u (Holor.mul v (Holor.mul w t)) (idx i x y) = a i * (b x * c y) := rfl
        have he : flatten (Holor.mul u (Holor.mul v (Holor.mul w t))) = L * cross a * R := by
          ext ⟨i,x⟩ ⟨j,y⟩
          rw [hLR]
          change cross (fun k => Holor.mul u (Holor.mul v (Holor.mul w t)) (idx k x y)) i j = _
          simp only [hEval]
          fin_cases i <;> fin_cases j <;> simp [cross] <;> ring
        rw [he]
        exact (Matrix.rank_mul_le_left _ _).trans
          ((Matrix.rank_mul_le_right _ _).trans (cross_rank_le_two a))

lemma rank_le_of_cprankMax {n r : ℕ} {ds : List ℕ} {T : Holor ℂ ds}
    (hT : Holor.CPRankMax r T) :
    ∀ h : ds = [3,n,n], (flatten (h ▸ T)).rank ≤ 2*r := by
  induction hT with
  | zero =>
    intro h
    subst h
    rw [flatten_zero, Matrix.rank_zero]
  | @succ k ds T S hSimple _ ih =>
    intro h
    subst h
    rw [flatten_add]
    have h1 := simple_flatten_rank hSimple
    have h2 : (flatten S).rank ≤ 2*k := ih rfl
    have h3 := rank_add_le (flatten T) (flatten S)
    omega

lemma rank_le_tensor_rank {n : ℕ} (T : Holor ℂ [3,n,n]) :
    (flatten T).rank ≤ 2 * T.cprank := by
  classical
  have hspec : Holor.CPRankMax T.cprank T := by
    unfold Holor.cprank
    exact Nat.find_spec (p := fun r => Holor.CPRankMax r T)
      (H := ⟨[3,n,n].prod, Holor.cprankMax_upper_bound T⟩)
  exact rank_le_of_cprankMax hspec rfl

def witness (n : ℕ) : Holor ℂ [3,n,n] := fun t =>
  match t.val with
  | [0, i, j] => if i = j then 1 else 0
  | [1, i, j] => if i = j then (i : ℂ) else 0
  | [2, i, j] => if (i + 1) % n = j then 1 else 0
  | _ => 0

lemma shift_val {n : ℕ} (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
  letI := i.neZero
  rw [finRotate_apply]
  change (i.val + 1 % n) % n = (i.val + 1) % n
  exact Nat.add_mod_mod _ _ _

lemma witness_eval0 {n : ℕ} (i j : Fin n) :
    witness n (idx 0 i j) = if i = j then 1 else 0 := by
  unfold witness idx
  simp [Fin.ext_iff]

lemma witness_eval1 {n : ℕ} (i j : Fin n) :
    witness n (idx 1 i j) = if i = j then (i.val : ℂ) else 0 := by
  unfold witness idx
  simp [Fin.ext_iff]

lemma witness_eval2 {n : ℕ} (i j : Fin n) :
    witness n (idx 2 i j) = if finRotate n i = j then 1 else 0 := by
  have h : finRotate n i = j ↔ (i.val + 1) % n = j.val := by
    rw [Fin.ext_iff, shift_val]
  unfold witness idx
  simp only [Fin.val_two, h]

lemma witness_det {n : ℕ} (hn : 2 ≤ n) : (flatten (witness n)).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hzero⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := flatten (witness n))).mpr hd
  apply hv
  have row0 (i : Fin n) : -v (1, finRotate n i) + (i.val : ℂ) * v (2,i) = 0 := by
    have h := congrFun hzero (0,i)
    simpa [flatten, cross, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
      witness_eval0, witness_eval1, witness_eval2, ite_mul, neg_ite] using h
  have row1 (i : Fin n) : v (0, finRotate n i) - v (2,i) = 0 := by
    have h := congrFun hzero (1,i)
    simpa [flatten, cross, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
      witness_eval0, witness_eval1, witness_eval2, ite_mul, neg_ite, sub_eq_add_neg] using h
  have row2 (i : Fin n) : -((i.val : ℂ) * v (0,i)) + v (1,i) = 0 := by
    have h := congrFun hzero (2,i)
    simpa [flatten, cross, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
      witness_eval0, witness_eval1, witness_eval2, ite_mul, neg_ite] using h
  have h2 (i : Fin n) : v (2,i) = v (0,finRotate n i) := (sub_eq_zero.mp (row1 i)).symm
  have h1 (i : Fin n) : v (1,i) = (i.val : ℂ) * v (0,i) := by linear_combination row2 i
  have h0 (i : Fin n) : v (0,i) = 0 := by
    obtain ⟨j,rfl⟩ := (finRotate n).surjective i
    have h := row0 j
    rw [h1, h2] at h
    have hd : (j.val : ℂ) - ((finRotate n j).val : ℂ) ≠ 0 := by
      intro he
      have hj : j.val = (finRotate n j).val := by exact_mod_cast sub_eq_zero.mp he
      rw [shift_val] at hj
      have hjlt := j.isLt
      by_cases hj' : j.val + 1 < n
      · rw [Nat.mod_eq_of_lt hj'] at hj
        omega
      · have heq : j.val + 1 = n := by omega
        rw [heq, Nat.mod_self] at hj
        omega
    exact (mul_eq_zero.mp (show ((j.val : ℂ) - ((finRotate n j).val : ℂ)) *
      v (0, finRotate n j) = 0 by linear_combination h)).resolve_left hd
  funext ⟨i,j⟩
  fin_cases i <;> simp [h0, h1, h2]

noncomputable def detPolynomial (n : ℕ) : MvPolynomial (HolorIndex [3,n,n]) ℂ :=
  (flatten (fun i => MvPolynomial.X i)).det

lemma eval_detPolynomial {n : ℕ} (T : Holor ℂ [3,n,n]) :
    MvPolynomial.eval T (detPolynomial n) = (flatten T).det := by
  unfold detPolynomial
  rw [RingHom.map_det]
  congr 1
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> simp [flatten, cross, Matrix.map_apply] <;>
    exact MvPolynomial.eval_X (f := T) _

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hz : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hz

lemma generic_lower (p : ℕ) (hp : 1 ≤ p) :
    ∃ U : Set (Holor ℂ [3, 2 * p + 1, 2 * p + 1]),
      IsOpen U ∧ Dense U ∧ ∀ T ∈ U, 3 * p + 2 ≤ T.cprank := by
  let n := 2*p+1
  have hn : 2 ≤ n := by dsimp [n]; omega
  refine ⟨{T | (flatten T).det ≠ 0}, ?_, ?_, ?_⟩
  · have hcont : Continuous (flatten : Holor ℂ [3,n,n] → _) := by
      refine continuous_matrix ?_
      intro ⟨i,a⟩ ⟨j,b⟩
      fin_cases i <;> fin_cases j <;> simp [flatten, cross] <;>
        first | exact continuous_const | exact continuous_apply _ | exact (continuous_apply _).neg
    exact isOpen_ne_fun hcont.matrix_det continuous_const
  · rw [dense_iff_closure_eq]
    change closure ({T : HolorIndex [3,n,n] → ℂ | (flatten (n := n) T).det = 0}ᶜ) = Set.univ
    have hP : detPolynomial n ≠ 0 := by
      intro h
      have he := eval_detPolynomial (witness n)
      rw [h, map_zero] at he
      exact witness_det hn he.symm
    have hz : {T : HolorIndex [3,n,n] → ℂ | (flatten (n := n) T).det = 0} =
        {T : HolorIndex [3,n,n] → ℂ | MvPolynomial.eval T (detPolynomial n) = 0} := by
      ext T
      change (flatten T).det = 0 ↔ MvPolynomial.eval T (detPolynomial n) = 0
      rw [eval_detPolynomial (n := n) T]
    rw [hz, closure_compl, interior_polynomial_zero_locus _ hP, Set.compl_empty]
  · intro T hT
    have hdet : (flatten T).det ≠ 0 := hT
    have hFull := Matrix.rank_of_det_ne_zero hdet
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hFull
    have hRank := rank_le_tensor_rank T
    omega

end OMA.KoszulThree

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_three_odd_R1.H1 :=
  OMA.KoszulThree.generic_lower
