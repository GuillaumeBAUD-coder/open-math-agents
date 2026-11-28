import OMAStatements.S_mo_388967
import Mathlib

open OMA.S_mo_388967
open Matrix Finset
open scoped BigOperators

namespace MinimalSpan

lemma rankOneFactor {n : ℕ} (A : Sq n) (h : A.rank = 1) :
    ∃ u v : Fin n → ℂ, A = Matrix.vecMulVec u v := by
  classical
  let S := Submodule.span ℂ (Set.range A.col)
  have hd : Module.finrank ℂ S = 1 := A.rank_eq_finrank_span_cols.symm.trans h
  obtain ⟨u, -, hu⟩ := finrank_eq_one_iff'.mp hd
  have hcol (j : Fin n) : A.col j ∈ S := Submodule.subset_span ⟨j, rfl⟩
  choose v hv using fun j => hu (⟨A.col j, hcol j⟩ : S)
  refine ⟨u, v, ?_⟩
  ext i j
  have hij := congrFun (congrArg Subtype.val (hv j)) i
  change v j * u.val i = A i j at hij
  simpa [Matrix.vecMulVec, mul_comm] using hij.symm

lemma sum_index {n : ℕ} (A : ℕ → Sq n) (e : Fin n ↪ ℕ) :
    ∑ i ∈ Finset.univ.map e, A i = ∑ j : Fin n, A (e j) := by
  rw [Finset.sum_map]

lemma sum_factor {n : ℕ} (u v : ℕ → Fin n → ℂ) (e : Fin n ↪ ℕ) :
    ∑ q : Fin n, Matrix.vecMulVec (u (e q)) (v (e q)) =
      (Matrix.of fun i q => u (e q) i) * (Matrix.of fun q j => v (e q) j) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec, Matrix.sum_apply]

lemma families {n : ℕ} (A : ℕ → Sq n) (hA : Admissible n A) :
    ∃ u v : ℕ → Fin n → ℂ,
      (∀ q, A q = Matrix.vecMulVec (u q) (v q)) ∧
      (∀ e : Fin n ↪ ℕ, LinearIndependent ℂ (u ∘ e)) ∧
      (∀ e : Fin n ↪ ℕ, LinearIndependent ℂ (v ∘ e)) := by
  classical
  choose u v h using fun i => rankOneFactor (A i) (hA.1 i)
  refine ⟨u, v, h, ?_, ?_⟩
  · intro e
    have hdet := hA.2 (Finset.univ.map e) (by simp)
    simp_rw [sum_index, h, sum_factor, Matrix.det_mul, isUnit_iff_ne_zero] at hdet
    exact Matrix.linearIndependent_cols_of_det_ne_zero (fun hz => hdet (by
      have hz' : (Matrix.of fun i q => u (e q) i).det = 0 := hz
      rw [hz', zero_mul]))
  · intro e
    have hdet := hA.2 (Finset.univ.map e) (by simp)
    simp_rw [sum_index, h, sum_factor, Matrix.det_mul, isUnit_iff_ne_zero] at hdet
    exact Matrix.linearIndependent_rows_of_det_ne_zero (fun hz => hdet (by
      have hz' : (Matrix.of fun q j => v (e q) j).det = 0 := hz
      rw [hz', mul_zero]))

noncomputable def model (n : ℕ) (q : ℕ) : Sq n :=
  Matrix.vecMulVec (fun i => (q : ℂ) ^ i.val) (fun i => (q : ℂ) ^ i.val)

lemma model_admissible (n : ℕ) (hn : 0 < n) : Admissible n (model n) := by
  classical
  constructor
  · intro q
    apply le_antisymm (rank_vecMulVec_le _ _)
    let j : Fin n := ⟨0, hn⟩
    have hne : ((model n q).col j) ≠ 0 := by
      intro h
      have he := congrFun h j
      norm_num [j, model, Matrix.vecMulVec, Matrix.col] at he
    rw [Matrix.rank_eq_finrank_span_cols]
    have hc : (model n q).col j ∈ Submodule.span ℂ (Set.range (model n q).col) :=
      Submodule.subset_span ⟨j, rfl⟩
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, hc⟩, by
      intro h
      exact hne (congrArg Subtype.val h)⟩
  · intro s hs
    let b : Fin n ≃ s := (Finset.equivFinOfCardEq hs).symm
    let e : Fin n ↪ ℕ := b.toEmbedding.trans (Function.Embedding.subtype _)
    have he : Finset.univ.map e = s := by
      ext q
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact (b i).property
      · intro hq
        exact ⟨b.symm ⟨q, hq⟩, by simp [e]⟩
    have hcast : Function.Injective (fun i : Fin n => (e i : ℂ)) := by
      intro i j hij
      apply e.injective
      exact Nat.cast_injective (R := ℂ) hij
    have hdet := Matrix.det_vandermonde_ne_zero_iff.mpr hcast
    rw [← he, sum_index]
    unfold model
    rw [sum_factor (fun q i => (q : ℂ) ^ i.val) (fun q i => (q : ℂ) ^ i.val),
      Matrix.det_mul]
    have hprod₁ : (Matrix.of fun (i q : Fin n) => (e q : ℂ) ^ (i : ℕ)) =
        (Matrix.vandermonde fun q => (e q : ℂ))ᵀ := rfl
    have hprod₂ : (Matrix.of fun (q j : Fin n) => (e q : ℂ) ^ (j : ℕ)) =
        Matrix.vandermonde (fun q => (e q : ℂ)) := rfl
    rw [hprod₁, hprod₂, Matrix.det_transpose]
    exact (isUnit_iff_ne_zero.mpr hdet).mul (isUnit_iff_ne_zero.mpr hdet)

lemma model_finrank_le (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (model n))) ≤ 2 * n - 1 := by
  classical
  let coord (i j : Fin n) : Fin (2 * n - 1) := ⟨i.val + j.val, by omega⟩
  let Hankel : (Fin (2 * n - 1) → ℂ) →ₗ[ℂ] Sq n :=
    { toFun := fun p => Matrix.of fun i j => p (coord i j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hspan : Submodule.span ℂ (Set.range (model n)) ≤ LinearMap.range Hankel := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    refine ⟨fun t => (q : ℂ) ^ t.val, ?_⟩
    ext i j
    exact pow_add _ _ _
  exact (Submodule.finrank_mono hspan).trans (by simpa using Hankel.finrank_range_le)

def project {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] ℂ) : Sq n →ₗ[ℂ] Fin n → ℂ where
  toFun A j := f (A.col j)
  map_add' A B := by
    funext j
    change f (A.col j + B.col j) = _
    rw [map_add]
    rfl
  map_smul' c A := by
    funext j
    change f (c • A.col j) = _
    rw [map_smul]
    rfl

lemma project_outer {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] ℂ) (u v : Fin n → ℂ) :
    project f (Matrix.vecMulVec u v) = f u • v := by
  funext j
  have hcol : (Matrix.vecMulVec u v).col j = v j • u := by
    funext i
    simp [Matrix.col, Matrix.vecMulVec, mul_comm]
  change f ((Matrix.vecMulVec u v).col j) = f u * v j
  rw [hcol, map_smul]
  exact mul_comm _ _

lemma dimension_lower (m : ℕ) (A : ℕ → Sq (m + 1)) (hA : Admissible (m + 1) A) :
    2 * (m + 1) - 1 ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range A)) := by
  classical
  obtain ⟨u, v, hAeval, hu, hv⟩ := families A hA
  let e : Fin (m + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let e' : Fin (m + 1) ↪ ℕ := ⟨fun i => m + i.val, by
    intro i j h
    exact Fin.ext (Nat.add_left_cancel h)⟩
  have hdim : Fintype.card (Fin (m + 1)) = Module.finrank ℂ (Fin (m + 1) → ℂ) := by simp
  let U := basisOfLinearIndependentOfCardEqFinrank (hu e) hdim
  have hU (i : Fin (m + 1)) : U i = u i.val := by
    simp [U, e]
  let L := U.coord (Fin.last m)
  have hLleft (i : Fin m) : L (u i.val) = 0 := by
    have hi : U i.castSucc = u i.val := hU i.castSucc
    rw [← hi]
    simp [L, Module.Basis.coord_apply, Fin.castSucc_ne_last, eq_comm]
  have hLright (q : ℕ) (hq : m ≤ q) : L (u q) ≠ 0 := by
    intro hz
    let w : Fin (m + 1) ↪ ℕ :=
      ⟨fun i => if i.val = m then q else i.val, by
        intro i j hij
        have hi := i.isLt
        have hj := j.isLt
        apply Fin.ext
        dsimp at hij
        split at hij <;> split at hij <;> omega⟩
    let W := basisOfLinearIndependentOfCardEqFinrank (hu w) hdim
    have hzero : L = 0 := by
      apply W.ext
      intro i
      have hw : W i = u (w i) := by simp [W]
      rw [hw]
      change L (u (if i.val = m then q else i.val)) = 0
      split
      · exact hz
      · rename_i h
        exact hLleft ⟨i.val, by have := i.isLt; omega⟩
    have hone : L (u m) = 1 := by
      have hl : U (Fin.last m) = u m := hU (Fin.last m)
      rw [← hl]
      simp [L, Module.Basis.coord_apply]
    rw [hzero] at hone
    norm_num at hone
  let index : Fin m ⊕ Fin (m + 1) → ℕ := Sum.elim Fin.val e'
  have hLI : LinearIndependent ℂ (A ∘ index) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hp := congrArg (project L) hc
    simp only [Fintype.sum_sum_type, map_add, map_sum, map_smul, map_zero, Function.comp_apply,
      index, Sum.elim_inl, Sum.elim_inr, hAeval, project_outer, hLleft, zero_smul, smul_zero,
      Finset.sum_const_zero, zero_add, smul_smul] at hp
    have hr (i : Fin (m + 1)) : c (Sum.inr i) = 0 := by
      have hz := (Fintype.linearIndependent_iff.mp (hv e')
        (fun q => c (Sum.inr q) * L (u (e' q))) hp i)
      exact (mul_eq_zero.mp hz).resolve_right (hLright (e' i) (by change m ≤ m + i.val; omega))
    have hc' : ∑ i : Fin m, c (Sum.inl i) • A i.val = 0 := by
      simpa [Fintype.sum_sum_type, Function.comp_apply, index, hr] using hc
    intro i
    cases i with
    | inr i => exact hr i
    | inl i =>
      have hcj := congrArg (project (U.coord i.castSucc)) hc'
      have hcoord (j : Fin m) :
          U.coord i.castSucc (u j.val) = if j = i then 1 else 0 := by
        have hj : U j.castSucc = u j.val := hU j.castSucc
        rw [← hj, Module.Basis.coord_apply, Module.Basis.repr_self]
        simp [Finsupp.single_apply, eq_comm]
      simp only [map_sum, map_smul, map_zero, hAeval, project_outer, hcoord, smul_smul] at hcj
      have hh : c (Sum.inl i) • v i.val = 0 := by
        rw [Finset.sum_eq_single i] at hcj
        · simpa using hcj
        · intro j _ hj
          simp [hj]
        · simp
      exact (smul_eq_zero.mp hh).resolve_right ((hv e).ne_zero i.castSucc)
  have hspan : Submodule.span ℂ (Set.range (A ∘ index)) ≤ Submodule.span ℂ (Set.range A) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨index i, rfl⟩)
  have hd := (Submodule.finrank_mono hspan)
  rw [finrank_span_eq_card hLI, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hd
  omega

lemma lower (n : ℕ) (hn : 0 < n) (A : ℕ → Sq n) (hA : Admissible n A) :
    2 * n - 1 ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range A)) := by
  cases n with
  | zero => omega
  | succ m => exact dimension_lower m A hA

end MinimalSpan

open MinimalSpan in
theorem OMA.solution : ∀ n : ℕ, 0 < n →
    IsLeast {d : ℕ | ∃ A : ℕ → Sq n, Admissible n A ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = d} (2 * n - 1) := by
  intro n hn
  constructor
  · exact ⟨model n, model_admissible n hn,
      le_antisymm (model_finrank_le n hn) (lower n hn _ (model_admissible n hn))⟩
  · rintro d ⟨A, ha, rfl⟩
    exact lower n hn A ha