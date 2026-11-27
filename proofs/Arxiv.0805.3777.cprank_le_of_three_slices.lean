import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Problem: Generic and maximal rank of 3-tensors — cprank le of three slices
-- Upstream: formal-conjectures FormalConjectures/Arxiv/0805.3777/TensorRank.lean:291 (declaration Arxiv.«0805.3777».cprank_le_of_three_slices)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof. Every complex n x n x 3 tensor has rank at most 2n - 1 (Sumi, Miyazaki, Sakata,
-- Ann. Inst. Statist. Math. 62 (2010), Theorem 4.5; arXiv 0806.4048). We follow the structure of
-- their induction, on the level of the span of the three slices (CP3.Cov): pick a nonzero
-- singular matrix in the span, bring it to a 0/1 diagonal form, and split into cases.
-- * A nonzero entry in the zero block, or a column of the zero block with independent fibres:
--   their Lemma 4.3 (perturb by diagonal matrices so that the remaining pencil has distinct
--   eigenvalues). The analytic perturbation argument is replaced by an algebraic one: indices
--   are added one at a time, and h + x F is separable for all but finitely many x when F is
--   separable (CP3.fel, CP3.osl, CP3.osl_all); distinct eigenvalues give a diagonalisation
--   (CP3.nice_of_good). Their Lemma 4.4 is replaced by an explicit elementary conjugation.
-- * A zero row (or column) in the zero block, or only rank-one fibres: peel rows and columns
--   and use the induction hypothesis.
--
-- Reuse and credit: the section Bridge (holor indices, slices, rank-one holors, and the passage
-- from a cover by rank-one matrices to a CP-rank bound) is adapted from the Bridge section of
-- proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean (merged in PR 2438, credited to
-- DomTheDeveloper), which is itself a port of the work of Kenta Kitamura,
-- https://github.com/KitaKen1/mrank-3-3-5-lean (Apache License 2.0). Everything else is new.

namespace CP3

open Matrix Polynomial

theorem sep_iff (f : ℂ[X]) :
    f.Separable ↔ ∀ a : ℂ, f.eval a ≠ 0 ∨ (derivative f).eval a ≠ 0 := by
  rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  simp only [coe_aeval_eq_eval]

theorem fel (F h : ℂ[X]) (hF : F.Separable) :
    {x : ℂ | ¬ (h + C x * F).Separable}.Finite := by
  set W := F * derivative h - derivative F * h with hWdef
  have hF0 : F ≠ 0 := hF.ne_zero
  by_cases hW : W = 0
  · have hdvd : F ∣ h := by
      have h1 : F ∣ h * derivative F := ⟨derivative h, by linear_combination (-1 : ℂ[X]) * hW⟩
      exact ((separable_def F).mp hF).dvd_of_dvd_mul_right h1
    obtain ⟨g, rfl⟩ := hdvd
    have hg : derivative g = 0 := by
      have h2 : F * F * derivative g = 0 := by
        rw [hWdef, derivative_mul] at hW
        linear_combination hW
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (mul_self_eq_zero.mp h3) hF0
      · exact h3
    have hgC := eq_C_of_derivative_eq_zero hg
    apply (Set.finite_singleton (-(g.coeff 0))).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hx
    have : F * g + C x * F = F * C (g.coeff 0 + x) := by
      rw [hgC]; simp only [coeff_C_zero, C_add]; ring
    rw [this]
    refine hF.mul_unit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_))
    intro h0; apply hne; linear_combination h0
  · let φ : ℂ → ℂ := fun a => if F.eval a ≠ 0 then -(h.eval a / F.eval a)
      else -((derivative h).eval a / (derivative F).eval a)
    apply ((W.roots.toFinset.finite_toSet).image φ).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [sep_iff] at hx
    push_neg at hx
    obtain ⟨a, ha1, ha2⟩ := hx
    simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, eval_add,
      eval_mul, eval_C] at ha1 ha2
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [mem_roots hW, IsRoot, hWdef]
      simp only [eval_sub, eval_mul]
      linear_combination (eval a F) * ha2 - (eval a (derivative F)) * ha1
    · simp only [φ]
      by_cases hFa : F.eval a ≠ 0
      · rw [if_pos hFa, neg_eq_iff_eq_neg, div_eq_iff hFa]; linear_combination ha1
      · rw [if_neg hFa]
        push_neg at hFa
        have hF' : (derivative F).eval a ≠ 0 := by
          rcases (sep_iff F).mp hF a with h4 | h4
          · exact absurd hFa h4
          · exact h4
        rw [neg_eq_iff_eq_neg, div_eq_iff hF']; linear_combination ha2

/-- determinant is affine in the bottom-right corner entry -/
theorem det_add_corner {R : Type*} [CommRing R] (k : ℕ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (a : R) : (M + diagonal (Pi.single (Fin.last k) a)).det
      = M.det + a * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row _ (Fin.last k), det_succ_row M (Fin.last k)]
  simp_rw [Fin.succAbove_last]
  have hsub : ∀ j : Fin (k + 1), ((M + diagonal (Pi.single (Fin.last k) a)).submatrix
      Fin.castSucc j.succAbove) = M.submatrix Fin.castSucc j.succAbove := by
    intro j; ext r c
    simp [diagonal_apply, Fin.castSucc_ne_last]
  simp_rw [hsub]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin k, (M + diagonal (Pi.single (Fin.last k) a)) (Fin.last k) j.castSucc
      = M (Fin.last k) j.castSucc := by
    intro j; simp [diagonal_apply, (Fin.castSucc_ne_last j).symm]
  have h2 : (M + diagonal (Pi.single (Fin.last k) a)) (Fin.last k) (Fin.last k)
      = M (Fin.last k) (Fin.last k) + a := by simp [diagonal_apply]
  simp_rw [h1, h2, Fin.succAbove_last]
  have : ((-1 : R) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]; simp
  rw [this]
  ring


/-- the pencil polynomial `det (X U + V)` -/
noncomputable def penPoly {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) : ℂ[X] :=
  ((X : ℂ[X]) • U.map C + V.map C).det

/-- a pencil with invertible first member and `n` distinct generalized eigenvalues -/
def Good {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) : Prop :=
  U.det ≠ 0 ∧ (penPoly U V).Separable

theorem exists_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : ∃ a : ℂ, p.eval a ≠ 0 := by
  obtain ⟨a, ha⟩ := (p.roots.toFinset.finite_toSet).exists_notMem
  refine ⟨a, fun h0 => ha ?_⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (mem_roots hp).mpr h0

theorem osl (k : ℕ) (U V : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : Good (U.submatrix Fin.castSucc Fin.castSucc) (V.submatrix Fin.castSucc Fin.castSucc)) :
    ∃ x y : ℂ, Good (U + diagonal (Pi.single (Fin.last k) x))
      (V + diagonal (Pi.single (Fin.last k) y)) := by
  set Ub := U.submatrix Fin.castSucc Fin.castSucc
  set Vb := V.submatrix Fin.castSucc Fin.castSucc
  set pb := penPoly Ub Vb with hpb
  have hpb0 : pb ≠ 0 := h.2.ne_zero
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hpb0
  have hcop : IsCoprime (X - C a) pb := by
    rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro b
    simp only [coe_aeval_eq_eval, eval_sub, eval_X, eval_C]
    by_cases hb : b = a
    · right; rw [hb]; exact ha
    · left; exact sub_ne_zero.mpr hb
  set F := (X - C a) * pb with hF
  have hFs : F.Separable := (separable_X_sub_C (R := ℂ) (x := a)).mul h.2 hcop
  have hpen : ∀ x : ℂ, penPoly (U + diagonal (Pi.single (Fin.last k) x))
      (V + diagonal (Pi.single (Fin.last k) (-a * x))) = penPoly U V + C x * F := by
    intro x
    unfold penPoly
    have e1 : (X : ℂ[X]) • (U + diagonal (Pi.single (Fin.last k) x)).map C
        + (V + diagonal (Pi.single (Fin.last k) (-a * x))).map C
        = ((X : ℂ[X]) • U.map C + V.map C) + diagonal (Pi.single (Fin.last k) (C x * (X - C a))) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, diagonal_apply,
        smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = Fin.last k
        · subst hi; simp only [if_true, Pi.single_eq_same, map_add, map_mul, map_neg]; ring
        · simp [Pi.single_eq_of_ne hi]
      · simp [hij]
    rw [e1, det_add_corner]
    have e2 : ((X : ℂ[X]) • U.map C + V.map C).submatrix Fin.castSucc Fin.castSucc
        = (X : ℂ[X]) • Ub.map C + Vb.map C := by
      ext i j; simp [Ub, Vb]
    rw [e2, hF, hpb]
    unfold penPoly
    ring
  have hdet : ∀ x : ℂ, (U + diagonal (Pi.single (Fin.last k) x)).det = U.det + x * Ub.det :=
    fun x => det_add_corner k U x
  have hfin := fel F (penPoly U V) hFs
  have hfin2 : {x : ℂ | U.det + x * Ub.det = 0}.Finite := by
    apply (Set.finite_singleton (-(U.det / Ub.det))).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_singleton_iff]
    rw [eq_neg_iff_add_eq_zero, add_div_eq_mul_add_div _ _ h.1, div_eq_zero_iff]
    left; linear_combination hx
  obtain ⟨x, hx⟩ := (hfin.union hfin2).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hx
  refine ⟨x, -a * x, ?_, ?_⟩
  · rw [hdet]; exact hx.2
  · rw [hpen]; exact hx.1

theorem osl_all (s : ℕ) : ∀ (n : ℕ) (hs : s ≤ n) (U V : Matrix (Fin n) (Fin n) ℂ),
    Good (U.submatrix (Fin.castLE hs) (Fin.castLE hs)) (V.submatrix (Fin.castLE hs) (Fin.castLE hs))
    → ∃ d₁ d₂ : Fin n → ℂ, (∀ i : Fin n, (i : ℕ) < s → d₁ i = 0 ∧ d₂ i = 0)
      ∧ Good (U + diagonal d₁) (V + diagonal d₂) := by
  intro n
  induction n with
  | zero =>
    intro hs U V h
    obtain rfl : s = 0 := by omega
    refine ⟨0, 0, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    have hU : U + diagonal (0 : Fin 0 → ℂ) = U.submatrix (Fin.castLE hs) (Fin.castLE hs) :=
      Subsingleton.elim _ _
    have hV : V + diagonal (0 : Fin 0 → ℂ) = V.submatrix (Fin.castLE hs) (Fin.castLE hs) :=
      Subsingleton.elim _ _
    rw [hU, hV]; exact h
  | succ k ih =>
    intro hs U V h
    by_cases hsk : s = k + 1
    · subst hsk
      refine ⟨0, 0, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
      have e : ∀ W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
          W.submatrix (Fin.castLE hs) (Fin.castLE hs) = W + diagonal 0 := by
        intro W; ext i j; simp
      rw [e U, e V] at h; exact h
    · have hs' : s ≤ k := by omega
      obtain ⟨e₁, e₂, he, hg⟩ := ih hs' (U.submatrix Fin.castSucc Fin.castSucc)
        (V.submatrix Fin.castSucc Fin.castSucc) (by
          have e : ∀ W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
              (W.submatrix Fin.castSucc Fin.castSucc).submatrix (Fin.castLE hs') (Fin.castLE hs')
              = W.submatrix (Fin.castLE hs) (Fin.castLE hs) := by
            intro W; ext i j; simp
          rw [e U, e V]; exact h)
      have e3 : ∀ (W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (e : Fin k → ℂ),
          (W + diagonal (Fin.snoc e 0)).submatrix Fin.castSucc Fin.castSucc
            = W.submatrix Fin.castSucc Fin.castSucc + diagonal e := by
        intro W e; ext i j
        simp only [submatrix_apply, Matrix.add_apply, diagonal_apply, Fin.castSucc_inj,
          Fin.snoc_castSucc]
      obtain ⟨x, y, hxy⟩ := osl k (U + diagonal (Fin.snoc e₁ 0))
        (V + diagonal (Fin.snoc e₂ 0)) (by rw [e3, e3]; exact hg)
      refine ⟨Fin.snoc e₁ 0 + Pi.single (Fin.last k) x, Fin.snoc e₂ 0 + Pi.single (Fin.last k) y,
        ?_, ?_⟩
      · intro i hi
        have hne : i ≠ Fin.last k := by
          intro h0; rw [h0, Fin.val_last] at hi; omega
        obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hne
        have hi' : (i' : ℕ) < s := by simpa using hi
        rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne,
          Fin.snoc_castSucc, Fin.snoc_castSucc, (he i' hi').1, (he i' hi').2]
        simp
      · have key : ∀ (W : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (f g : Fin (k + 1) → ℂ),
            W + diagonal (f + g) = W + diagonal f + diagonal g := by
          intro W f g; rw [add_assoc, diagonal_add]; rfl
        rw [key, key]; exact hxy

theorem core1 (U V : Matrix (Fin 1) (Fin 1) ℂ) (h : U 0 0 ≠ 0) : Good U V := by
  refine ⟨by rw [det_unique]; exact h, ?_⟩
  unfold penPoly
  rw [det_unique]
  have : ((X : ℂ[X]) • U.map C + V.map C) default default = C (U 0 0) * (X + C (V 0 0 / U 0 0)) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [mul_add, ← C_mul, mul_div_cancel₀ _ h]
    simp only [Fin.default_eq_zero]; ring
  rw [this]
  exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr h)) (separable_X_add_C _)

theorem lin_sep {α β : ℂ} (h : α ≠ 0) : (X * C α + C β).Separable := by
  have : X * C α + C β = C α * (X + C (β / α)) := by
    rw [mul_add, ← C_mul, mul_div_cancel₀ _ h]; ring
  rw [this]
  exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr h)) (separable_X_add_C _)

theorem core2 (U V : Matrix (Fin 2) (Fin 2) ℂ) (h11 : U 1 1 = 0) (h11' : V 1 1 = 0)
    (h1 : U 0 1 * U 1 0 ≠ 0) (h2 : U 0 1 * V 1 0 ≠ V 0 1 * U 1 0) : Good U V := by
  refine ⟨by rw [det_fin_two, h11]; simpa using h1, ?_⟩
  have hα : U 0 1 ≠ 0 := left_ne_zero_of_mul h1
  have hβ : U 1 0 ≠ 0 := right_ne_zero_of_mul h1
  unfold penPoly
  rw [det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, h11, h11',
    map_zero, mul_zero, add_zero, zero_sub]
  rw [neg_eq_neg_one_mul, ← C_1, ← C_neg]
  refine Separable.unit_mul (isUnit_C.mpr (by norm_num)) ((lin_sep hα).mul (lin_sep hβ) ?_)
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro a
  simp only [coe_aeval_eq_eval, eval_add, eval_mul, eval_X, eval_C]
  by_contra hc
  push_neg at hc
  apply h2
  linear_combination (U 0 1) * hc.2 - (U 1 0) * hc.1

theorem outer_sum {k : ℕ} (M W : Matrix (Fin k) (Fin k) ℂ) (hW : W.det ≠ 0) :
    M = ∑ l, vecMulVec (M *ᵥ fun i => W i l) (W⁻¹ l) := by
  have h1 : M = M * W * W⁻¹ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hW), Matrix.mul_one]
  ext i j
  conv_lhs => rw [h1]
  simp only [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, mulVec, dotProduct,
    Finset.sum_mul]

theorem nice_of_good {k : ℕ} (U V : Matrix (Fin k) (Fin k) ℂ) (h : Good U V) :
    ∃ (x y : Fin k → Fin k → ℂ) (c : Fin k → ℂ),
      U = ∑ l, vecMulVec (x l) (y l) ∧ V = ∑ l, c l • vecMulVec (x l) (y l) := by
  set p := penPoly U V with hp
  have hp0 : p ≠ 0 := h.2.ne_zero
  have hdeg : p.natDegree = k := by
    apply le_antisymm
    · have := natDegree_det_X_add_C_le U V
      simp only [Fintype.card_fin] at this
      rw [hp, penPoly]; exact this
    · apply le_natDegree_of_ne_zero
      have := coeff_det_X_add_C_card U V
      simp only [Fintype.card_fin] at this
      rw [hp, penPoly, this]; exact h.1
  have hcard : p.roots.card = k := by
    rw [← hdeg]; exact splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hnd : p.roots.Nodup := nodup_roots h.2
  have hfc : p.roots.toFinset.card = k := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let μ : Fin k → ℂ := fun l => (p.roots.toFinset.equivFin.symm (Fin.cast hfc.symm l) : ℂ)
  have hμinj : Function.Injective μ := by
    intro a b hab
    have := Subtype.val_injective hab
    exact Fin.cast_injective _ (p.roots.toFinset.equivFin.symm.injective this)
  have hμroot : ∀ l, p.eval (μ l) = 0 := by
    intro l
    have hm : μ l ∈ p.roots.toFinset := (p.roots.toFinset.equivFin.symm _).2
    rw [Multiset.mem_toFinset, mem_roots hp0] at hm
    exact hm
  have hdet : ∀ l, (μ l • U + V).det = 0 := by
    intro l
    rw [← hμroot l, hp, penPoly, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  choose v hv0 hv using fun l => exists_mulVec_eq_zero_iff.mpr (hdet l)
  have hUu : IsUnit U := (isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr h.1)
  have hVv : ∀ l, V *ᵥ v l = (-(μ l)) • (U *ᵥ v l) := by
    intro l
    have := hv l
    rw [add_mulVec, smul_mulVec] at this
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact this
  have heig : ∀ l, Module.End.HasEigenvector (toLin' (U⁻¹ * V)) (-(μ l)) (v l) := by
    intro l
    refine ⟨?_, hv0 l⟩
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, ← mulVec_mulVec, hVv l, mulVec_smul,
      mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det U).mp hUu), one_mulVec]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (toLin' (U⁻¹ * V)) (fun l => -(μ l))
      (neg_injective.comp hμinj) v heig
  let W : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i l => v l i
  have hWcol : W.col = v := by ext l i; rfl
  have hW : IsUnit W := (linearIndependent_cols_iff_isUnit (K := ℂ)).mp (by rw [hWcol]; exact hli)
  have hWd : W.det ≠ 0 := ((isUnit_iff_isUnit_det W).mp hW).ne_zero
  have hcol : ∀ l, (fun i => W i l) = v l := fun l => rfl
  refine ⟨fun l => U *ᵥ v l, fun l => W⁻¹ l, fun l => -(μ l), ?_, ?_⟩
  · conv_lhs => rw [outer_sum U W hWd]
    simp only [hcol]
  · conv_lhs => rw [outer_sum V W hWd]
    simp only [hcol, hVv, smul_vecMulVec]


/-! ### Coverings of matrix spaces by rank-one matrices -/

/-- `M` has rank at most one -/
def IsR1 {ι κ : Type*} (M : Matrix ι κ ℂ) : Prop := ∃ (a : ι → ℂ) (b : κ → ℂ), M = vecMulVec a b

/-- `S` lies in the span of at most `r` matrices of rank at most one -/
def Cov {ι κ : Type*} (S : Submodule ℂ (Matrix ι κ ℂ)) (r : ℕ) : Prop :=
  ∃ s : Finset (Matrix ι κ ℂ), s.card ≤ r ∧ (∀ M ∈ s, IsR1 M) ∧ S ≤ Submodule.span ℂ (s : Set _)

section CovAPI

variable {ι κ ι' κ' : Type*}

theorem Cov.mono {S S' : Submodule ℂ (Matrix ι κ ℂ)} {r : ℕ} (h : S' ≤ S) (hS : Cov S r) :
    Cov S' r := by
  obtain ⟨s, hs, h1, h2⟩ := hS
  exact ⟨s, hs, h1, h.trans h2⟩

theorem Cov.mono_r {S : Submodule ℂ (Matrix ι κ ℂ)} {r r' : ℕ} (h : r ≤ r') (hS : Cov S r) :
    Cov S r' := by
  obtain ⟨s, hs, h1, h2⟩ := hS
  exact ⟨s, hs.trans h, h1, h2⟩

theorem Cov.sup {S₁ S₂ : Submodule ℂ (Matrix ι κ ℂ)} {r₁ r₂ : ℕ} (h₁ : Cov S₁ r₁)
    (h₂ : Cov S₂ r₂) : Cov (S₁ ⊔ S₂) (r₁ + r₂) := by
  classical
  obtain ⟨s, hs, hs1, hs2⟩ := h₁
  obtain ⟨t, ht, ht1, ht2⟩ := h₂
  refine ⟨s ∪ t, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · exact hs1 M h
    · exact ht1 M h
  · refine sup_le (hs2.trans (Submodule.span_mono ?_)) (ht2.trans (Submodule.span_mono ?_))
    · intro x hx; simp only [Finset.coe_union]; exact Or.inl hx
    · intro x hx; simp only [Finset.coe_union]; exact Or.inr hx

theorem Cov.map {S : Submodule ℂ (Matrix ι κ ℂ)} {r : ℕ}
    (f : Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ) (hf : ∀ M, IsR1 M → IsR1 (f M)) (hS : Cov S r) :
    Cov (S.map f) r := by
  classical
  obtain ⟨s, hs, h1, h2⟩ := hS
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_, ?_⟩
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hM
    exact hf N (h1 N hN)
  · refine (Submodule.map_mono h2).trans ?_
    rw [Submodule.map_span, Finset.coe_image]

theorem cov_family {β : Type*} [Fintype β] (x : β → ι → ℂ) (y : β → κ → ℂ) :
    Cov (Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) (Fintype.card β) := by
  classical
  refine ⟨Finset.univ.image fun l => vecMulVec (x l) (y l), Finset.card_image_le, ?_, ?_⟩
  · intro M hM
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hM
    exact ⟨x l, y l, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨l, rfl⟩
    simp

/-- the span of three matrices -/
def sp3 (A B C : Matrix ι κ ℂ) : Submodule ℂ (Matrix ι κ ℂ) :=
  Submodule.span ℂ ({A, B, C} : Set (Matrix ι κ ℂ))

theorem sp3_map (f : Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ) (A B C : Matrix ι κ ℂ) :
    (sp3 A B C).map f = sp3 (f A) (f B) (f C) := by
  rw [sp3, sp3, Submodule.map_span]
  congr 1
  simp [Set.image_insert_eq]

theorem sp3_le {A B C : Matrix ι κ ℂ} {S : Submodule ℂ (Matrix ι κ ℂ)} (hA : A ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) : sp3 A B C ≤ S := by
  rw [sp3, Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem mem_sp3_1 (A B C : Matrix ι κ ℂ) : A ∈ sp3 A B C := Submodule.subset_span (by simp)
theorem mem_sp3_2 (A B C : Matrix ι κ ℂ) : B ∈ sp3 A B C := Submodule.subset_span (by simp)
theorem mem_sp3_3 (A B C : Matrix ι κ ℂ) : C ∈ sp3 A B C := Submodule.subset_span (by simp)

theorem cov_transfer {A B C : Matrix ι κ ℂ} {r : ℕ} (f : Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ)
    (g : Matrix ι' κ' ℂ →ₗ[ℂ] Matrix ι κ ℂ) (hg : ∀ M, IsR1 M → IsR1 (g M))
    (hA : g (f A) = A) (hB : g (f B) = B) (hC : g (f C) = C)
    (h : Cov (sp3 (f A) (f B) (f C)) r) : Cov (sp3 A B C) r := by
  have := h.map g hg
  rwa [sp3_map, hA, hB, hC] at this

end CovAPI

/-- `M ↦ P * M * Q` as a linear map -/
def lrMul {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι' ι ℂ) (Q : Matrix κ κ' ℂ) :
    Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ where
  toFun M := P * M * Q
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem lrMul_apply {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι' ι ℂ)
    (Q : Matrix κ κ' ℂ) (M : Matrix ι κ ℂ) : lrMul P Q M = P * M * Q := rfl

theorem isR1_lrMul {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι' ι ℂ)
    (Q : Matrix κ κ' ℂ) (M : Matrix ι κ ℂ) (h : IsR1 M) : IsR1 (lrMul P Q M) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨P *ᵥ a, b ᵥ* Q, by
    show P * vecMulVec a b * Q = _
    rw [mul_vecMulVec, vecMulVec_mul]⟩

/-- reindexing (submatrix by functions) as a linear map -/
def subL {ι κ ι' κ' : Type*} (e : ι' → ι) (f : κ' → κ) :
    Matrix ι κ ℂ →ₗ[ℂ] Matrix ι' κ' ℂ where
  toFun M := M.submatrix e f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subL_apply {ι κ ι' κ' : Type*} (e : ι' → ι) (f : κ' → κ) (M : Matrix ι κ ℂ) :
    subL e f M = M.submatrix e f := rfl

theorem isR1_subL {ι κ ι' κ' : Type*} (e : ι' → ι) (f : κ' → κ) (M : Matrix ι κ ℂ)
    (h : IsR1 M) : IsR1 (subL e f M) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨a ∘ e, b ∘ f, rfl⟩

/-- transposition as a linear map -/
def trL {ι κ : Type*} : Matrix ι κ ℂ →ₗ[ℂ] Matrix κ ι ℂ where
  toFun M := Mᵀ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trL_apply {ι κ : Type*} (M : Matrix ι κ ℂ) : trL M = Mᵀ := rfl

theorem isR1_trL {ι κ : Type*} (M : Matrix ι κ ℂ) (h : IsR1 M) : IsR1 (trL M) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨b, a, by ext i j; exact mul_comm _ _⟩

/-- extension by zero from a pair of subtypes -/
def extL {ι κ : Type*} (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q] :
    Matrix {x // p x} {y // q y} ℂ →ₗ[ℂ] Matrix ι κ ℂ where
  toFun M := Matrix.of fun i j => if h : p i ∧ q j then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  map_add' X Y := by ext i j; by_cases h : p i ∧ q j <;> simp [h]
  map_smul' c X := by ext i j; by_cases h : p i ∧ q j <;> simp [h]

theorem isR1_extL {ι κ : Type*} (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q]
    (M : Matrix {x // p x} {y // q y} ℂ) (h : IsR1 M) : IsR1 (extL p q M) := by
  obtain ⟨a, b, rfl⟩ := h
  refine ⟨fun i => if h : p i then a ⟨i, h⟩ else 0, fun j => if h : q j then b ⟨j, h⟩ else 0, ?_⟩
  ext i j
  simp only [extL, LinearMap.coe_mk, AddHom.coe_mk, vecMulVec_apply, Matrix.of_apply]
  by_cases hi : p i <;> by_cases hj : q j <;> simp [hi, hj]

/-- compression: a triple supported on `p × q` is covered if its compression is -/
theorem cov_compress {ι κ : Type*} (p : ι → Prop) (q : κ → Prop) [DecidablePred p]
    [DecidablePred q] {A B C : Matrix ι κ ℂ} {r : ℕ}
    (hA : ∀ i j, A i j ≠ 0 → p i ∧ q j) (hB : ∀ i j, B i j ≠ 0 → p i ∧ q j)
    (hC : ∀ i j, C i j ≠ 0 → p i ∧ q j)
    (h : Cov (sp3 (subL Subtype.val Subtype.val A : Matrix {x // p x} {y // q y} ℂ)
      (subL Subtype.val Subtype.val B) (subL Subtype.val Subtype.val C)) r) :
    Cov (sp3 A B C) r := by
  have key : ∀ M : Matrix ι κ ℂ, (∀ i j, M i j ≠ 0 → p i ∧ q j) →
      extL p q (subL Subtype.val Subtype.val M) = M := by
    intro M hM
    ext i j
    simp only [extL, subL, LinearMap.coe_mk, AddHom.coe_mk, submatrix_apply, Matrix.of_apply]
    split_ifs with hij
    · rfl
    · by_contra hne; exact hij (hM i j (Ne.symm hne))
  exact cov_transfer _ (extL p q) (isR1_extL p q) (key A hA) (key B hB) (key C hC) h

/-! ### The perturbation lemma (SMS10, Lemma 4.3) -/

theorem diag_sum {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    diagonal d = ∑ l, d l • vecMulVec (Pi.single l 1) (Pi.single l 1) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul, diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : i = l
    · subst hl; simp [Ne.symm hij]
    · simp [hl]

theorem L43Fin {n s : ℕ} (hs : s ≤ n) (D : Fin n → ℂ) (B C : Matrix (Fin n) (Fin n) ℂ)
    (j0 : Fin n) (hj0 : (j0 : ℕ) < s) (hD : D j0 = 0)
    (hgood : Good (B.submatrix (Fin.castLE hs) (Fin.castLE hs))
      (C.submatrix (Fin.castLE hs) (Fin.castLE hs))) :
    Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  classical
  obtain ⟨d₁, d₂, hd, hg⟩ := osl_all s n hs B C hgood
  obtain ⟨x, y, c, hB, hC⟩ := nice_of_good _ _ hg
  let E : Fin n → Matrix (Fin n) (Fin n) ℂ := fun l => vecMulVec (Pi.single l 1) (Pi.single l 1)
  let T₁ : Finset (Matrix (Fin n) (Fin n) ℂ) := (Finset.univ.erase j0).image E
  let T₂ : Finset (Matrix (Fin n) (Fin n) ℂ) := Finset.univ.image fun l => vecMulVec (x l) (y l)
  have hT₁ : T₁.card ≤ n - 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hT₂ : T₂.card ≤ n := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  have hn : 1 ≤ n := by have := j0.2; omega
  refine ⟨T₁ ∪ T₂, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨_, _, rfl⟩
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨_, _, rfl⟩
  · set W := Submodule.span ℂ ((T₁ ∪ T₂ : Finset _) : Set (Matrix (Fin n) (Fin n) ℂ))
    have hdiag : ∀ d : Fin n → ℂ, d j0 = 0 → diagonal d ∈ W := by
      intro d hd0
      rw [diag_sum, ← Finset.sum_erase Finset.univ (a := j0) (by simp [hd0])]
      apply Submodule.sum_mem
      intro l hl
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      left
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    have hnice : ∀ c' : Fin n → ℂ, ∑ l, c' l • vecMulVec (x l) (y l) ∈ W := by
      intro c'
      apply Submodule.sum_mem
      intro l _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      right
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
    apply sp3_le (hdiag D hD)
    · have : B = (B + diagonal d₁) - diagonal d₁ := by abel
      rw [this, hB]
      refine W.sub_mem ?_ (hdiag d₁ (hd j0 hj0).1)
      simpa using hnice 1
    · have : C = (C + diagonal d₂) - diagonal d₂ := by abel
      rw [this, hC]
      exact W.sub_mem (hnice c) (hdiag d₂ (hd j0 hj0).2)

theorem exists_equiv_core {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (core : Fin s → ι)
    (hcore : Function.Injective core) (hs : s ≤ Fintype.card ι) :
    ∃ e : ι ≃ Fin (Fintype.card ι), ∀ a, e (core a) = Fin.castLE hs a := by
  classical
  let p : ι → Prop := fun x => x ∈ Set.range core
  let e₁ : {x // p x} ≃ Fin s := (Equiv.ofInjective core hcore).symm
  have hc1 : Fintype.card {x // p x} = s := by rw [Fintype.card_congr e₁, Fintype.card_fin]
  have hc : Fintype.card {x // ¬ p x} = Fintype.card ι - s := by
    rw [Fintype.card_subtype_compl, hc1]
  let e₂ : {x // ¬ p x} ≃ Fin (Fintype.card ι - s) := Fintype.equivFinOfCardEq hc
  let e : ι ≃ Fin (Fintype.card ι) := (Equiv.sumCompl p).symm.trans ((Equiv.sumCongr e₁ e₂).trans
    (finSumFinEquiv.trans (finCongr (by omega))))
  refine ⟨e, fun a => ?_⟩
  have hp : p (core a) := ⟨a, rfl⟩
  simp only [e, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hp, Equiv.sumCongr_apply,
    Sum.map_inl, finSumFinEquiv_apply_left]
  ext
  have h1 : (Equiv.ofInjective core hcore).symm ⟨core a, hp⟩ = a :=
    Equiv.ofInjective_symm_apply hcore a
  simp [e₁, h1]

theorem L43 {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (core : Fin s → ι)
    (hcore : Function.Injective core) (D : ι → ℂ) (B C : Matrix ι ι ℂ) (j0 : Fin s)
    (hD : D (core j0) = 0) (hgood : Good (B.submatrix core core) (C.submatrix core core)) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  have hs : s ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective core hcore
  obtain ⟨e, he⟩ := exists_equiv_core s core hcore hs
  have he' : ∀ a, e.symm (Fin.castLE hs a) = core a := by
    intro a; rw [← he a, Equiv.symm_apply_apply]
  have hgg : ∀ M : Matrix ι ι ℂ, subL e e (subL e.symm e.symm M) = M := by
    intro M; ext i j; simp [subL_apply]
  refine cov_transfer (subL e.symm e.symm) (subL e e) (isR1_subL e e) (hgg _) (hgg _) (hgg _) ?_
  have hdg : subL e.symm e.symm (diagonal D) = diagonal (D ∘ e.symm) := by
    ext i j; simp [subL_apply, diagonal_apply]
  rw [hdg]
  have hsub : ∀ M : Matrix ι ι ℂ, (subL e.symm e.symm M).submatrix (Fin.castLE hs) (Fin.castLE hs)
      = M.submatrix core core := by
    intro M; ext i j; simp [subL_apply, he']
  refine L43Fin hs (D ∘ e.symm) _ _ (Fin.castLE hs j0) (by simp) (by simp [he', hD]) ?_
  rw [hsub, hsub]; exact hgood

/-! ### The case analysis -/

/-- the inductive statement -/
def Pn (n : ℕ) : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ],
    Fintype.card ι = n → Fintype.card κ = n → ∀ A B C : Matrix ι κ ℂ, Cov (sp3 A B C) (2 * n - 1)

theorem cov_pair {ι κ : Type*} (a₁ a₂ : ι → ℂ) (b₁ b₂ : κ → ℂ) :
    Cov (Submodule.span ℂ ({vecMulVec a₁ b₁, vecMulVec a₂ b₂} : Set (Matrix ι κ ℂ))) 2 := by
  have := cov_family (fun l : Fin 2 => ![a₁, a₂] l) (fun l : Fin 2 => ![b₁, b₂] l)
  rw [Fintype.card_fin] at this
  refine this.mono (Submodule.span_mono ?_)
  intro M hM
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem card_ne_sub {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) :
    Fintype.card {x // x ≠ j} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- (a): a nonzero entry in the zero block of `diagonal D` -/
theorem stepA {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (B C : Matrix ι ι ℂ) (i j : ι)
    (hi : D i = 0) (hj : D j = 0) (hB : B i j ≠ 0) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  set σ := Equiv.swap i j
  have hgg : ∀ M : Matrix ι ι ℂ, subL id σ (subL id σ M) = M := by
    intro M; ext a b; simp [subL_apply, σ]
  refine cov_transfer (subL id σ) (subL id σ) (isR1_subL id σ) (hgg _) (hgg _) (hgg _) ?_
  have hdg : subL id σ (diagonal D) = diagonal D := by
    ext a b
    simp only [subL_apply, submatrix_apply, id, diagonal_apply, σ]
    by_cases hb1 : b = i
    · subst hb1; rw [Equiv.swap_apply_left]
      by_cases ha : a = j
      · subst ha; simp [hi, hj]
      · by_cases hab : a = b
        · subst hab; simp [hi]
        · simp [ha, hab]
    · by_cases hb2 : b = j
      · subst hb2; rw [Equiv.swap_apply_right]
        by_cases ha : a = i
        · subst ha; simp [hi, hj]
        · by_cases hab : a = b
          · subst hab; simp [hj]
          · simp [ha, hab]
      · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
  rw [hdg]
  refine L43 1 (fun _ => i) (fun a b _ => Subsingleton.elim a b) D _ _ 0 hi (core1 _ _ ?_)
  simp only [subL_apply, submatrix_apply, id, σ, Equiv.swap_apply_left]
  exact hB

/-- (z): row `j` vanishes; peel column `j` at cost two -/
theorem stepZ {n : ℕ} (hn : 2 ≤ n) (IH : Pn (n - 1)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (D : ι → ℂ) (B C : Matrix ι ι ℂ) (j : ι) (hj : D j = 0)
    (hrow : ∀ l, B j l = 0 ∧ C j l = 0) : Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  classical
  set RB := vecMulVec (fun i => B i j) (Pi.single j (1 : ℂ))
  set RC := vecMulVec (fun i => C i j) (Pi.single j (1 : ℂ))
  have h1 := cov_pair (fun i => B i j) (fun i => C i j) (Pi.single j (1 : ℂ)) (Pi.single j 1)
  have hsupp : ∀ M : Matrix ι ι ℂ, (∀ l, M j l = 0) → ∀ a b,
      (M - vecMulVec (fun i => M i j) (Pi.single j (1 : ℂ))) a b ≠ 0 → a ≠ j ∧ b ≠ j := by
    intro M hM a b hab
    simp only [Matrix.sub_apply, vecMulVec_apply, Pi.single_apply] at hab
    constructor
    · rintro rfl; apply hab; simp [hM]
    · rintro rfl; apply hab; simp
  have h2 : Cov (sp3 (diagonal D) (B - RB) (C - RC)) (2 * (n - 1) - 1) := by
    apply cov_compress (fun x => x ≠ j) (fun x => x ≠ j)
    · intro a b hab
      simp only [diagonal_apply] at hab
      split_ifs at hab with h
      · subst h; exact ⟨fun h' => hab (h' ▸ hj), fun h' => hab (h' ▸ hj)⟩
      · exact absurd rfl hab
    · exact hsupp B (fun l => (hrow l).1)
    · exact hsupp C (fun l => (hrow l).2)
    · exact IH _ _ (by rw [card_ne_sub, hι]) (by rw [card_ne_sub, hι]) _ _ _
  refine ((h1.sup h2).mono ?_).mono_r (by omega)
  apply sp3_le
  · exact Submodule.mem_sup_right (mem_sp3_1 _ _ _)
  · have h := Submodule.add_mem_sup
      (Submodule.subset_span (by simp [RB]) : RB ∈ Submodule.span ℂ ({RB, RC} : Set _))
      (mem_sp3_2 (diagonal D) (B - RB) (C - RC))
    simpa using h
  · have h := Submodule.add_mem_sup
      (Submodule.subset_span (by simp [RC]) : RC ∈ Submodule.span ℂ ({RB, RC} : Set _))
      (mem_sp3_3 (diagonal D) (B - RB) (C - RC))
    simpa using h

theorem sp3_swap {ι κ : Type*} (A B C : Matrix ι κ ℂ) : sp3 A B C = sp3 A C B := by
  unfold sp3; congr 1; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem stepB_core {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (X Y : Matrix ι ι ℂ)
    (p j : ι) (hpj : p ≠ j) (hj : D j = 0) (hX : X j j = 0) (hY : Y j j = 0)
    (h1 : X p j * X j p ≠ 0) (h2 : X p j * Y j p ≠ Y p j * X j p) :
    Cov (sp3 (diagonal D) X Y) (2 * Fintype.card ι - 1) := by
  have hinj : Function.Injective ![p, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [hpj, Ne.symm hpj]
  exact L43 2 ![p, j] hinj D X Y 1 (by simpa using hj)
    (core2 _ _ (by simpa using hX) (by simpa using hY) (by simpa using h1) (by simpa using h2))

theorem stepB_pair {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (B C : Matrix ι ι ℂ)
    (p j : ι) (hpj : p ≠ j) (hj : D j = 0) (hB : B j j = 0) (hC : C j j = 0)
    (hdet : C p j * B j p ≠ B p j * C j p) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  by_cases hc1 : B p j * B j p ≠ 0
  · exact stepB_core D B C p j hpj hj hB hC hc1 (fun h => hdet (by linear_combination -h))
  by_cases hc2 : C p j * C j p ≠ 0
  · rw [sp3_swap]
    exact stepB_core D C B p j hpj hj hC hB hc2 hdet
  push_neg at hc1 hc2
  have hmono : sp3 (diagonal D) B C ≤ sp3 (diagonal D) (B + C) C := by
    apply sp3_le (mem_sp3_1 _ _ _) _ (mem_sp3_3 _ _ _)
    have := Submodule.sub_mem _ (mem_sp3_2 (diagonal D) (B + C) C) (mem_sp3_3 (diagonal D) (B + C) C)
    simpa using this
  refine Cov.mono hmono (stepB_core D (B + C) C p j hpj hj (by simp [hB, hC]) hC ?_ ?_)
  · simp only [Matrix.add_apply]
    rcases mul_eq_zero.mp hc1 with h | h <;> rcases mul_eq_zero.mp hc2 with h' | h'
    · rw [h, h'] at hdet; simp at hdet
    · rw [h, h', zero_add, add_zero]
      exact mul_ne_zero (left_ne_zero_of_mul (by rw [h] at hdet; simpa using hdet))
        (right_ne_zero_of_mul (by rw [h] at hdet; simpa using hdet))
    · rw [h, h', add_zero, zero_add]
      have : B p j * C j p ≠ 0 := by rw [h] at hdet; simpa [eq_comm] using hdet
      exact this
    · rw [h, h'] at hdet; simp at hdet
  · simp only [Matrix.add_apply]
    intro h
    apply hdet
    linear_combination -h

theorem conj_apply {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (t : ℂ) (p q : ι)
    (a b : ι) :
    ((1 + t • single p q (1 : ℂ)) * M * (1 - t • single p q (1 : ℂ))) a b
      = M a b + t * (if a = p then M q b else 0) - t * (if b = q then M a p else 0)
        - t * t * (if a = p then (if b = q then M q p else 0) else 0) := by
  have e1 : ∀ (N : Matrix ι ι ℂ) (a b : ι), (single p q (1 : ℂ) * N) a b
      = if a = p then N q b else 0 := by
    intro N a b
    by_cases ha : a = p
    · subst ha; simp [single_mul_apply_same]
    · simp [single_mul_apply_of_ne (1 : ℂ) p q a b ha N, ha]
  have e2 : ∀ (N : Matrix ι ι ℂ) (a b : ι), (N * single p q (1 : ℂ)) a b
      = if b = q then N a p else 0 := by
    intro N a b
    by_cases hb : b = q
    · subst hb; simp [mul_single_apply_same]
    · simp [mul_single_apply_of_ne (1 : ℂ) p q a b hb N, hb]
  have hexp : (1 + t • single p q (1 : ℂ)) * M * (1 - t • single p q (1 : ℂ))
      = M + t • (single p q 1 * M) - t • (M * single p q 1)
        - (t * t) • (single p q 1 * (M * single p q 1)) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    module
  rw [hexp]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]

theorem stepB {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℂ) (hD01 : ∀ i, D i = 0 ∨ D i = 1)
    (B C : Matrix ι ι ℂ) (hZZ : ∀ a b, D a = 0 → D b = 0 → B a b = 0 ∧ C a b = 0) (j : ι)
    (hj : D j = 0) (hind : ∀ c₁ c₂ : ℂ, (∀ i, c₁ * B i j + c₂ * C i j = 0) → c₁ = 0 ∧ c₂ = 0)
    (p : ι) (hp : B j p ≠ 0 ∨ C j p ≠ 0) :
    Cov (sp3 (diagonal D) B C) (2 * Fintype.card ι - 1) := by
  have hDp : D p = 1 := by
    rcases hD01 p with h | h
    · exfalso
      obtain ⟨h1, h2⟩ := hZZ j p hj h
      rcases hp with h3 | h3
      · exact h3 h1
      · exact h3 h2
    · exact h
  have hpj : p ≠ j := by
    intro h; rw [h, hj] at hDp; norm_num at hDp
  set w : ι → ℂ := fun i => B j p * C i j - C j p * B i j with hw
  have hwex : ∃ q, w q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hind (-C j p) (B j p) (fun i => by
      have := hcon i; simp only [hw] at this; linear_combination this)
    rcases hp with h3 | h3
    · exact h3 h2
    · exact h3 (neg_eq_zero.mp h1)
  obtain ⟨t, q, hqp, htq, hwt⟩ : ∃ (t : ℂ) (q : ι), q ≠ p ∧ (t = 0 ∨ (D q = 1 ∧ q ≠ j)) ∧
      w p + t * w q ≠ 0 := by
    by_cases hwp : w p ≠ 0
    · exact ⟨0, j, Ne.symm hpj, Or.inl rfl, by simpa using hwp⟩
    push_neg at hwp
    obtain ⟨q, hq⟩ := hwex
    have hqp : q ≠ p := fun h => hq (h ▸ hwp)
    have hDq : D q = 1 := by
      rcases hD01 q with h | h
      · exfalso; apply hq
        simp only [hw, (hZZ q j h hj).1, (hZZ q j h hj).2, mul_zero, sub_zero]
      · exact h
    have hqj : q ≠ j := fun h => by rw [h, hj] at hDq; norm_num at hDq
    exact ⟨1, q, hqp, Or.inr ⟨hDq, hqj⟩, by rw [hwp]; simpa using hq⟩
  set E := single p q (1 : ℂ)
  have hEE : E * E = 0 := single_mul_single_of_ne (1 : ℂ) p q p hqp 1
  set G := 1 + t • E
  set Gi := 1 - t • E
  have hGGi : G * Gi = 1 := by
    simp only [G, Gi, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hEE, smul_zero]
    abel
  have hGiG : Gi * G = 1 := by
    simp only [G, Gi, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hEE, smul_zero]
    abel
  have hgg : ∀ M : Matrix ι ι ℂ, lrMul Gi G (lrMul G Gi M) = M := by
    intro M
    simp only [lrMul_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul, Matrix.mul_assoc, hGiG,
      Matrix.mul_one]
  refine cov_transfer (lrMul G Gi) (lrMul Gi G) (isR1_lrMul Gi G) (hgg _) (hgg _) (hgg _) ?_
  have hcomm : t • E * diagonal D = diagonal D * (t • E) := by
    ext a b
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, E,
      mul_diagonal, diagonal_mul, single_apply]
    rcases htq with h | ⟨h, _⟩
    · simp [h]
    · by_cases hab : p = a ∧ q = b
      · obtain ⟨rfl, rfl⟩ := hab; simp [hDp, h]
      · simp [hab]
  have hGD : G * diagonal D = diagonal D * G := by
    simp only [G, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]
  have hdg : lrMul G Gi (diagonal D) = diagonal D := by
    rw [lrMul_apply, hGD, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  rw [hdg]
  have hq' : t * (if j = q then (1 : ℂ) else 0) = 0 := by
    rcases htq with h | ⟨_, h⟩
    · simp [h]
    · simp [Ne.symm h]
  have entry : ∀ M : Matrix ι ι ℂ, lrMul G Gi M p j = M p j + t * M q j ∧
      lrMul G Gi M j p = M j p ∧ lrMul G Gi M j j = M j j := by
    intro M
    simp only [lrMul_apply, G, Gi, E, conj_apply]
    refine ⟨?_, ?_, ?_⟩
    · rcases htq with h | ⟨_, h⟩
      · simp [h]
      · simp [Ne.symm h]
    · simp [Ne.symm hpj, Ne.symm hqp]
    · rcases htq with h | ⟨_, h⟩
      · simp [h, Ne.symm hpj]
      · simp [Ne.symm h, Ne.symm hpj]
  obtain ⟨b1, b2, b3⟩ := entry B
  obtain ⟨c1, c2, c3⟩ := entry C
  refine stepB_pair D _ _ p j hpj hj (by rw [b3]; exact (hZZ j j hj hj).1)
    (by rw [c3]; exact (hZZ j j hj hj).2) ?_
  rw [b1, b2, c1, c2]
  intro h
  apply hwt
  simp only [hw]
  linear_combination h

/-- (c): every column and row of the zero block is a rank-one fibre; peel them all -/
theorem stepC {n : ℕ} (IH : ∀ m < n, Pn m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (D : ι → ℂ) (hz : ∃ i, D i = 0) (hnz : ∃ i, D i ≠ 0)
    (B C : Matrix ι ι ℂ) (hZZ : ∀ a b, D a = 0 → D b = 0 → B a b = 0 ∧ C a b = 0)
    (v : ι → ι → ℂ) (cv₁ cv₂ : ι → ℂ)
    (hv : ∀ j, D j = 0 → ∀ i, B i j = cv₁ j * v j i ∧ C i j = cv₂ j * v j i)
    (w : ι → ι → ℂ) (cw₁ cw₂ : ι → ℂ)
    (hw : ∀ i, D i = 0 → ∀ l, B i l = cw₁ i * w i l ∧ C i l = cw₂ i * w i l) :
    Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  classical
  set Zf := Finset.univ.filter (fun j => D j = 0) with hZf
  let colR : ι → Matrix ι ι ℂ := fun j => vecMulVec (v j) (Pi.single j 1)
  let rowR : ι → Matrix ι ι ℂ := fun i => vecMulVec (Pi.single i 1) (w i)
  set T := Zf.image colR ∪ Zf.image rowR with hT
  have hTc : Cov (Submodule.span ℂ (T : Set (Matrix ι ι ℂ))) (2 * Zf.card) := by
    refine ⟨T, (Finset.card_union_le _ _).trans ?_, ?_, le_rfl⟩
    · have h1 := Finset.card_image_le (s := Zf) (f := colR)
      have h2 := Finset.card_image_le (s := Zf) (f := rowR)
      omega
    · intro M hM
      rcases Finset.mem_union.mp hM with h | h
      · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨_, _, rfl⟩
      · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨_, _, rfl⟩
  let mask : Matrix ι ι ℂ → Matrix ι ι ℂ := fun M => Matrix.of fun a b =>
    if D a ≠ 0 ∧ D b ≠ 0 then M a b else 0
  have hdec : ∀ (M : Matrix ι ι ℂ) (c₁ c₂ : ι → ℂ),
      (∀ j, D j = 0 → ∀ i, M i j = c₁ j * v j i) → (∀ i, D i = 0 → ∀ l, M i l = c₂ i * w i l) →
      (∀ a b, D a = 0 → D b = 0 → M a b = 0) →
      M - mask M = ∑ j ∈ Zf, c₁ j • colR j + ∑ i ∈ Zf, c₂ i • rowR i := by
    intro M c₁ c₂ h1 h2 h3
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, colR, rowR, vecMulVec_apply, Pi.single_apply, mask, Matrix.of_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [hZf, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : D a = 0 <;> by_cases hb : D b = 0
    · have e1 := h1 b hb a
      have e2 := h2 a ha b
      have e3 := h3 a b ha hb
      simp [ha, hb, h3 a b ha hb]
      linear_combination e1 + e2 - 2 * e3
    · simp [ha, hb, h2 a ha b]
    · simp [ha, hb, h1 b hb a]
    · simp [ha, hb]
  have hmem : ∀ (c₁ c₂ : ι → ℂ), ∑ j ∈ Zf, c₁ j • colR j + ∑ i ∈ Zf, c₂ i • rowR i ∈
      Submodule.span ℂ (T : Set (Matrix ι ι ℂ)) := by
    intro c₁ c₂
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    · apply Submodule.subset_span
      simp only [hT, Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inl (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    · apply Submodule.subset_span
      simp only [hT, Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hBd := hdec B cv₁ cw₁ (fun j hj i => (hv j hj i).1) (fun i hi l => (hw i hi l).1)
    (fun a b ha hb => (hZZ a b ha hb).1)
  have hCd := hdec C cv₂ cw₂ (fun j hj i => (hv j hj i).2) (fun i hi l => (hw i hi l).2)
    (fun a b ha hb => (hZZ a b ha hb).2)
  -- sizes
  have hZc : Fintype.card {x // D x = 0} = Zf.card := by
    rw [Fintype.card_subtype]
  have hNc : Fintype.card {x // D x ≠ 0} = n - Zf.card := by
    rw [← hι, ← hZc]; exact Fintype.card_subtype_compl _
  have hZpos : 1 ≤ Zf.card := by
    obtain ⟨i, hi⟩ := hz
    exact Finset.card_pos.mpr ⟨i, by simp [hZf, hi]⟩
  have hNpos : 1 ≤ Fintype.card {x // D x ≠ 0} := by
    obtain ⟨i, hi⟩ := hnz
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  have hZle : Zf.card ≤ n := by
    rw [← hι]; exact Finset.card_le_univ _
  have h2 : Cov (sp3 (diagonal D) (mask B) (mask C)) (2 * (n - Zf.card) - 1) := by
    apply cov_compress (fun x => D x ≠ 0) (fun x => D x ≠ 0)
    · intro a b hab
      simp only [diagonal_apply] at hab
      split_ifs at hab with h
      · subst h; exact ⟨hab, hab⟩
      · exact absurd rfl hab
    · intro a b hab
      simp only [mask, Matrix.of_apply] at hab
      split_ifs at hab with h
      · exact h
      · exact absurd rfl hab
    · intro a b hab
      simp only [mask, Matrix.of_apply] at hab
      split_ifs at hab with h
      · exact h
      · exact absurd rfl hab
    · exact IH _ (by omega) _ _ hNc hNc _ _ _
  refine ((hTc.sup h2).mono ?_).mono_r (by omega)
  apply sp3_le
  · exact Submodule.mem_sup_right (mem_sp3_1 _ _ _)
  · have h := Submodule.add_mem_sup (hmem cv₁ cw₁) (mem_sp3_2 (diagonal D) (mask B) (mask C))
    rw [← hBd] at h; simpa using h
  · have h := Submodule.add_mem_sup (hmem cv₂ cw₂) (mem_sp3_3 (diagonal D) (mask B) (mask C))
    rw [← hCd] at h; simpa using h

theorem dep_vec {ι : Type} (x y : ι → ℂ)
    (h : ¬ ∀ c₁ c₂ : ℂ, (∀ i, c₁ * x i + c₂ * y i = 0) → c₁ = 0 ∧ c₂ = 0) :
    ∃ (v : ι → ℂ) (a b : ℂ), ∀ i, x i = a * v i ∧ y i = b * v i := by
  push_neg at h
  obtain ⟨c₁, c₂, hc, hne⟩ := h
  by_cases hc2 : c₂ = 0
  · have hc1 : c₁ ≠ 0 := fun h => hne h hc2
    refine ⟨y, 0, 1, fun i => ⟨?_, by ring⟩⟩
    have := hc i
    rw [hc2, zero_mul, add_zero] at this
    rw [zero_mul]
    exact (mul_eq_zero.mp this).resolve_left hc1
  · refine ⟨x, 1, -(c₁ / c₂), fun i => ⟨by ring, ?_⟩⟩
    have := hc i
    field_simp
    linear_combination this

theorem trL_diag {ι : Type} [DecidableEq ι] (D : ι → ℂ) : trL (diagonal D) = diagonal D := by
  rw [trL_apply, diagonal_transpose]

theorem cov_transpose {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → ℂ} {B C : Matrix ι ι ℂ}
    {r : ℕ} (h : Cov (sp3 (diagonal D) Bᵀ Cᵀ) r) : Cov (sp3 (diagonal D) B C) r := by
  refine cov_transfer trL trL isR1_trL (by simp [trL_apply]) (by simp [trL_apply])
    (by simp [trL_apply]) ?_
  rw [trL_diag]; exact h

theorem core_step {n : ℕ} (IH : ∀ m < n, Pn m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (D : ι → ℂ) (hD01 : ∀ i, D i = 0 ∨ D i = 1) (hz : ∃ i, D i = 0)
    (hnz : ∃ i, D i = 1) (B C : Matrix ι ι ℂ) : Cov (sp3 (diagonal D) B C) (2 * n - 1) := by
  obtain ⟨i₀, hi₀⟩ := hz
  obtain ⟨i₁, hi₁⟩ := hnz
  have hn2 : 2 ≤ n := by
    rw [← hι]
    have : 1 < Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i₀, i₁, fun h => by
      rw [h, hi₁] at hi₀; norm_num at hi₀⟩
    omega
  have hnz' : ∃ i, D i ≠ 0 := ⟨i₁, by rw [hi₁]; norm_num⟩
  by_cases ha : ∃ i j, D i = 0 ∧ D j = 0 ∧ (B i j ≠ 0 ∨ C i j ≠ 0)
  · obtain ⟨i, j, hi, hj, hB | hC⟩ := ha
    · rw [← hι]; exact stepA D B C i j hi hj hB
    · rw [← hι, sp3_swap]; exact stepA D C B i j hi hj hC
  have hZZ : ∀ a b, D a = 0 → D b = 0 → B a b = 0 ∧ C a b = 0 := by
    intro a b hA hB'
    by_contra hc
    apply ha
    refine ⟨a, b, hA, hB', ?_⟩
    by_contra hc'
    push_neg at hc'
    exact hc hc'
  have IH1 : Pn (n - 1) := IH _ (by omega)
  by_cases hzr : ∃ j, D j = 0 ∧ ∀ l, B j l = 0 ∧ C j l = 0
  · obtain ⟨j, hj, hrow⟩ := hzr
    exact stepZ hn2 IH1 hι D B C j hj hrow
  by_cases hzc : ∃ j, D j = 0 ∧ ∀ l, B l j = 0 ∧ C l j = 0
  · obtain ⟨j, hj, hcol⟩ := hzc
    exact cov_transpose (stepZ hn2 IH1 hι D Bᵀ Cᵀ j hj (fun l => hcol l))
  by_cases hbc : ∃ j, D j = 0 ∧
      ∀ c₁ c₂ : ℂ, (∀ i, c₁ * B i j + c₂ * C i j = 0) → c₁ = 0 ∧ c₂ = 0
  · obtain ⟨j, hj, hind⟩ := hbc
    have : ∃ l, B j l ≠ 0 ∨ C j l ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hzr ⟨j, hj, hcon⟩
    obtain ⟨l, hl⟩ := this
    rw [← hι]
    exact stepB D hD01 B C hZZ j hj hind l hl
  by_cases hbr : ∃ j, D j = 0 ∧
      ∀ c₁ c₂ : ℂ, (∀ i, c₁ * B j i + c₂ * C j i = 0) → c₁ = 0 ∧ c₂ = 0
  · obtain ⟨j, hj, hind⟩ := hbr
    have : ∃ l, B l j ≠ 0 ∨ C l j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hzc ⟨j, hj, hcon⟩
    obtain ⟨l, hl⟩ := this
    rw [← hι]
    refine cov_transpose (stepB D hD01 Bᵀ Cᵀ (fun a b ha hb => ?_) j hj (fun c₁ c₂ h => hind c₁ c₂ h) l hl)
    exact ⟨(hZZ b a hb ha).1, (hZZ b a hb ha).2⟩
  have hcolv : ∀ j, ∃ (v : ι → ℂ) (a b : ℂ), D j = 0 → ∀ i, B i j = a * v i ∧ C i j = b * v i := by
    intro j
    by_cases hj : D j = 0
    · obtain ⟨v, a, b, h⟩ := dep_vec (fun i => B i j) (fun i => C i j) (fun h => hbc ⟨j, hj, h⟩)
      exact ⟨v, a, b, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hj⟩
  have hrowv : ∀ i, ∃ (w : ι → ℂ) (a b : ℂ), D i = 0 → ∀ l, B i l = a * w l ∧ C i l = b * w l := by
    intro i
    by_cases hi : D i = 0
    · obtain ⟨w, a, b, h⟩ := dep_vec (fun l => B i l) (fun l => C i l) (fun h => hbr ⟨i, hi, h⟩)
      exact ⟨w, a, b, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hi⟩
  choose v cv₁ cv₂ hv using hcolv
  choose w cw₁ cw₂ hw using hrowv
  exact stepC IH hι D ⟨i₀, hi₀⟩ hnz' B C hZZ v cv₁ cv₂ hv w cw₁ cw₂ hw

theorem sing_comb {ι : Type} [Fintype ι] [DecidableEq ι] (M₁ M₂ : Matrix ι ι ℂ)
    (hn : 0 < Fintype.card ι) :
    ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ (c₁ • M₁ + c₂ • M₂).det = 0 := by
  by_cases h : M₂.det = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, by simpa using h⟩
  have : Nonempty ι := Fintype.card_pos_iff.mp hn
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (toLin' (M₂⁻¹ * M₁))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨1, -μ, Or.inl one_ne_zero, ?_⟩
  apply exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv.2, ?_⟩
  have h1 := hv.apply_eq_smul
  rw [toLin'_apply, ← mulVec_mulVec] at h1
  have h2 : M₁ *ᵥ v = μ • (M₂ *ᵥ v) := by
    have := congrArg (fun x => M₂ *ᵥ x) h1
    simp only [mulVec_mulVec, mulVec_smul] at this
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mul] at this
    exact this
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_smul, h2, neg_smul, add_neg_cancel]

theorem normal_form {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ∃ P Q : Matrix ι ι ℂ, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ D : ι → ℂ, (∀ i, D i = 0 ∨ D i = 1) ∧
      P * A * Q = diagonal D := by
  obtain ⟨L, L', D₀, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A
  let s : ι → ℂ := fun i => if D₀ i = 0 then 1 else (D₀ i)⁻¹
  have hunit : ∀ L : List (TransvectionStruct ι ℂ), IsUnit (L.map TransvectionStruct.toMatrix).prod := by
    intro L
    apply List.prod_isUnit
    intro m hm
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hm
    exact (isUnit_iff_isUnit_det _).mpr (by rw [TransvectionStruct.det]; exact isUnit_one)
  refine ⟨diagonal s * (L.map TransvectionStruct.toMatrix).prod, (L'.map TransvectionStruct.toMatrix).prod,
    ?_, (isUnit_iff_isUnit_det _).mp (hunit L'), fun i => s i * D₀ i, ?_, ?_⟩
  · rw [det_mul]
    refine IsUnit.mul ?_ ((isUnit_iff_isUnit_det _).mp (hunit L))
    rw [det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    simp only [s]
    split_ifs with h0
    · exact one_ne_zero
    · exact inv_ne_zero h0
  · intro i
    simp only [s]
    split_ifs with h0
    · left; simp [h0]
    · right; exact inv_mul_cancel₀ h0
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A, h, diagonal_mul_diagonal]

theorem cov_single {ι κ : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι κ ℂ) :
    Cov (Submodule.span ℂ {M}) (Fintype.card ι) := by
  refine (cov_family (fun i => Pi.single i (1 : ℂ)) (fun i => M i)).mono ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have : M = ∑ i, vecMulVec (Pi.single i (1 : ℂ)) (M i) := by
    ext a b
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  have hsum : ∑ i, vecMulVec (Pi.single i (1 : ℂ)) (M i) ∈ Submodule.span ℂ
      (Set.range fun i => vecMulVec (Pi.single i (1 : ℂ)) (M i)) :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, rfl⟩
  rw [← this] at hsum
  exact hsum

theorem pencil_span {ι κ : Type} (M₁ M₂ : Matrix ι κ ℂ) (c₁ c₂ : ℂ) (hc : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    ∃ M, M₁ ∈ Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M} : Set (Matrix ι κ ℂ)) ∧
      M₂ ∈ Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M} : Set (Matrix ι κ ℂ)) := by
  set S := Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M₂} : Set (Matrix ι κ ℂ))
  by_cases h1 : c₁ ≠ 0
  · refine ⟨M₂, ?_, Submodule.subset_span (by simp)⟩
    have hA : c₁ • M₁ + c₂ • M₂ ∈ S := Submodule.subset_span (by simp)
    have hB : M₂ ∈ S := Submodule.subset_span (by simp)
    have := S.smul_mem c₁⁻¹ (S.sub_mem hA (S.smul_mem c₂ hB))
    rwa [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h1, one_smul] at this
  · push_neg at h1
    have h2 : c₂ ≠ 0 := hc.resolve_left (by simpa using h1)
    refine ⟨M₁, Submodule.subset_span (by simp), ?_⟩
    have hA : c₁ • M₁ + c₂ • M₂ ∈ Submodule.span ℂ ({c₁ • M₁ + c₂ • M₂, M₁} : Set _) :=
      Submodule.subset_span (by simp)
    convert Submodule.smul_mem _ c₂⁻¹ hA using 1
    rw [h1, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem span_pair_le {ι κ : Type} {X Y : Matrix ι κ ℂ} {S : Submodule ℂ (Matrix ι κ ℂ)}
    (hX : X ∈ S) (hY : Y ∈ S) : Submodule.span ℂ ({X, Y} : Set (Matrix ι κ ℂ)) ≤ S := by
  rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hX, hY⟩

theorem reduce3 {ι : Type} [Fintype ι] [DecidableEq ι] (A₁ A₂ A₃ : Matrix ι ι ℂ)
    (hn : 0 < Fintype.card ι) :
    (∃ N : Matrix ι ι ℂ, sp3 A₁ A₂ A₃ ≤ Submodule.span ℂ {N}) ∨
      ∃ A B C : Matrix ι ι ℂ, A.det = 0 ∧ A ≠ 0 ∧ sp3 A₁ A₂ A₃ ≤ sp3 A B C := by
  obtain ⟨c₁, c₂, hc, hdet⟩ := sing_comb A₁ A₂ hn
  obtain ⟨M, h1, h2⟩ := pencil_span A₁ A₂ c₁ c₂ hc
  by_cases hA : c₁ • A₁ + c₂ • A₂ = 0
  · rw [hA] at h1 h2
    have hsM : Submodule.span ℂ ({0, M} : Set (Matrix ι ι ℂ)) ≤ Submodule.span ℂ {M} :=
      span_pair_le (Submodule.zero_mem _) (Submodule.subset_span (by simp))
    obtain ⟨d₁, d₂, hd, hdet'⟩ := sing_comb A₃ M hn
    obtain ⟨M', g1, g2⟩ := pencil_span A₃ M d₁ d₂ hd
    by_cases hA' : d₁ • A₃ + d₂ • M = 0
    · left
      rw [hA'] at g1 g2
      have hs' : Submodule.span ℂ ({0, M'} : Set (Matrix ι ι ℂ)) ≤ Submodule.span ℂ {M'} :=
        span_pair_le (Submodule.zero_mem _) (Submodule.subset_span (by simp))
      have hM : M ∈ Submodule.span ℂ {M'} := hs' g2
      have hMM : Submodule.span ℂ {M} ≤ Submodule.span ℂ {M'} := by
        rw [Submodule.span_le, Set.singleton_subset_iff]; exact hM
      exact ⟨M', sp3_le (hMM (hsM h1)) (hMM (hsM h2)) (hs' g1)⟩
    · right
      refine ⟨d₁ • A₃ + d₂ • M, M', 0, hdet', hA', ?_⟩
      have hP : Submodule.span ℂ ({d₁ • A₃ + d₂ • M, M'} : Set (Matrix ι ι ℂ)) ≤
          sp3 (d₁ • A₃ + d₂ • M) M' 0 := span_pair_le (mem_sp3_1 _ _ _) (mem_sp3_2 _ _ _)
      have hMM : Submodule.span ℂ {M} ≤ sp3 (d₁ • A₃ + d₂ • M) M' 0 := by
        rw [Submodule.span_le, Set.singleton_subset_iff]; exact hP g2
      exact sp3_le (hMM (hsM h1)) (hMM (hsM h2)) (hP g1)
  · right
    refine ⟨c₁ • A₁ + c₂ • A₂, M, A₃, hdet, hA, ?_⟩
    have hP : Submodule.span ℂ ({c₁ • A₁ + c₂ • A₂, M} : Set (Matrix ι ι ℂ)) ≤
        sp3 (c₁ • A₁ + c₂ • A₂) M A₃ := span_pair_le (mem_sp3_1 _ _ _) (mem_sp3_2 _ _ _)
    exact sp3_le (hP h1) (hP h2) (mem_sp3_3 _ _ _)

theorem sq_main {n : ℕ} (IH : ∀ m < n, Pn m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = n) (A₁ A₂ A₃ : Matrix ι ι ℂ) : Cov (sp3 A₁ A₂ A₃) (2 * n - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (hι.trans h0)
    refine ⟨∅, by simp, by simp, ?_⟩
    intro x _
    have : x = 0 := by ext i; exact (IsEmpty.false i).elim
    rw [this]; exact Submodule.zero_mem _
  rcases reduce3 A₁ A₂ A₃ (by omega) with ⟨N, hN⟩ | ⟨A, B, C, hdet, hA0, hS⟩
  · exact ((cov_single N).mono hN).mono_r (by omega)
  refine Cov.mono hS ?_
  obtain ⟨P, Q, hP, hQ, D, hD01, hPAQ⟩ := normal_form A
  have hgg : ∀ M : Matrix ι ι ℂ, lrMul P⁻¹ Q⁻¹ (lrMul P Q M) = M := by
    intro M
    simp only [lrMul_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hP, Matrix.one_mul,
      Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.mul_one]
  refine cov_transfer (lrMul P Q) (lrMul P⁻¹ Q⁻¹) (isR1_lrMul _ _) (hgg _) (hgg _) (hgg _) ?_
  rw [lrMul_apply P Q A, hPAQ]
  have hz : ∃ i, D i = 0 := by
    have : (diagonal D).det = 0 := by rw [← hPAQ, det_mul, det_mul, hdet]; ring
    rw [det_diagonal, Finset.prod_eq_zero_iff] at this
    obtain ⟨i, -, hi⟩ := this
    exact ⟨i, hi⟩
  have hnz : ∃ i, D i = 1 := by
    by_contra hcon
    push_neg at hcon
    have hD0 : diagonal D = 0 := by
      ext i j
      rcases hD01 i with h | h
      · simp [diagonal_apply, h]
      · exact absurd h (hcon i)
    apply hA0
    rw [← hgg A, lrMul_apply P Q A, hPAQ, hD0, lrMul_apply, Matrix.mul_zero, Matrix.zero_mul]
  exact core_step IH hι D hD01 hz hnz _ _

theorem main (n : ℕ) : Pn n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ι κ _ _ _ _ hι hκ A B C
    have e : κ ≃ ι := Fintype.equivOfCardEq (by rw [hκ, hι])
    have hgg : ∀ M : Matrix ι κ ℂ, subL id e (subL id e.symm M) = M := by
      intro M; ext i j; simp [subL_apply]
    exact cov_transfer (subL id e.symm) (subL id e) (isR1_subL id e) (hgg _) (hgg _) (hgg _)
      (sq_main IH hι _ _ _)

/-! ### From holors to slices (adapted from the `Bridge` section of
`proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean`) -/

section Bridge

variable {n : ℕ}

/-- The index `(i, j, k)` of an `n × n × 3` holor. -/
def ix (i j : Fin n) (k : Fin 3) : HolorIndex [n, n, 3] :=
  ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩

theorem ix_surjective (t : HolorIndex [n, n, 3]) : ∃ i j k, t = ix i j k := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

/-- entry `(i, j, k)` -/
def ev (T : Holor ℂ [n, n, 3]) (i j : Fin n) (k : Fin 3) : ℂ := T (ix i j k)

theorem holor_ext {T T' : Holor ℂ [n, n, 3]} (h : ∀ i j k, ev T i j k = ev T' i j k) :
    T = T' := by
  funext t
  obtain ⟨i, j, k, rfl⟩ := ix_surjective t
  exact h i j k

theorem ev_add (T T' : Holor ℂ [n, n, 3]) (i j : Fin n) (k : Fin 3) :
    ev (T + T') i j k = ev T i j k + ev T' i j k := rfl

theorem ev_sum {β : Type*} (s : Finset β) (f : β → Holor ℂ [n, n, 3]) (i j : Fin n) (k : Fin 3) :
    ev (∑ l ∈ s, f l) i j k = ∑ l ∈ s, ev (f l) i j k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

/-- the `k`-th slice -/
def slice (T : Holor ℂ [n, n, 3]) (k : Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ev T i j k

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

/-- The first coordinate of a holor index. -/
def idxHead {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : Fin d :=
  ⟨t.1.headI, headI_lt t⟩

/-- A vector as a one-dimensional holor. -/
def vec {m : ℕ} (u : Fin m → ℂ) : Holor ℂ [m] := fun t => u (idxHead t)

/-- The scalar holor `1`. -/
def one0 : Holor ℂ [] := fun _ => 1

/-- The rank-one holor `u ⊗ v ⊗ w`. -/
def r1 (u v : Fin n → ℂ) (w : Fin 3 → ℂ) : Holor ℂ [n, n, 3] :=
  Holor.mul (vec u) (Holor.mul (vec v) (Holor.mul (vec w) one0))

theorem ev_r1 (u v : Fin n → ℂ) (w : Fin 3 → ℂ) (i j : Fin n) (k : Fin 3) :
    ev (r1 u v w) i j k = u i * v j * w k := by
  show u i * (v j * (w k * 1)) = _
  ring

theorem cprankMax1_r1 (u v : Fin n → ℂ) (w : Fin 3 → ℂ) : Holor.CPRankMax1 (r1 u v w) :=
  .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {m : ℕ}
    (h : Holor.CPRankMax m x) : x.cprank ≤ m :=
  @Nat.find_min' (fun m => Holor.CPRankMax m x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ m h

theorem cprank_le_of_cov (T : Holor ℂ [n, n, 3]) (r : ℕ)
    (h : Cov (sp3 (slice T 0) (slice T 1) (slice T 2)) r) : T.cprank ≤ r := by
  classical
  obtain ⟨s, hs, hr1, hS⟩ := h
  have hk : ∀ k : Fin 3, slice T k ∈ Submodule.span ℂ (s : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    intro k
    fin_cases k
    · exact hS (mem_sp3_1 _ _ _)
    · exact hS (mem_sp3_2 _ _ _)
    · exact hS (mem_sp3_3 _ _ _)
  choose c hc using fun k => Submodule.mem_span_finset.mp (hk k)
  have hab : ∀ M : s, ∃ (a b : Fin n → ℂ), M.1 = vecMulVec a b := fun M => hr1 M.1 M.2
  choose a b hab using hab
  have hT : T = ∑ M : s, r1 (a M) (b M) (fun k => c k M.1) := by
    refine holor_ext fun i j k => ?_
    rw [ev_sum]
    have h1 : ev T i j k = slice T k i j := rfl
    rw [h1, ← (hc k).2, Matrix.sum_apply, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [ev_r1, Matrix.smul_apply, hab M, vecMulVec_apply, smul_eq_mul]
    ring
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ
    (fun M : s => r1 (a M) (b M) (fun k => c k M.1))
    fun M _ => Holor.cprankMax_1 (cprankMax1_r1 _ _ _)
  rw [Finset.card_univ, Fintype.card_coe, mul_one, ← hT] at hr
  exact (cprank_le_of_cprankMax hr).trans hs

end Bridge

end CP3

theorem OMA.solution : type_of% @Arxiv.«0805.3777».cprank_le_of_three_slices := by
  intro n _ T
  exact CP3.cprank_le_of_cov T _ (CP3.main n (Fin n) (Fin n) (by simp) (by simp) _ _ _)
