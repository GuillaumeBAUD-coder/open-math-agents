import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Reduction Arxiv.0805.3777.cprank_le_of_square_slices.R1 of Generic and maximal rank of 3-tensors — cprank le of square slices
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The bound: every complex tensor with m slices of size n x n has rank at most (m + 1) n / 2.
--
-- H1 and H2 are one statement about a pair (A, B) of n x n matrices, split by whether the pencil
-- is regular (some combination s A + t B is invertible, H1) or singular (H2): in suitable bases
-- (P, Q) the pair is simultaneously diagonal up to a tensor of rank at most n / 2, that is
--   A = P diag(a) Q + sum_j alpha_j u_j v_j^T,   B = P diag(b) Q + sum_j beta_j u_j v_j^T,
-- with n / 2 rank-one matrices u_j v_j^T. This refines the bound n + n / 2 for the rank of a
-- pencil of square matrices (Ja'Ja'): n of the rank-one matrices can be taken of the form
-- (P e_i)(e_i^T Q).
--
-- What main proves from them.
-- * The perturbation lemma (pert): for any n x n matrices U, V there are diagonal d1, d2 such
--   that the pencil (U + d1, V + d2) has n distinct eigenvalues, hence lies in the span of n
--   rank-one matrices. Conjugating by (P, Q), the span of the n matrices (P e_i)(e_i^T Q) and of
--   n further rank-one matrices contains any given pair (pair_pert).
-- * Odd m = 2k + 1: write the first slice as P diag(D) Q with P, Q products of transvections; it
--   lies in the span of the (P e_i)(e_i^T Q). The other 2k slices are taken in pairs, each pair
--   costing n more rank-one matrices. Total n + k n = (m + 1) n / 2. No hypothesis is used.
-- * Even m = 2k + 2: apply H1 or H2 to the first two slices; they lie in the span of the
--   (P e_i)(e_i^T Q) and of n / 2 more rank-one matrices. The other 2k slices are taken in
--   pairs as before. Total n + n / 2 + k n = (m + 1) n / 2 (rounded down).
--
-- Reuse and credit: the lemmas sep_iff, fel, det_add_corner, exists_eval_ne_zero, osl, osl_all,
-- outer_sum, nice_of_good and diag_sum are taken from the merged proof
-- proofs/Arxiv.0805.3777.cprank_le_of_three_slices.lean (PR #3512, same owner), with its two
-- definitions penPoly and Good written out, since a reduction file declares no definitions.
-- The passage from rank-one sums to CP rank follows the Bridge section of
-- proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean (PR #2438, DomTheDeveloper; a
-- port of Kenta Kitamura's https://github.com/KitaKen1/mrank-3-3-5-lean, Apache License 2.0),
-- again without definitions.

namespace OMA.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1

open Matrix Polynomial

def H1 : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), (∃ s t : ℂ, IsUnit (s • A + t • B)) →
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin (n / 2) → Fin n → ℂ)
      (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)

def H2 : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), (∀ s t : ℂ, ¬ IsUnit (s • A + t • B)) →
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin (n / 2) → Fin n → ℂ)
      (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)

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



theorem exists_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : ∃ a : ℂ, p.eval a ≠ 0 := by
  obtain ⟨a, ha⟩ := (p.roots.toFinset.finite_toSet).exists_notMem
  refine ⟨a, fun h0 => ha ?_⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (mem_roots hp).mpr h0

theorem osl (k : ℕ) (U V : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : ((U.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 ∧ (((X : ℂ[X]) • (U.submatrix Fin.castSucc Fin.castSucc).map C + (V.submatrix Fin.castSucc Fin.castSucc).map C).det).Separable)) :
    ∃ x y : ℂ, ((U + diagonal (Pi.single (Fin.last k) x)).det ≠ 0 ∧ (((X : ℂ[X]) • (U + diagonal (Pi.single (Fin.last k) x)).map C + (V + diagonal (Pi.single (Fin.last k) y)).map C).det).Separable) := by
  set Ub := U.submatrix Fin.castSucc Fin.castSucc
  set Vb := V.submatrix Fin.castSucc Fin.castSucc
  set pb := ((X : ℂ[X]) • (Ub).map C + (Vb).map C).det with hpb
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
  have hpen : ∀ x : ℂ, ((X : ℂ[X]) • (U + diagonal (Pi.single (Fin.last k) x)).map C + (V + diagonal (Pi.single (Fin.last k) (-a * x))).map C).det
      = ((X : ℂ[X]) • (U).map C + (V).map C).det + C x * F := by
    intro x
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
    ring
  have hdet : ∀ x : ℂ, (U + diagonal (Pi.single (Fin.last k) x)).det = U.det + x * Ub.det :=
    fun x => det_add_corner k U x
  have hfin := fel F (((X : ℂ[X]) • (U).map C + (V).map C).det) hFs
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
    ((U.submatrix (Fin.castLE hs) (Fin.castLE hs)).det ≠ 0 ∧ (((X : ℂ[X]) • (U.submatrix (Fin.castLE hs) (Fin.castLE hs)).map C + (V.submatrix (Fin.castLE hs) (Fin.castLE hs)).map C).det).Separable)
    → ∃ d₁ d₂ : Fin n → ℂ, (∀ i : Fin n, (i : ℕ) < s → d₁ i = 0 ∧ d₂ i = 0)
      ∧ ((U + diagonal d₁).det ≠ 0 ∧ (((X : ℂ[X]) • (U + diagonal d₁).map C + (V + diagonal d₂).map C).det).Separable) := by
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

theorem outer_sum {k : ℕ} (M W : Matrix (Fin k) (Fin k) ℂ) (hW : W.det ≠ 0) :
    M = ∑ l, vecMulVec (M *ᵥ fun i => W i l) (W⁻¹ l) := by
  have h1 : M = M * W * W⁻¹ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hW), Matrix.mul_one]
  ext i j
  conv_lhs => rw [h1]
  simp only [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, mulVec, dotProduct,
    Finset.sum_mul]

theorem nice_of_good {k : ℕ} (U V : Matrix (Fin k) (Fin k) ℂ)
    (h : ((U).det ≠ 0 ∧ (((X : ℂ[X]) • (U).map C + (V).map C).det).Separable)) :
    ∃ (x y : Fin k → Fin k → ℂ) (c : Fin k → ℂ),
      U = ∑ l, vecMulVec (x l) (y l) ∧ V = ∑ l, c l • vecMulVec (x l) (y l) := by
  set p := ((X : ℂ[X]) • (U).map C + (V).map C).det with hp
  have hp0 : p ≠ 0 := h.2.ne_zero
  have hdeg : p.natDegree = k := by
    apply le_antisymm
    · have := natDegree_det_X_add_C_le U V
      simp only [Fintype.card_fin] at this
      rw [hp]; exact this
    · apply le_natDegree_of_ne_zero
      have := coeff_det_X_add_C_card U V
      simp only [Fintype.card_fin] at this
      rw [hp, this]; exact h.1
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
    rw [← hμroot l, hp, ← coe_evalRingHom, RingHom.map_det]
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

/-- The perturbation lemma: after adding suitable diagonal matrices, a pair of square matrices
lies in the span of `n` rank-one matrices. -/
theorem pert {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (d₁ d₂ : Fin n → ℂ) (x y : Fin n → Fin n → ℂ) (c : Fin n → ℂ),
      U + diagonal d₁ = ∑ l, vecMulVec (x l) (y l) ∧
      V + diagonal d₂ = ∑ l, c l • vecMulVec (x l) (y l) := by
  obtain ⟨d₁, d₂, -, hg⟩ := osl_all 0 n (Nat.zero_le n) U V
    ⟨by rw [Matrix.det_isEmpty]; exact one_ne_zero,
      by rw [Matrix.det_isEmpty]; exact separable_one⟩
  obtain ⟨x, y, c, h1, h2⟩ := nice_of_good _ _ hg
  exact ⟨d₁, d₂, x, y, c, h1, h2⟩

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

theorem base_eq {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) :
    P * diagonal d * Q = ∑ i, d i • vecMulVec (P *ᵥ Pi.single i 1) (Pi.single i 1 ᵥ* Q) := by
  rw [diag_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul]

/-- The perturbation lemma in the bases `(P, Q)`. -/
theorem pair_pert {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (hQ : IsUnit Q)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (x y : Fin n → Fin n → ℂ) (d₁ d₂ c : Fin n → ℂ),
      A = ∑ l, vecMulVec (x l) (y l) - P * diagonal d₁ * Q ∧
      B = ∑ l, c l • vecMulVec (x l) (y l) - P * diagonal d₂ * Q := by
  obtain ⟨d₁, d₂, x, y, c, h1, h2⟩ := pert (P⁻¹ * A * Q⁻¹) (P⁻¹ * B * Q⁻¹)
  have hPd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hQd : IsUnit Q.det := (isUnit_iff_isUnit_det Q).mp hQ
  have conj : ∀ M : Matrix (Fin n) (Fin n) ℂ, P * (P⁻¹ * M * Q⁻¹) * Q = M := by
    intro M
    calc P * (P⁻¹ * M * Q⁻¹) * Q = (P * P⁻¹) * M * (Q⁻¹ * Q) := by
          simp only [Matrix.mul_assoc]
      _ = M := by
          rw [mul_nonsing_inv _ hPd, nonsing_inv_mul _ hQd, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun l => P *ᵥ x l, fun l => y l ᵥ* Q, d₁, d₂, c, ?_, ?_⟩
  · have h := congrArg (fun M => P * M * Q) h1
    simp only [Matrix.mul_add, Matrix.add_mul, conj, Matrix.mul_sum, Matrix.sum_mul,
      mul_vecMulVec, vecMulVec_mul] at h
    rw [← h]
    abel
  · have h := congrArg (fun M => P * M * Q) h2
    simp only [Matrix.mul_add, Matrix.add_mul, conj, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul] at h
    rw [← h]
    abel

/-- The covering family: the `n` matrices `(P eᵢ)(eᵢᵀ Q)`, `n` rank-one matrices for each of the
`k` pairs, and `e` extra rank-one matrices. -/
theorem cover {n k e : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (hQ : IsUnit Q)
    (A B : Fin k → Matrix (Fin n) (Fin n) ℂ) (ue ve : Fin e → Fin n → ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (x y : ι → Fin n → ℂ), Fintype.card ι = n + k * n + e ∧
      (∀ (d : Fin n → ℂ) (α : Fin e → ℂ),
        P * diagonal d * Q + ∑ j, α j • vecMulVec (ue j) (ve j) ∈
          Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) ∧
      ∀ j, A j ∈ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) ∧
        B j ∈ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  classical
  choose x' y' d₁ d₂ c hA hB using fun j => pair_pert P Q hP hQ (A j) (B j)
  refine ⟨Fin n ⊕ ((Fin k × Fin n) ⊕ Fin e), inferInstance,
    Sum.elim (fun i => P *ᵥ Pi.single i 1) (Sum.elim (fun p => x' p.1 p.2) ue),
    Sum.elim (fun i => Pi.single i 1 ᵥ* Q) (Sum.elim (fun p => y' p.1 p.2) ve), ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin]
    ring
  · set W := Submodule.span ℂ (Set.range fun l : Fin n ⊕ ((Fin k × Fin n) ⊕ Fin e) =>
      vecMulVec (Sum.elim (fun i => P *ᵥ Pi.single i 1) (Sum.elim (fun p => x' p.1 p.2) ue) l)
        (Sum.elim (fun i => Pi.single i 1 ᵥ* Q) (Sum.elim (fun p => y' p.1 p.2) ve) l)) with hW
    have hbase : ∀ i : Fin n, vecMulVec (P *ᵥ Pi.single i 1) (Pi.single i 1 ᵥ* Q) ∈ W :=
      fun i => Submodule.subset_span ⟨Sum.inl i, rfl⟩
    have hpair : ∀ j l, vecMulVec (x' j l) (y' j l) ∈ W :=
      fun j l => Submodule.subset_span ⟨Sum.inr (Sum.inl (j, l)), rfl⟩
    have hext : ∀ j, vecMulVec (ue j) (ve j) ∈ W :=
      fun j => Submodule.subset_span ⟨Sum.inr (Sum.inr j), rfl⟩
    have hdiag : ∀ d : Fin n → ℂ, P * diagonal d * Q ∈ W := by
      intro d
      rw [base_eq]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbase i)
    refine ⟨fun d α => W.add_mem (hdiag d)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hext j)), fun j => ⟨?_, ?_⟩⟩
    · rw [hA j]
      exact W.sub_mem (Submodule.sum_mem _ fun l _ => hpair j l) (hdiag _)
    · rw [hB j]
      exact W.sub_mem (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hpair j l))
        (hdiag _)

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

theorem ix_surj {d₁ d₂ d₃ : ℕ} (t : HolorIndex [d₁, d₂, d₃]) :
    ∃ (c : Fin d₁) (i : Fin d₂) (j : Fin d₃),
      t = ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {k : ℕ}
    (h : Holor.CPRankMax k x) : x.cprank ≤ k :=
  @Nat.find_min' (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ k h

/-- A tensor whose entries are a sum of products has rank at most the number of summands. -/
theorem cprank_le_of_sum {d₁ d₂ d₃ : ℕ} {ι : Type} [Fintype ι] (T : Holor ℂ [d₁, d₂, d₃])
    (u : ι → Fin d₁ → ℂ) (v : ι → Fin d₂ → ℂ) (w : ι → Fin d₃ → ℂ)
    (h : ∀ (c : Fin d₁) (i : Fin d₂) (j : Fin d₃),
      T ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ =
        ∑ l, u l c * v l i * w l j) :
    T.cprank ≤ Fintype.card ι := by
  classical
  let R : ι → Holor ℂ [d₁, d₂, d₃] := fun l =>
    Holor.mul (fun t : HolorIndex [d₁] => u l ⟨t.1.headI, headI_lt t⟩)
      (Holor.mul (fun t : HolorIndex [d₂] => v l ⟨t.1.headI, headI_lt t⟩)
        (Holor.mul (fun t : HolorIndex [d₃] => w l ⟨t.1.headI, headI_lt t⟩)
          (fun _ : HolorIndex [] => (1 : ℂ))))
  have hR : ∀ l, Holor.CPRankMax1 (R l) := fun l => .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))
  have hT : T = ∑ l, R l := by
    funext t
    obtain ⟨c, i, j, rfl⟩ := ix_surj t
    rw [h]
    have hs : ∀ s : Finset ι,
        (∑ l ∈ s, R l) ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ =
          ∑ l ∈ s, u l c * v l i * w l j := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rfl
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
        show R a _ + _ = _
        congr 1
        show u a c * (v a i * (w a j * 1)) = _
        ring
    exact (hs Finset.univ).symm
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ R fun l _ => Holor.cprankMax_1 (hR l)
  rw [Finset.card_univ, mul_one, ← hT] at hr
  exact cprank_le_of_cprankMax hr

/-- If all slices lie in the span of `r` rank-one matrices, the tensor has rank at most `r`. -/
theorem cprank_le_of_cover {m n r : ℕ} (T : Holor ℂ [m, n, n]) {ι : Type} [Fintype ι]
    (x y : ι → Fin n → ℂ) (hcard : Fintype.card ι ≤ r)
    (h : ∀ i : Fin m, (Matrix.of fun (j k : Fin n) =>
        T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
          Matrix (Fin n) (Fin n) ℂ) ∈
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) : T.cprank ≤ r := by
  classical
  have hc : ∀ i : Fin m, ∃ c : ι → ℂ, ∑ l, c l • vecMulVec (x l) (y l) =
      (Matrix.of fun (j k : Fin n) =>
        T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
          Matrix (Fin n) (Fin n) ℂ) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (h i)
  choose c hc using hc
  refine (cprank_le_of_sum T (fun l i => c i l) x y ?_).trans hcard
  intro i j k
  have h1 := congrFun (congrFun (hc i) j) k
  rw [Matrix.of_apply] at h1
  rw [← h1, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

theorem main : H1 → H2 → type_of% @Arxiv.«0805.3777».cprank_le_of_square_slices := by
  intro h1 h2 m n hm hn T
  classical
  let S : ℕ → Matrix (Fin n) (Fin n) ℂ := fun i => Matrix.of fun j k =>
    if h : i < m then T ⟨[i, j.1, k.1], .cons h (.cons j.2 (.cons k.2 .nil))⟩ else 0
  have hS : ∀ i : Fin m, (Matrix.of fun (j k : Fin n) =>
      T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
        Matrix (Fin n) (Fin n) ℂ) = S i.1 := by
    intro i
    ext j k
    simp only [S, Matrix.of_apply, dif_pos i.2]
  have hfin : ∀ (ι : Type) (_ : Fintype ι) (x y : ι → Fin n → ℂ),
      Fintype.card ι ≤ (m + 1) * n / 2 →
      (∀ i < m, S i ∈ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) →
      T.cprank ≤ (m + 1) * n / 2 := by
    intro ι _ x y hcard hmem
    exact cprank_le_of_cover T x y hcard fun i => by
      rw [hS i]
      exact hmem i.1 i.2
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · -- even number of slices
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hE : ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ)
        (u v : Fin (n / 2) → Fin n → ℂ) (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
        S 0 = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
        S 1 = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j) := by
      by_cases h : ∃ s t : ℂ, IsUnit (s • S 0 + t • S 1)
      · exact h1 n (S 0) (S 1) h
      · exact h2 n (S 0) (S 1) fun s t hst => h ⟨s, t, hst⟩
    obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hS0, hS1⟩ := hE
    obtain ⟨ι, inst, x, y, hcard, hbase, hpairs⟩ := cover P Q hP hQ
      (fun j : Fin k => S (2 * j.1 + 2)) (fun j : Fin k => S (2 * j.1 + 3)) u v
    refine hfin ι inst x y ?_ ?_
    · rw [hcard, hk]
      have e : (2 * (k + 1) + 1) * n = n + 2 * ((k + 1) * n) := by ring
      rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      have e2 : (k + 1) * n = k * n + n := by ring
      omega
    · intro i hi
      rcases Nat.lt_or_ge i 2 with h2' | h2'
      · interval_cases i
        · rw [hS0]
          exact hbase a α
        · rw [hS1]
          exact hbase b β
      · obtain ⟨j, hj | hj⟩ : ∃ j, i = 2 * j + 2 ∨ i = 2 * j + 3 := ⟨(i - 2) / 2, by omega⟩
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).1
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).2
  · -- odd number of slices
    obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (S 0)
    have hP : IsUnit (L.map Matrix.TransvectionStruct.toMatrix).prod :=
      (isUnit_iff_isUnit_det _).mpr (by
        rw [Matrix.TransvectionStruct.det_toMatrix_prod]
        exact isUnit_one)
    have hQ : IsUnit (L'.map Matrix.TransvectionStruct.toMatrix).prod :=
      (isUnit_iff_isUnit_det _).mpr (by
        rw [Matrix.TransvectionStruct.det_toMatrix_prod]
        exact isUnit_one)
    obtain ⟨ι, inst, x, y, hcard, hbase, hpairs⟩ := cover _ _ hP hQ
      (fun j : Fin k => S (2 * j.1 + 1)) (fun j : Fin k => S (2 * j.1 + 2))
      (Fin.elim0 : Fin 0 → Fin n → ℂ) (Fin.elim0 : Fin 0 → Fin n → ℂ)
    refine hfin ι inst x y ?_ ?_
    · rw [hcard, hk]
      have e : (2 * k + 1 + 1) * n = 2 * ((k + 1) * n) := by ring
      rw [e, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      have e2 : (k + 1) * n = k * n + n := by ring
      omega
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, hD]
        have hb := hbase D (Fin.elim0 : Fin 0 → ℂ)
        simpa using hb
      · obtain ⟨j, hj | hj⟩ : ∃ j, i = 2 * j + 1 ∨ i = 2 * j + 2 := ⟨(i - 1) / 2, by omega⟩
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).1
        · have hjk : j < k := by omega
          rw [hj]
          exact (hpairs ⟨j, hjk⟩).2

end OMA.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1
