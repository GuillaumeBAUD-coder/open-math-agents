import OMAReductions.R_Erdos499_vanDerWaerden_R1

-- Step Erdos499.vanDerWaerden.R1.H1: hypothesis H1 of reduction Erdos499.vanDerWaerden.R1
-- Credit: @LordMike
-- H1 := for nonnegative vectors v, w and a nonnegative matrix C, the permanent of the matrix whose
-- first k columns are v + t w and whose other columns are those of C is, as a function of t, of the
-- form a * prod (t + r i) with a >= 0, at most k factors and all r i >= 0 (Gurvits; Laurent-Schrijver).
-- Proof idea: for strictly positive data, the permanent with k columns equal to a complex vector u
-- does not vanish when all entries of u lie in an open half plane containing the positive reals
-- (downward induction on k from n; the step is the Gauss-Lucas theorem applied to the polynomial
-- s -> perm with k+1 columns u + s c, whose derivative at 0 is (k+1) times the permanent at level k
-- by symmetry under column swaps, and whose top coefficient is a positive permanent). Hence the
-- real polynomial t -> perm has only real nonpositive complex roots and splits over the reals.
-- The nonnegative case follows by a limit: the factored form gives the uniform lower bound
-- |p(t)| >= delta(t)^k * p(1) off the nonpositive real axis, which is a closed condition.

open Matrix Finset Polynomial

namespace OMA

variable {n : ℕ}

/-- The matrix whose columns of index below `k` all equal `u`, the others being those of `D`. -/
def colMat {R : Type} (k : ℕ) (u : Fin n → R) (D : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) < k then u i else D i j

lemma perm_map {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (M : Matrix (Fin n) (Fin n) R) : f M.permanent = (M.map f).permanent := by
  simp [Matrix.permanent, map_sum, map_prod]

lemma colMat_map {R S : Type} (f : R → S) (k : ℕ) (u : Fin n → R) (D : Matrix (Fin n) (Fin n) R) :
    (colMat k u D).map f = colMat k (fun i => f (u i)) (D.map f) := by
  ext i j
  simp only [colMat, map_apply, of_apply]
  split_ifs <;> rfl

lemma card_lt (k : ℕ) (hk : k ≤ n) : #{i : Fin n | (i : ℕ) < k} = k := by
  rw [Fin.card_filter_val_lt]; omega

/-- Derivative at `0` of the permanent along a line in the repeated column. -/
lemma eval_deriv_perm (u c : Fin n → ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (hk : k < n)
    (hc : ∀ i, c i = D i ⟨k, hk⟩) :
    eval 0 (derivative (colMat (k + 1) (fun i => C (u i) + X * C (c i)) (D.map C)).permanent)
      = ((k : ℂ) + 1) * (colMat k u D).permanent := by
  classical
  have key : ∀ l : Fin n, (l : ℕ) < k + 1 →
      ∑ σ : Equiv.Perm (Fin n), (∏ j ∈ univ.erase l, colMat (k + 1) u D (σ j) j) * c (σ l)
        = (colMat k u D).permanent := by
    intro l hl
    rw [← permanent_permute_rows (Equiv.swap l ⟨k, hk⟩) (colMat k u D)]
    simp only [permanent]
    refine sum_congr rfl fun σ _ => ?_
    rw [← prod_erase_mul univ
      (fun i => (colMat k u D).submatrix id (Equiv.swap l ⟨k, hk⟩) (σ i) i) (mem_univ l)]
    congr 1
    · refine prod_congr rfl fun j hj => ?_
      have hjl : j ≠ l := ne_of_mem_erase hj
      simp only [colMat, of_apply, submatrix_apply, id]
      by_cases hjk : j = ⟨k, hk⟩
      · subst hjk
        rw [Equiv.swap_apply_right]
        have : (l : ℕ) ≠ k := fun h => hjl (Fin.ext h.symm)
        rw [if_pos (by simp), if_pos (by omega)]
      · rw [Equiv.swap_apply_of_ne_of_ne hjl hjk]
        have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
        by_cases h1 : (j : ℕ) < k
        · rw [if_pos (by omega), if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
    · simp only [colMat, of_apply, submatrix_apply, id, Equiv.swap_apply_left]
      rw [if_neg (by simp), hc]
  simp only [permanent, derivative_sum, derivative_prod_finset, eval_finsetSum, eval_mul,
    eval_prod]
  rw [sum_comm]
  have h2 : ∀ l : Fin n, ∑ σ : Equiv.Perm (Fin n),
      (∏ j ∈ univ.erase l, eval 0 (colMat (k + 1) (fun i => C (u i) + X * C (c i)) (D.map C) (σ j) j))
        * eval 0 (derivative (colMat (k + 1) (fun i => C (u i) + X * C (c i)) (D.map C) (σ l) l))
      = if (l : ℕ) < k + 1 then (colMat k u D).permanent else 0 := by
    intro l
    have hev : ∀ (i j : Fin n),
        eval 0 (colMat (k + 1) (fun i => C (u i) + X * C (c i)) (D.map C) i j)
          = colMat (k + 1) u D i j := by
      intro i j
      simp only [colMat, of_apply, map_apply]
      split_ifs <;> simp
    split_ifs with hl
    · rw [← key l hl]
      refine sum_congr rfl fun σ _ => ?_
      congr 1
      · exact prod_congr rfl fun j _ => hev _ _
      · simp only [colMat, of_apply, if_pos hl]
        simp
    · refine sum_eq_zero fun σ _ => ?_
      simp only [colMat, of_apply, map_apply, if_neg hl]
      simp
  rw [sum_congr rfl fun l _ => h2 l, sum_ite, sum_const_zero, add_zero, sum_const, card_lt (k + 1) hk]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, permanent]

/-- Top coefficient of the permanent along a line in the repeated column. -/
lemma coeff_perm (u c : Fin n → ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (hk : k ≤ n) :
    (colMat k (fun i => C (u i) + X * C (c i)) (D.map C)).permanent.coeff k
      = (colMat k c D).permanent := by
  classical
  simp only [permanent, finsetSum_coeff]
  refine sum_congr rfl fun σ _ => ?_
  simp only [colMat, of_apply, map_apply]
  rw [prod_ite, prod_ite]
  have h1 : (∏ x ∈ univ.filter (fun x : Fin n => ¬ (x : ℕ) < k), C (D (σ x) x))
      = C (∏ x ∈ univ.filter (fun x : Fin n => ¬ (x : ℕ) < k), D (σ x) x) := (map_prod C _ _).symm
  rw [h1, coeff_mul_C]
  congr 1
  have h2 := coeff_prod_of_natDegree_le (s := univ.filter (fun x : Fin n => (x : ℕ) < k))
    (fun x => C (u (σ x)) + X * C (c (σ x))) 1 (fun p _ => by compute_degree)
  rw [card_lt k hk, mul_one] at h2
  rw [h2]
  refine prod_congr rfl fun x _ => ?_
  simp

lemma perm_pos (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) : 0 < A.permanent :=
  Finset.sum_pos (fun σ _ => prod_pos fun i _ => hA _ _) univ_nonempty

/-- Stability: the permanent with `k` columns equal to `u` and the other columns positive does not
vanish when all entries of `u` lie in an open half plane containing the positive reals. -/
lemma stab (lam : ℂ) (hlam : 0 < lam.re) (Dr : Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ i j, 0 < Dr i j) :
    ∀ d k : ℕ, k + d = n → ∀ u : Fin n → ℂ, (∀ i, 0 < (lam * u i).re) →
      (colMat k u (Dr.map Complex.ofRealHom)).permanent ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro k hk u hu
    have hk' : k = n := by omega
    subst hk'
    have h0 : ∀ i, u i ≠ 0 := fun i h => by have := hu i; simp [h] at this
    simp only [permanent, colMat, of_apply, Fin.is_lt, if_true]
    have : ∀ σ : Equiv.Perm (Fin k), ∏ i, u (σ i) = ∏ i, u i := fun σ => Equiv.prod_comp σ u
    simp only [this, sum_const, nsmul_eq_mul]
    refine mul_ne_zero ?_ (prod_ne_zero_iff.2 fun i _ => h0 i)
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    exact_mod_cast Nat.factorial_ne_zero k
  | succ d ih =>
    intro k hk u hu
    have hkn : k < n := by omega
    set D : Matrix (Fin n) (Fin n) ℂ := Dr.map Complex.ofRealHom with hDdef
    set c : Fin n → ℂ := fun i => D i ⟨k, hkn⟩ with hcdef
    have hcr : ∀ i, c i = ((Dr i ⟨k, hkn⟩ : ℝ) : ℂ) := fun i => rfl
    set q : ℂ[X] := (colMat (k + 1) (fun i => C (u i) + X * C (c i)) (D.map C)).permanent with hq
    have heval : ∀ s : ℂ, eval s q = (colMat (k + 1) (fun i => u i + s * c i) D).permanent := by
      intro s
      have := perm_map (evalRingHom s) (colMat (k + 1) (fun i => C (u i) + X * C (c i)) (D.map C))
      rw [coe_evalRingHom] at this
      rw [hq, this, colMat_map]
      congr 1
      · congr 1
        · ext i; simp; exact mul_comm _ _
        · ext i j; simp
    have hroots : ∀ s : ℂ, eval s q = 0 → (lam * s).re < 0 := by
      intro s hs
      by_contra hcon
      rw [not_lt] at hcon
      rw [heval] at hs
      refine ih (k + 1) (by omega) (fun i => u i + s * c i) (fun i => ?_) hs
      have e : lam * (u i + s * c i) = lam * u i + ((Dr i ⟨k, hkn⟩ : ℝ) : ℂ) * (lam * s) := by
        rw [hcr]; ring
      rw [e, Complex.add_re, Complex.re_ofReal_mul]
      have := hu i
      have := mul_nonneg (hD i ⟨k, hkn⟩).le hcon
      linarith
    have hcoeff : q.coeff (k + 1) ≠ 0 := by
      rw [hq, coeff_perm u c D (k + 1) hkn]
      have e : colMat (k + 1) c D
          = (colMat (k + 1) (fun i => Dr i ⟨k, hkn⟩) Dr).map Complex.ofRealHom := by
        rw [colMat_map]; rfl
      rw [e, ← perm_map]
      have hp := perm_pos (colMat (k + 1) (fun i => Dr i ⟨k, hkn⟩) Dr) (fun i j => by
        simp only [colMat, of_apply]; split_ifs <;> exact hD _ _)
      simpa using hp.ne'
    have hdeg : 0 < q.degree := by
      have h1 := le_degree_of_ne_zero hcoeff
      have h2 : ((0 : ℕ) : WithBot ℕ) < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.succ_pos k
      exact lt_of_lt_of_le (by simpa using h2) h1
    intro hzero
    have hd0 : eval 0 (derivative q) = 0 := by
      rw [hq, eval_deriv_perm u c D k hkn (fun i => rfl), hzero, mul_zero]
    have hmem := eq_centerMass_of_eval_derivative_eq_zero hdeg hd0
    have hconv : Convex ℝ {s : ℂ | (lam * s).re < 0} := by
      refine convex_halfSpace_lt ⟨fun x y => ?_, fun a x => ?_⟩ 0
      · simp [mul_add]
      · simp [mul_left_comm]; ring
    have hin : (0 : ℂ) ∈ {s : ℂ | (lam * s).re < 0} := by
      rw [hmem]
      refine hconv.centerMass_mem (fun i _ => derivRootWeight_nonneg _ _ _)
        (sum_derivRootWeight_pos hdeg 0) (fun i hi => ?_)
      have hi' : i ∈ q.roots := Multiset.mem_toFinset.1 hi
      exact hroots i (mem_roots'.1 hi').2
    simp at hin

lemma exists_lam (t : ℂ) (ht : t.im ≠ 0 ∨ 0 < t.re) :
    ∃ lam : ℂ, 0 < lam.re ∧ 0 < (lam * t).re := by
  by_cases h : 0 < t.re
  · exact ⟨1, by simp, by simpa using h⟩
  · have hy : t.im ≠ 0 := ht.resolve_right h
    refine ⟨⟨1, -((|t.re| + 1) / t.im)⟩, by simp, ?_⟩
    have h1 : (|t.re| + 1) / t.im * t.im = |t.re| + 1 := div_mul_cancel₀ _ hy
    have h2 := neg_abs_le t.re
    rw [Complex.mul_re]
    simp only
    nlinarith

lemma nonvanish (v w : Fin n → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (Dr : Matrix (Fin n) (Fin n) ℝ) (hD : ∀ i j, 0 < Dr i j) (k : ℕ) (hk : k ≤ n) (t : ℂ)
    (ht : t.im ≠ 0 ∨ 0 < t.re) :
    (colMat k (fun i => (v i : ℂ) + t * (w i : ℂ)) (Dr.map Complex.ofRealHom)).permanent ≠ 0 := by
  obtain ⟨lam, h1, h2⟩ := exists_lam t ht
  refine stab lam h1 Dr hD (n - k) k (by omega) _ fun i => ?_
  have e : lam * ((v i : ℂ) + t * (w i : ℂ)) = (v i : ℂ) * lam + (w i : ℂ) * (lam * t) := by ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have := mul_pos (hv i) h1
  have := mul_pos (hw i) h2
  linarith

/-- A real polynomial all of whose complex roots are real and nonpositive is a constant
times a product of factors `X + r` with `r ≥ 0`. -/
lemma factor (p : ℝ[X]) (h1 : 0 ≤ p.eval 1)
    (hroots : ∀ t : ℂ, (p.map (algebraMap ℝ ℂ)).eval t = 0 → t.im = 0 ∧ t.re ≤ 0) :
    ∃ m : ℕ, m ≤ p.natDegree ∧ ∃ a : ℝ, 0 ≤ a ∧ ∃ r : Fin m → ℝ, (∀ i, 0 ≤ r i) ∧
      p = C a * ∏ i, (X + C (r i)) := by
  have hinj : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  have hs : p.Splits := by
    refine Splits.of_splits_map_of_injective hinj (IsAlgClosed.splits _) fun a ha => ?_
    have h0 := (mem_roots'.1 ha).2
    obtain ⟨him, _⟩ := hroots a h0
    exact ⟨a.re, Complex.ext (by simp) (by simp [him])⟩
  have hrt : ∀ x ∈ p.roots, x ≤ 0 := by
    intro x hx
    have h0 : eval x p = 0 := (mem_roots'.1 hx).2
    have h2 : (p.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = 0 := by
      rw [eval_map, eval₂_at_apply, h0, map_zero]
    simpa using (hroots _ h2).2
  have hl : (p.roots.map fun a => X - C a).prod
      = (p.roots.toList.map fun a => (X - C a : ℝ[X])).prod := by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
  have heq : p = C p.leadingCoeff * ∏ i : Fin p.roots.toList.length,
      (X + C (-(p.roots.toList[i.1]))) := by
    conv_lhs => rw [hs.eq_prod_roots, hl, ← Fin.prod_univ_fun_getElem]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    simp [sub_eq_add_neg]
  have hr : ∀ i : Fin p.roots.toList.length, 0 ≤ -(p.roots.toList[i.1]) := fun i =>
    neg_nonneg.2 (hrt _ (Multiset.mem_toList.1 (List.getElem_mem _)))
  refine ⟨p.roots.toList.length, ?_, p.leadingCoeff, ?_, _, hr, heq⟩
  · rw [Multiset.length_toList]; exact hs.natDegree_eq_card_roots.ge
  · by_contra hneg
    rw [not_le] at hneg
    have h3 := congrArg (eval 1) heq
    simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X] at h3
    have hpos : 0 < ∏ i : Fin p.roots.toList.length, (1 + -(p.roots.toList[i.1])) :=
      prod_pos fun i _ => by have := hr i; linarith
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith

lemma exists_delta (t : ℂ) (ht : t.im ≠ 0 ∨ 0 < t.re) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ r : ℝ, 0 ≤ r → δ * (1 + r) ≤ ‖t + (r : ℂ)‖ := by
  by_cases h : 0 < t.re
  · refine ⟨min t.re 1, lt_min h one_pos, min_le_right _ _, fun r hr => ?_⟩
    have h1 : (t + (r : ℂ)).re ≤ ‖t + (r : ℂ)‖ := Complex.re_le_norm _
    simp only [Complex.add_re, Complex.ofReal_re] at h1
    have h2 := min_le_left t.re 1
    have h3 := min_le_right t.re 1
    nlinarith [mul_le_mul_of_nonneg_right h3 hr]
  · have hy := ht.resolve_right h
    have hy' : 0 < |t.im| := abs_pos.2 hy
    have hx := abs_nonneg t.re
    refine ⟨|t.im| / (|t.im| + 1 + |t.re|), by positivity,
      (div_le_one (by positivity)).2 (by linarith), fun r hr => ?_⟩
    have h1 : |t.im| ≤ ‖t + (r : ℂ)‖ := by simpa using Complex.abs_im_le_norm (t + (r : ℂ))
    have h2 : |t.re + r| ≤ ‖t + (r : ℂ)‖ := by simpa using Complex.abs_re_le_norm (t + (r : ℂ))
    have h3 : r - |t.re| ≤ |t.re + r| := by
      have := neg_abs_le t.re
      have := le_abs_self (t.re + r)
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (h3.trans h2) hy'.le,
      mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 1 + |t.re|)]

/-- The permanent with `k` columns `v + X w`, as a real polynomial. -/
noncomputable def polyP (k : ℕ) (v w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ[X] :=
  (colMat k (fun i => C (v i) + X * C (w i)) (A.map C)).permanent

lemma polyP_eval (k : ℕ) (v w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    eval t (polyP k v w A) = (colMat k (fun i => v i + t * w i) A).permanent := by
  have := perm_map (evalRingHom t) (colMat k (fun i => C (v i) + X * C (w i)) (A.map C))
  rw [coe_evalRingHom] at this
  rw [polyP, this, colMat_map]
  congr 1
  congr 1
  · ext i; simp; exact mul_comm _ _
  · ext i j; simp

lemma polyP_evalC (k : ℕ) (v w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (t : ℂ) :
    eval t ((polyP k v w A).map (algebraMap ℝ ℂ))
      = (colMat k (fun i => (v i : ℂ) + t * (w i : ℂ)) (A.map Complex.ofRealHom)).permanent := by
  have := perm_map (eval₂RingHom (algebraMap ℝ ℂ) t)
    (colMat k (fun i => C (v i) + X * C (w i)) (A.map C))
  rw [coe_eval₂RingHom] at this
  rw [eval_map, polyP, this, colMat_map]
  congr 1
  congr 1
  · ext i; simp; exact mul_comm _ _
  · ext i j; simp

lemma polyP_natDegree (k : ℕ) (v w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (polyP k v w A).natDegree ≤ k := by
  unfold polyP permanent
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc _ ≤ ∑ i : Fin n, (if (i : ℕ) < k then 1 else 0) := sum_le_sum fun i _ => by
          simp only [colMat, of_apply, map_apply]
          split_ifs
          · compute_degree
          · simp
    _ = #{i : Fin n | (i : ℕ) < k} := by simp
    _ ≤ k := by rw [Fin.card_filter_val_lt]; exact min_le_right _ _

lemma main_pos (v w : Fin n → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (k : ℕ) (hk : k ≤ n) :
    ∃ m : ℕ, m ≤ k ∧ ∃ a : ℝ, 0 ≤ a ∧ ∃ r : Fin m → ℝ, (∀ i, 0 ≤ r i) ∧
      polyP k v w A = C a * ∏ i, (X + C (r i)) := by
  have h1 : 0 < eval 1 (polyP k v w A) := by
    rw [polyP_eval]
    refine perm_pos _ fun i j => ?_
    simp only [colMat, of_apply]
    split_ifs
    · have := hv i; have := hw i; linarith
    · exact hA i j
  obtain ⟨m, hm, a, ha, r, hr, heq⟩ := factor (polyP k v w A) h1.le (by
    intro t ht
    by_contra hcon
    have ht' : t.im ≠ 0 ∨ 0 < t.re := by
      by_contra hc
      rw [not_or, not_not, not_lt] at hc
      exact hcon ⟨hc.1, hc.2⟩
    rw [polyP_evalC] at ht
    exact nonvanish v w hv hw A hA k hk t ht' ht)
  exact ⟨m, hm.trans (polyP_natDegree k v w A), a, ha, r, hr, heq⟩

lemma bound (p : ℝ[X]) (k m : ℕ) (hm : m ≤ k) (a : ℝ) (ha : 0 ≤ a) (r : Fin m → ℝ)
    (hr : ∀ i, 0 ≤ r i) (heq : p = C a * ∏ i, (X + C (r i))) (t : ℂ) (δ : ℝ) (h0 : 0 < δ)
    (h1 : δ ≤ 1) (hδ : ∀ r : ℝ, 0 ≤ r → δ * (1 + r) ≤ ‖t + (r : ℂ)‖) :
    δ ^ k * eval 1 p ≤ ‖eval t (p.map (algebraMap ℝ ℂ))‖ := by
  have e1 : eval 1 p = a * ∏ i, (1 + r i) := by
    rw [heq]; simp [eval_prod]
  have e2 : ‖eval t (p.map (algebraMap ℝ ℂ))‖ = a * ∏ i, ‖t + (r i : ℂ)‖ := by
    rw [heq]
    simp [eval_prod, Polynomial.map_prod, abs_of_nonneg ha]
  rw [e1, e2]
  have hP : 0 ≤ ∏ i, (1 + r i) := prod_nonneg fun i _ => by have := hr i; linarith
  calc δ ^ k * (a * ∏ i, (1 + r i)) ≤ δ ^ m * (a * ∏ i, (1 + r i)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h0.le h1 hm) (mul_nonneg ha hP)
    _ = a * ∏ i, (δ * (1 + r i)) := by
        rw [prod_mul_distrib, prod_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ a * ∏ i, ‖t + (r i : ℂ)‖ :=
        mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => mul_nonneg h0.le
          (by have := hr i; linarith)) fun i _ => hδ _ (hr i)) ha

lemma limit_bound (v w : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (hk : k ≤ n) (t : ℂ)
    (ht : t.im ≠ 0 ∨ 0 < t.re) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ^ k * eval 1 (polyP k v w A) ≤ ‖eval t ((polyP k v w A).map (algebraMap ℝ ℂ))‖ := by
  obtain ⟨δ, h0, h1, hδ⟩ := exists_delta t ht
  refine ⟨δ, h0, ?_⟩
  set S : Set ℝ := {ε : ℝ | δ ^ k * eval 1 (polyP k (fun i => v i + ε) (fun i => w i + ε)
      (Matrix.of fun i j => A i j + ε)) ≤
    ‖eval t ((polyP k (fun i => v i + ε) (fun i => w i + ε)
      (Matrix.of fun i j => A i j + ε)).map (algebraMap ℝ ℂ))‖} with hS
  have hclosed : IsClosed S := by
    rw [hS]
    simp only [polyP_eval, polyP_evalC]
    refine isClosed_le (continuous_const.mul ?_) (Continuous.norm ?_)
    · simp only [permanent, colMat, of_apply]
      exact continuous_finset_sum _ fun σ _ => continuous_finset_prod _ fun i _ => by
        split_ifs <;> fun_prop
    · simp only [permanent, colMat, of_apply, map_apply, Complex.ofRealHom_eq_coe]
      exact continuous_finset_sum _ fun σ _ => continuous_finset_prod _ fun i _ => by
        split_ifs <;> fun_prop
  have hsub : Set.Ioi (0 : ℝ) ⊆ S := by
    intro ε hε
    have hε' : (0 : ℝ) < ε := hε
    obtain ⟨m, hm, a, ha, r, hr, heq⟩ := main_pos (fun i => v i + ε) (fun i => w i + ε)
      (fun i => by have := hv i; linarith) (fun i => by have := hw i; linarith)
      (Matrix.of fun i j => A i j + ε) (fun i j => by
        have := hA i j; simp only [of_apply]; linarith) k hk
    exact bound _ k m hm a ha r hr heq t δ h0 h1 hδ
  have hcl : closure (Set.Ioi (0 : ℝ)) ⊆ S := hclosed.closure_subset_iff.2 hsub
  rw [closure_Ioi] at hcl
  have h00 : (0 : ℝ) ∈ S := hcl Set.self_mem_Ici
  have e1 : (fun i => v i + (0 : ℝ)) = v := by ext; simp
  have e2 : (fun i => w i + (0 : ℝ)) = w := by ext; simp
  have e3 : (Matrix.of fun i j => A i j + (0 : ℝ)) = A := by ext; simp
  rw [hS, Set.mem_setOf_eq, e1, e2, e3] at h00
  exact h00

end OMA

theorem OMA.solution : OMA.R_Erdos499_vanDerWaerden_R1.H1 := by
  intro n k v w A hv hw hA
  have hkn : min k n ≤ n := min_le_right _ _
  have hmat : ∀ t : ℝ,
      (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else A i j).permanent
        = eval t (OMA.polyP (min k n) v w A) := by
    intro t
    rw [OMA.polyP_eval]
    congr 1
    ext i j
    simp only [OMA.colMat, of_apply]
    have hj : ((j : ℕ) < k ↔ (j : ℕ) < min k n) := by
      have := j.isLt
      omega
    simp only [hj]
  have hnn : 0 ≤ eval 1 (OMA.polyP (min k n) v w A) := by
    rw [OMA.polyP_eval]
    refine Finset.sum_nonneg fun σ _ => prod_nonneg fun i _ => ?_
    simp only [OMA.colMat, of_apply]
    split_ifs
    · have := hv (σ i); have := hw (σ i); linarith
    · exact hA _ _
  by_cases h1 : eval 1 (OMA.polyP (min k n) v w A) = 0
  · have hz : ∀ t : ℝ, eval t (OMA.polyP (min k n) v w A) = 0 := by
      intro t
      rw [OMA.polyP_eval] at h1 ⊢
      unfold permanent at h1 ⊢
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun σ _ => prod_nonneg fun i _ => by
        simp only [OMA.colMat, of_apply]
        split_ifs
        · have := hv (σ i); have := hw (σ i); linarith
        · exact hA _ _)).1 h1
      refine Finset.sum_eq_zero fun σ hσ => ?_
      obtain ⟨i, _, hi⟩ := prod_eq_zero_iff.1 (h2 σ hσ)
      refine prod_eq_zero (mem_univ i) ?_
      simp only [OMA.colMat, of_apply] at hi ⊢
      split_ifs at hi ⊢ with hh
      · have a1 := hv (σ i)
        have a2 := hw (σ i)
        have a3 : v (σ i) = 0 := by linarith
        have a4 : w (σ i) = 0 := by linarith
        rw [a3, a4]; ring
      · exact hi
    refine ⟨0, Nat.zero_le _, 0, le_rfl, fun i => i.elim0, fun i => i.elim0, fun t => ?_⟩
    rw [hmat, hz t]; simp
  · have hpos : 0 < eval 1 (OMA.polyP (min k n) v w A) := lt_of_le_of_ne hnn (Ne.symm h1)
    obtain ⟨m, hm, a, ha, r, hr, heq⟩ := OMA.factor (OMA.polyP (min k n) v w A) hnn (by
      intro t ht
      by_contra hcon
      have ht' : t.im ≠ 0 ∨ 0 < t.re := by
        by_contra hc
        rw [not_or, not_not, not_lt] at hc
        exact hcon ⟨hc.1, hc.2⟩
      obtain ⟨δ, h0, hb⟩ := OMA.limit_bound v w hv hw A hA (min k n) hkn t ht'
      rw [ht, norm_zero] at hb
      have := mul_pos (pow_pos h0 (min k n)) hpos
      linarith)
    refine ⟨m, (hm.trans (OMA.polyP_natDegree _ v w A)).trans (min_le_left _ _), a, ha, r, hr,
      fun t => ?_⟩
    rw [hmat, heq]
    simp [eval_prod]
