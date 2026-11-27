import FormalConjectures.ErdosProblems.«499»

/-!
Erdős Problem 499 — van der Waerden permanent bound.
Assembled from reduction R1 (Gurvits 2008 / Laurent–Schrijver 2010) and proofs of
H1 (real-rootedness / stability), H2 (derivative of permanent), and H3 (univariate Gurvits inequality).
-/

namespace OMA.Erdos499Vdw

/-- Real-rootedness (Gurvits): for nonnegative vectors `v, w` and a nonnegative matrix `C`, the
permanent of the matrix whose first `k` columns are `v + t w` and whose other columns are those of
`C` is, as a function of `t`, of the form `a * prod (t + r i)` with `a ≥ 0`, at most `k` factors
and all `r i ≥ 0`. -/
def H1 : Prop :=
  ∀ (n k : ℕ) (v w : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ),
    (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) → (∀ i j, 0 ≤ C i j) →
    ∃ m ≤ k, ∃ a : ℝ, 0 ≤ a ∧ ∃ r : Fin m → ℝ, (∀ i, 0 ≤ r i) ∧
      ∀ t : ℝ, (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent
        = a * ∏ i, (t + r i)

/-- Derivative of a permanent (multilinearity in the columns plus symmetry under column
permutations): for `1 ≤ k ≤ n`, the derivative at `t = 0` of the permanent of the matrix with first
`k` columns `v + t w` (other columns from `C`) is `k` times the permanent of the matrix with
columns `v` before position `k - 1`, `w` at position `k - 1` and `C` after it. -/
def H2 : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ (v w : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ),
    HasDerivAt
      (fun t : ℝ =>
        (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else C i j).permanent)
      ((k : ℝ) * (Matrix.of fun i j : Fin n =>
        if (j : ℕ) + 1 < k then v i else if (j : ℕ) + 1 = k then w i else C i j).permanent)
      0

/-- Univariate Gurvits inequality: if `f t = a * prod_{i<m} (t + r i)` with `a ≥ 0`, `r i ≥ 0`,
`m ≤ d`, `d ≥ 1`, and `L * t ≤ f t` for all `t > 0`, then `((d-1)/d)^(d-1) * L ≤ f'(0)`. -/
def H3 : Prop :=
  ∀ (d m : ℕ), 1 ≤ d → m ≤ d → ∀ (a : ℝ) (r : Fin m → ℝ) (L D : ℝ), 0 ≤ a → (∀ i, 0 ≤ r i) →
    (∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) →
    HasDerivAt (fun t : ℝ => a * ∏ i, (t + r i)) D 0 →
    (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ D

namespace H1Impl

open Matrix Finset Polynomial

section

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

end

lemma proof : H1 := by
  intro n k v w A hv hw hA
  have hkn : min k n ≤ n := min_le_right _ _
  have hmat : ∀ t : ℝ,
      (Matrix.of fun i j : Fin n => if (j : ℕ) < k then v i + t * w i else A i j).permanent
        = eval t (polyP (min k n) v w A) := by
    intro t
    rw [polyP_eval]
    congr 1
    ext i j
    simp only [colMat, of_apply]
    have hj : ((j : ℕ) < k ↔ (j : ℕ) < min k n) := by
      have := j.isLt
      omega
    simp only [hj]
  have hnn : 0 ≤ eval 1 (polyP (min k n) v w A) := by
    rw [polyP_eval]
    refine Finset.sum_nonneg fun σ _ => prod_nonneg fun i _ => ?_
    simp only [colMat, of_apply]
    split_ifs
    · have := hv (σ i); have := hw (σ i); linarith
    · exact hA _ _
  by_cases h1 : eval 1 (polyP (min k n) v w A) = 0
  · have hz : ∀ t : ℝ, eval t (polyP (min k n) v w A) = 0 := by
      intro t
      rw [polyP_eval] at h1 ⊢
      unfold permanent at h1 ⊢
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun σ _ => prod_nonneg fun i _ => by
        simp only [colMat, of_apply]
        split_ifs
        · have := hv (σ i); have := hw (σ i); linarith
        · exact hA _ _)).1 h1
      refine Finset.sum_eq_zero fun σ hσ => ?_
      obtain ⟨i, _, hi⟩ := prod_eq_zero_iff.1 (h2 σ hσ)
      refine prod_eq_zero (mem_univ i) ?_
      simp only [colMat, of_apply] at hi ⊢
      split_ifs at hi ⊢ with hh
      · have a1 := hv (σ i)
        have a2 := hw (σ i)
        have a3 : v (σ i) = 0 := by linarith
        have a4 : w (σ i) = 0 := by linarith
        rw [a3, a4]; ring
      · exact hi
    refine ⟨0, Nat.zero_le _, 0, le_rfl, fun i => i.elim0, fun i => i.elim0, fun t => ?_⟩
    rw [hmat, hz t]; simp
  · have hpos : 0 < eval 1 (polyP (min k n) v w A) := lt_of_le_of_ne hnn (Ne.symm h1)
    obtain ⟨m, hm, a, ha, r, hr, heq⟩ := factor (polyP (min k n) v w A) hnn (by
      intro t ht
      by_contra hcon
      have ht' : t.im ≠ 0 ∨ 0 < t.re := by
        by_contra hc
        rw [not_or, not_not, not_lt] at hc
        exact hcon ⟨hc.1, hc.2⟩
      obtain ⟨δ, h0, hb⟩ := limit_bound v w hv hw A hA (min k n) hkn t ht'
      rw [ht, norm_zero] at hb
      have := mul_pos (pow_pos h0 (min k n)) hpos
      linarith)
    refine ⟨m, (hm.trans (polyP_natDegree _ v w A)).trans (min_le_left _ _), a, ha, r, hr,
      fun t => ?_⟩
    rw [hmat, heq]
    simp [eval_prod]

end H1Impl

namespace H2Impl

open Matrix Finset

lemma proof : H2 := by
  classical
  intro n k hk hkn v w C
  let p : Fin n := ⟨k - 1, by omega⟩
  have hp : p.val < k := by dsimp [p]; omega
  let A (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j =>
    if j.val < k then v i + t * w i else C i j
  let B (j : Fin n) : Matrix (Fin n) (Fin n) ℝ := (A 0).updateCol j w
  have exch (j : Fin n) (hj : j.val < k) : (B j).permanent = (B p).permanent := by
    rw [← Matrix.permanent_permute_rows (Equiv.swap p j) (B p)]
    congr 1
    ext i l
    by_cases hl : l = j
    · subst l
      simp [B, Matrix.submatrix_apply]
    by_cases hlp : l = p
    · subst l
      have hjp := Ne.symm hl
      simp [B, A, Matrix.submatrix_apply, hl, hjp, hp, hj]
    · simp [B, Matrix.submatrix_apply, hl, hlp,
        Equiv.swap_apply_of_ne_of_ne hlp hl]
  have hf (σ : Equiv.Perm (Fin n)) (j : Fin n) :
      HasDerivAt (fun t => A t (σ j) j) (if j.val < k then w (σ j) else 0) 0 := by
    by_cases hj : j.val < k
    · simpa [A, hj, Pi.add_def] using ((hasDerivAt_const (0 : ℝ) (v (σ j))).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (w (σ j))))
    · simpa [A, hj] using hasDerivAt_const (0 : ℝ) (C (σ j) j)
  have hpterm (σ : Equiv.Perm (Fin n)) (j : Fin n) :
      (∏ l ∈ univ.erase j, A 0 (σ l) l) • (if j.val < k then w (σ j) else 0) =
      if j.val < k then ∏ l, B j (σ l) l else 0 := by
    by_cases hj : j.val < k
    · simp only [if_pos hj, smul_eq_mul]
      rw [← prod_erase_mul _ _ (mem_univ j)]
      congr 1
      · apply prod_congr rfl
        intro l hl
        simp [B, (mem_erase.mp hl).1]
      · simp [B]
    · simp [hj]
  have hd := HasDerivAt.fun_sum (u := univ) (fun σ _ =>
    HasDerivAt.fun_finsetProd (u := univ) (fun j _ => hf σ j))
  simp_rw [hpterm] at hd
  rw [sum_comm] at hd
  have one (j : Fin n) : (∑ σ : Equiv.Perm (Fin n), if j.val < k then ∏ l, B j (σ l) l else 0) =
      if j.val < k then (B p).permanent else 0 := by
    by_cases hj : j.val < k
    · simpa only [if_pos hj, Matrix.permanent] using exch j hj
    · simp [hj]
  simp_rw [one] at hd
  let e : Fin k ↪ Fin n := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
  have hs : (univ.filter fun j : Fin n => j.val < k) = univ.map e := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · exact fun h => ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [← sum_filter, sum_const, hs, card_map, card_univ, Fintype.card_fin, nsmul_eq_mul] at hd
  have he : B p = Matrix.of (fun i j : Fin n =>
      if j.val + 1 < k then v i else if j.val + 1 = k then w i else C i j) := by
    ext i j
    by_cases h : j = p
    · subst j
      simp [B, p, show k - 1 + 1 = k by omega]
    · have hh : j.val ≠ k - 1 := fun hv => h (Fin.ext hv)
      simp [B, A, h, show j.val + 1 ≠ k by omega,
        show (j.val + 1 < k) ↔ j.val < k by omega]
  rw [he] at hd
  exact hd

end H2Impl

namespace H3Impl

open Finset Filter Topology

/-- AM-GM in power form. -/
lemma h3_prod_le_avg_pow {k : ℕ} (hk : 0 < k) (z : Fin k → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / k) ^ k := by
  have h := Real.geom_mean_le_arith_mean (univ : Finset (Fin k)) (fun _ => (1 : ℝ)) z
    (fun _ _ => zero_le_one) (by simp [hk]) (fun i _ => hz i)
  simp only [Real.rpow_one, one_mul, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  have hP : 0 ≤ ∏ i, z i := prod_nonneg fun i _ => hz i
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  calc ∏ i, z i = ((∏ i, z i) ^ ((k : ℝ))⁻¹) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hkr.ne', Real.rpow_one]
    _ ≤ ((∑ i, z i) / k) ^ k :=
        pow_le_pow_left₀ (Real.rpow_nonneg hP _) h k

/-- `prod (1 + t / r i)` bound. -/
lemma h3_one_add_bound {k : ℕ} (hk : 0 < k) (r : Fin k → ℝ) (hr : ∀ i, 0 < r i) (t : ℝ)
    (ht : 0 ≤ t) :
    ∏ i, (1 + t / r i) ≤ (1 + t * (∑ i, 1 / r i) / k) ^ k := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  refine (h3_prod_le_avg_pow hk _ fun i => by have := hr i; positivity).trans_eq ?_
  congr 1
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_sum]
  field_simp

/-- Optimal choice of `t`. -/
lemma h3_opt_t {k : ℕ} (hk : 2 ≤ k) (a0 a1 : ℝ) (h0 : 0 < a0) (h1 : 0 < a1) :
    let t := k * a0 / ((k - 1) * a1)
    0 < t ∧ a0 * (1 + a1 * t / (k * a0)) ^ k / t = a1 * ((k : ℝ) / (k - 1)) ^ (k - 1) := by
  intro t
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hkm : (0 : ℝ) < k - 1 := by linarith
  have hkp : (0 : ℝ) < k := by linarith
  refine ⟨by positivity, ?_⟩
  have e : 1 + a1 * t / (k * a0) = (k : ℝ) / (k - 1) := by
    simp only [t]; field_simp; ring
  rw [e]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ, t]
  push_cast at hkm ⊢
  field_simp

/-- Derivative of `a * prod (t + r i)` at `0`. -/
lemma h3_deriv_formula {m : ℕ} (a : ℝ) (r : Fin m → ℝ) (D : ℝ)
    (h : HasDerivAt (fun t : ℝ => a * ∏ i, (t + r i)) D 0) :
    D = a * ∑ i, ∏ j ∈ univ.erase i, r j := by
  have h1 : HasDerivAt (fun t : ℝ => ∏ i, (t + r i))
      (∑ i, (∏ j ∈ univ.erase i, (0 + r j)) • (1 : ℝ)) 0 :=
    HasDerivAt.fun_finsetProd (fun i _ => (hasDerivAt_id' (0 : ℝ)).add_const (r i))
  have h2 := h.unique (h1.const_mul a)
  simpa [smul_eq_mul] using h2

lemma h3_D_nonneg {m : ℕ} (a : ℝ) (r : Fin m → ℝ) (ha : 0 ≤ a) (hr : ∀ i, 0 ≤ r i) :
    0 ≤ a * ∑ i, ∏ j ∈ univ.erase i, r j :=
  mul_nonneg ha (sum_nonneg fun i _ => prod_nonneg fun j _ => hr j)

/-- Zero case: if `r i0 = 0`, then `L ≤ a * prod_{j ≠ i0} r j` (limit `t → 0`). -/
lemma h3_zero_case {m : ℕ} (a L : ℝ) (r : Fin m → ℝ) (i0 : Fin m) (hi0 : r i0 = 0)
    (h : ∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) :
    L ≤ a * ∏ j ∈ univ.erase i0, r j := by
  have hq : ∀ t : ℝ, 0 < t → L ≤ a * ∏ j ∈ univ.erase i0, (t + r j) := by
    intro t ht
    have h1 := h t ht
    have hprod : ∏ i, (t + r i) = (t + r i0) * ∏ j ∈ univ.erase i0, (t + r j) :=
      (Finset.mul_prod_erase univ (fun i => t + r i) (mem_univ i0)).symm
    rw [hprod, hi0, add_zero] at h1
    have e : a * (t * ∏ j ∈ univ.erase i0, (t + r j)) =
        (a * ∏ j ∈ univ.erase i0, (t + r j)) * t := by ring
    rw [e] at h1
    exact le_of_mul_le_mul_right h1 ht
  have hcont : Continuous (fun t : ℝ => a * ∏ j ∈ univ.erase i0, (t + r j)) := by
    fun_prop
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), L ≤ a * ∏ j ∈ univ.erase i0, (t + r j) :=
    eventually_nhdsWithin_of_forall fun t ht => hq t ht
  have := ge_of_tendsto hlim hev
  simpa using this

/-- AM-GM with `p+1` terms (one term `1`, `p` terms `(p+1)/p`). -/
lemma h3_amgm_step (p : ℕ) (hp : 1 ≤ p) :
    (((p : ℝ) + 1) / p) ^ p ≤ (((p : ℝ) + 2) / ((p : ℝ) + 1)) ^ (p + 1) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp0 : (p : ℝ) ≠ 0 := hpr.ne'
  let z : Fin (p + 1) → ℝ := fun i => if (i : ℕ) = 0 then 1 else ((p : ℝ) + 1) / p
  have hz : ∀ i, 0 ≤ z i := fun i => by
    simp only [z]
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (by linarith) hpr.le
  have h := h3_prod_le_avg_pow (by omega : 0 < p + 1) z hz
  have hprod : ∏ i, z i = (((p : ℝ) + 1) / p) ^ p := by
    rw [Fin.prod_univ_succ]
    simp [z, Fin.succ_ne_zero, div_pow]
  have hsum : ∑ i, z i = (p : ℝ) + 2 := by
    rw [Fin.sum_univ_succ]
    simp [z, Fin.succ_ne_zero]
    field_simp
    ring
  rw [hprod, hsum] at h
  push_cast at h
  exact h

lemma h3_g_step (n : ℕ) (hn : 1 ≤ n) :
    ((((n + 1 : ℕ) : ℝ) - 1) / ((n + 1 : ℕ) : ℝ)) ^ (n + 1 - 1) ≤ (((n : ℝ) - 1) / n) ^ (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hp : 1 ≤ p := by omega
    have hpr : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have A := h3_amgm_step p hp
    rw [show p + 1 + 1 - 1 = p + 1 by omega, show p + 1 - 1 = p by omega]
    push_cast
    have e1 : ((p : ℝ) + 1 + 1 - 1) / ((p : ℝ) + 1 + 1) = (((p : ℝ) + 2) / ((p : ℝ) + 1))⁻¹ := by
      rw [inv_div]; ring
    have e2 : ((p : ℝ) + 1 - 1) / ((p : ℝ) + 1) = (((p : ℝ) + 1) / (p : ℝ))⁻¹ := by
      rw [inv_div]; ring
    rw [e1, e2, inv_pow, inv_pow]
    exact inv_anti₀ (pow_pos (div_pos (by linarith) hpr) _) A

lemma h3_g_anti (m d : ℕ) (hm : 1 ≤ m) (hmd : m ≤ d) :
    (((d : ℝ) - 1) / d) ^ (d - 1) ≤ (((m : ℝ) - 1) / m) ^ (m - 1) := by
  induction d, hmd using Nat.le_induction with
  | base => exact le_refl _
  | succ n hmn ih => exact le_trans (h3_g_step n (by omega)) ih

/-- Positive core: all `r i > 0`, `a > 0`, `k ≥ 2` factors. -/
lemma h3_core_pos {k : ℕ} (hk : 2 ≤ k) (a L D : ℝ) (r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (ha : 0 < a) (hD : D = a * ∑ i, ∏ j ∈ univ.erase i, r j)
    (h : ∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) :
    (((k : ℝ) - 1) / k) ^ (k - 1) * L ≤ D := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hPpos : 0 < ∏ i, r i := prod_pos fun i _ => hr i
  have hsum : ∑ i, ∏ j ∈ univ.erase i, r j = (∏ i, r i) * ∑ i, 1 / r i := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← prod_erase_mul univ r (mem_univ i)]
    have := (hr i).ne'
    field_simp
  have hDS : D = (a * ∏ i, r i) * ∑ i, 1 / r i := by
    rw [hD, hsum]; ring
  have ha0 : 0 < a * ∏ i, r i := mul_pos ha hPpos
  have hS : 0 < ∑ i, 1 / r i := sum_pos (fun i _ => by have := hr i; positivity) univ_nonempty
  have ha1 : 0 < D := by rw [hDS]; exact mul_pos ha0 hS
  have key : ∀ t : ℝ, 0 < t → L * t ≤ (a * ∏ i, r i) * (1 + D * t / (k * (a * ∏ i, r i))) ^ k := by
    intro t ht
    have h1 := h t ht
    have h2 : ∏ i, (t + r i) = (∏ i, r i) * ∏ i, (1 + t / r i) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      have := (hr i).ne'
      field_simp
      ring
    have h3 := h3_one_add_bound (by omega) r hr t ht.le
    have hk0 : (k : ℝ) ≠ 0 := by
      have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      exact this.ne'
    have h4 : 1 + t * (∑ i, 1 / r i) / k = 1 + D * t / (k * (a * ∏ i, r i)) := by
      rw [hDS]
      have : a * ∏ i, r i ≠ 0 := ha0.ne'
      field_simp
    calc L * t ≤ a * ∏ i, (t + r i) := h1
      _ = (a * ∏ i, r i) * ∏ i, (1 + t / r i) := by rw [h2]; ring
      _ ≤ (a * ∏ i, r i) * (1 + t * (∑ i, 1 / r i) / k) ^ k :=
          mul_le_mul_of_nonneg_left h3 ha0.le
      _ = (a * ∏ i, r i) * (1 + D * t / (k * (a * ∏ i, r i))) ^ k := by rw [h4]
  obtain ⟨htpos, heq⟩ := h3_opt_t hk (a * ∏ i, r i) D ha0 ha1
  have hL2 : L ≤ D * ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 1) := by
    rw [← heq]
    exact (le_div_iff₀ htpos).mpr (key _ htpos)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hc : (((k : ℝ) - 1) / k) * ((k : ℝ) / ((k : ℝ) - 1)) = 1 := by
    have : (k : ℝ) - 1 ≠ 0 := by linarith
    have : (k : ℝ) ≠ 0 := by linarith
    field_simp
  calc (((k : ℝ) - 1) / k) ^ (k - 1) * L
      ≤ (((k : ℝ) - 1) / k) ^ (k - 1) * (D * ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left hL2 (pow_nonneg (div_nonneg (by linarith) (by linarith)) _)
    _ = D * ((((k : ℝ) - 1) / k) * ((k : ℝ) / ((k : ℝ) - 1))) ^ (k - 1) := by rw [mul_pow]; ring
    _ = D := by rw [hc, one_pow, mul_one]

/-- Proof of H3. -/
lemma proof : H3 := by
  intro d m hd hmd a r L D ha hr hL hder
  have hDf := h3_deriv_formula a r D hder
  have hD0 : 0 ≤ D := hDf ▸ h3_D_nonneg a r ha hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hg0 : 0 ≤ (((d : ℝ) - 1) / d) ^ (d - 1) :=
    pow_nonneg (div_nonneg (by linarith) hdpos.le) _
  have hg1 : (((d : ℝ) - 1) / d) ^ (d - 1) ≤ 1 :=
    pow_le_one₀ (div_nonneg (by linarith) hdpos.le) ((div_le_one hdpos).mpr (by linarith))
  rcases le_or_gt L 0 with hL0 | hLpos
  · have := mul_nonneg hg0 (neg_nonneg.mpr hL0)
    linarith
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exfalso
      subst hm0
      have h1 := hL ((a + 1) / L) (div_pos (by linarith) hLpos)
      have e : L * ((a + 1) / L) = a + 1 := by field_simp
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h1
      rw [e] at h1
      linarith
    · by_cases hz : ∃ i0, r i0 = 0
      · obtain ⟨i0, hi0⟩ := hz
        have hle := h3_zero_case a L r i0 hi0 hL
        have hLD : L ≤ D := by
          rw [hDf]
          refine hle.trans (mul_le_mul_of_nonneg_left ?_ ha)
          exact single_le_sum (f := fun i => ∏ j ∈ univ.erase i, r j)
            (fun i _ => prod_nonneg fun j _ => hr j) (mem_univ i0)
        calc (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ 1 * L := mul_le_mul_of_nonneg_right hg1 hLpos.le
          _ ≤ D := by linarith
      · push_neg at hz
        have hpos : ∀ i, 0 < r i := fun i => lt_of_le_of_ne (hr i) (hz i).symm
        have ha' : 0 < a := by
          rcases lt_or_eq_of_le ha with h | h
          · exact h
          · exfalso
            have := hL 1 one_pos
            rw [← h] at this
            simp at this
            linarith
        by_cases hm1 : m = 1
        · subst hm1
          have hDa : D = a := by rw [hDf]; simp
          have hLa : L ≤ a := by
            by_contra hcon
            push_neg at hcon
            have hLa' : 0 < L - a := by linarith
            have ht : 0 < (a * r 0 + 1) / (L - a) :=
              div_pos (by have := mul_nonneg ha (hr 0); linarith) hLa'
            have hh := hL _ ht
            rw [Fin.prod_univ_one] at hh
            have e : (L - a) * ((a * r 0 + 1) / (L - a)) = a * r 0 + 1 := by
              field_simp
            nlinarith
          have : (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ 1 * L := mul_le_mul_of_nonneg_right hg1 hLpos.le
          linarith
        · have hm2 : 2 ≤ m := by omega
          have hcore := h3_core_pos hm2 a L D r hpos ha' (hDf) hL
          have hmono := h3_g_anti m d hmpos hmd
          calc (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ (((m : ℝ) - 1) / m) ^ (m - 1) * L :=
                mul_le_mul_of_nonneg_right hmono hLpos.le
            _ ≤ D := hcore

end H3Impl

namespace Reduction

open Matrix Finset Nat

/-- Weighted AM-GM: for doubly stochastic `M` and positive `x`, `prod x ≤ prod (M x)`. -/
lemma cap_ge_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n))
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∏ j, x j ≤ ∏ i, ∑ j, M i j * x j := by
  obtain ⟨h0, hr, hc⟩ := hM
  have hrow : ∀ i, ∑ j, M i j = 1 := fun i => by
    have := congrFun hr i; simpa [mulVec, dotProduct] using this
  have hcol : ∀ j, ∑ i, M i j = 1 := fun j => by
    have := congrFun hc j; simpa [vecMul, dotProduct] using this
  calc ∏ j, x j = ∏ j, x j ^ (∑ i, M i j) := by simp [hcol]
    _ = ∏ j, ∏ i, x j ^ M i j := by
        refine prod_congr rfl fun j _ => ?_
        rw [Real.rpow_sum_of_pos (hx j)]
    _ = ∏ i, ∏ j, x j ^ M i j := prod_comm
    _ ≤ ∏ i, ∑ j, M i j * x j := by
        refine prod_le_prod (fun i _ => prod_nonneg fun j _ => (Real.rpow_nonneg (hx j).le _))
          fun i _ => ?_
        exact Real.geom_mean_le_arith_mean_weighted _ _ _ (fun j _ => h0 i j) (hrow i)
          (fun j _ => (hx j).le)

/-- The permanent of a matrix all of whose columns equal `u` is `n! * prod u`. -/
lemma permanent_const_cols {n : ℕ} (u : Fin n → ℝ) :
    (Matrix.of fun i (_ : Fin n) => u i).permanent = (n ! : ℝ) * ∏ i, u i := by
  simp only [permanent, of_apply]
  have : ∀ σ : Equiv.Perm (Fin n), ∏ i, u (σ i) = ∏ i, u i := fun σ => Equiv.prod_comp σ u
  simp only [this, sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

lemma pow_self_ne_zero (n : ℕ) : ((n : ℝ) ^ n) ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact pow_ne_zero _ (by exact_mod_cast h.ne')

/-- Telescoping of the constants: `((k+1-1)/(k+1))^k * (k+1)^(k+1) = k^k * (k+1)`. -/
lemma const_step (k : ℕ) :
    ((((k + 1 : ℕ) : ℝ) - 1) / ((k + 1 : ℕ) : ℝ)) ^ (k + 1 - 1) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)
      = (k : ℝ) ^ k * ((k : ℝ) + 1) := by
  push_cast
  simp only [add_sub_cancel_right]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [div_pow, pow_succ]
  field_simp

lemma main (hH1 : H1) (hH2 : H2) (hH3 : H3) : type_of% @Erdos499.vanDerWaerden := by
  intro n M hM
  have hM0 : ∀ i j, 0 ≤ M i j := hM.1
  set c : ℝ := (n ! : ℝ) / (n : ℝ) ^ n with hc
  have key : ∀ j : ℕ, j ≤ n → ∀ y : Fin n → ℝ, (∀ l, 0 < y l) →
      c * ((n - j : ℕ) : ℝ) ^ (n - j) * ∏ l : Fin n, (if (l : ℕ) < n - j then y l else 1) ≤
        (Matrix.of fun i jj : Fin n => if (jj : ℕ) < n - j then
          ∑ l : Fin n, (if (l : ℕ) < n - j then M i l * y l else 0) else M i jj).permanent := by
    intro j
    induction j with
    | zero =>
      intro _ y hy
      simp only [Nat.sub_zero, Fin.is_lt, if_true]
      rw [permanent_const_cols]
      have h1 := cap_ge_one M hM y hy
      have : c * (n : ℝ) ^ n = n ! := by
        rw [hc]; exact div_mul_cancel₀ _ (pow_self_ne_zero n)
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    | succ j ih =>
      intro hj y hy
      obtain ⟨k', hk'⟩ : ∃ k', n - j = k' + 1 := ⟨n - j - 1, by omega⟩
      have hk'' : n - (j + 1) = k' := by omega
      have ihk := ih (by omega)
      rw [hk'] at ihk
      rw [hk'']
      have hk'n : k' < n := by omega
      set idx : Fin n := ⟨k', hk'n⟩ with hidx
      set v : Fin n → ℝ := fun i => ∑ l : Fin n, (if (l : ℕ) < k' then M i l * y l else 0) with hv
      set w : Fin n → ℝ := fun i => M i idx with hw
      set P : ℝ := ∏ l : Fin n, (if (l : ℕ) < k' then y l else 1) with hP
      have hv0 : ∀ i, 0 ≤ v i := fun i => sum_nonneg fun l _ => by
        split_ifs
        · exact mul_nonneg (hM0 i l) (hy l).le
        · exact le_refl _
      have hw0 : ∀ i, 0 ≤ w i := fun i => hM0 i idx
      obtain ⟨m, hm, a, ha, r, hr, hfac⟩ := hH1 n (k' + 1) v w M hv0 hw0 hM0
      have hder := hH2 n (k' + 1) (by omega) (by omega) v w M
      have hfun : (fun t : ℝ =>
          (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' + 1 then v i + t * w i
            else M i jj).permanent) = fun t => a * ∏ i, (t + r i) := funext hfac
      rw [hfun] at hder
      have hline : ∀ t : ℝ, 0 < t →
          (c * ((k' + 1 : ℕ) : ℝ) ^ (k' + 1) * P) * t ≤ a * ∏ i, (t + r i) := by
        intro t ht
        have hyt : ∀ l, 0 < Function.update y idx t l := by
          intro l
          by_cases hl : l = idx
          · subst hl; simp [ht]
          · simp [Function.update_of_ne hl, hy l]
        have h := ihk (Function.update y idx t) hyt
        have hprod : ∏ l : Fin n, (if (l : ℕ) < k' + 1 then Function.update y idx t l else 1)
            = P * t := by
          rw [show P * t = P * ∏ l : Fin n, (if l = idx then t else 1) by simp, hP,
            ← prod_mul_distrib]
          refine prod_congr rfl fun l _ => ?_
          by_cases hl : l = idx
          · subst hl; simp [hidx]
          · have hl' : (l : ℕ) ≠ k' := fun h => hl (Fin.ext h)
            rw [Function.update_of_ne hl, if_neg hl]
            by_cases hlt : (l : ℕ) < k'
            · simp [hlt, show (l : ℕ) < k' + 1 by omega]
            · simp [hlt, show ¬ (l : ℕ) < k' + 1 by omega]
        have hmat : (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' + 1 then
            ∑ l : Fin n, (if (l : ℕ) < k' + 1 then M i l * Function.update y idx t l else 0)
            else M i jj) =
            (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' + 1 then v i + t * w i
              else M i jj) := by
          ext i jj
          simp only [of_apply]
          split_ifs with hjj
          · rw [hv, hw]
            simp only
            rw [show t * M i idx = ∑ l : Fin n, (if l = idx then t * M i l else 0) by simp,
              ← sum_add_distrib]
            refine sum_congr rfl fun l _ => ?_
            by_cases hl : l = idx
            · subst hl; simp [hidx, mul_comm]
            · rw [Function.update_of_ne hl, if_neg hl]
              have hl' : (l : ℕ) ≠ k' := fun h => hl (Fin.ext h)
              by_cases hlt : (l : ℕ) < k'
              · simp [hlt, show (l : ℕ) < k' + 1 by omega]
              · simp [hlt, show ¬ (l : ℕ) < k' + 1 by omega]
          · rfl
        rw [hprod, hmat, hfac] at h
        linarith [h]
      have h3 := hH3 (k' + 1) m (by omega) hm a r _ _ ha hr hline hder
      have hY : (Matrix.of fun i jj : Fin n =>
          if (jj : ℕ) + 1 < k' + 1 then v i else if (jj : ℕ) + 1 = k' + 1 then w i else M i jj) =
          (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' then
            ∑ l : Fin n, (if (l : ℕ) < k' then M i l * y l else 0) else M i jj) := by
        ext i jj
        simp only [of_apply]
        by_cases h1 : (jj : ℕ) < k'
        · rw [if_pos (by omega), if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
          by_cases h2 : (jj : ℕ) = k'
          · rw [if_pos (by omega), hw]
            simp only
            congr 1
            exact Fin.ext h2.symm
          · rw [if_neg (by omega)]
      rw [hY] at h3
      have hcs := const_step k'
      have hPnn : 0 ≤ P := prod_nonneg fun l _ => by
        split_ifs
        · exact (hy l).le
        · exact zero_le_one
      have hpos : (0 : ℝ) < (k' : ℝ) + 1 := by positivity
      have h4 : ((k' : ℝ) + 1) * (c * (k' : ℝ) ^ k' * P) ≤ ((k' : ℝ) + 1) *
          (Matrix.of fun i jj : Fin n => if (jj : ℕ) < k' then
            ∑ l : Fin n, (if (l : ℕ) < k' then M i l * y l else 0) else M i jj).permanent := by
        have e : ((((k' + 1 : ℕ) : ℝ) - 1) / ((k' + 1 : ℕ) : ℝ)) ^ (k' + 1 - 1) *
            (c * ((k' + 1 : ℕ) : ℝ) ^ (k' + 1) * P) = ((k' : ℝ) + 1) * (c * (k' : ℝ) ^ k' * P) := by
          calc _ = c * P * (((((k' + 1 : ℕ) : ℝ) - 1) / ((k' + 1 : ℕ) : ℝ)) ^ (k' + 1 - 1) *
                ((k' + 1 : ℕ) : ℝ) ^ (k' + 1)) := by ring
            _ = _ := by rw [hcs]; ring
        rw [← e]
        push_cast at h3 ⊢
        exact h3
      exact le_of_mul_le_mul_left h4 hpos
  have h0 := key n le_rfl (fun _ => 1) (fun _ => zero_lt_one)
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.not_lt_zero, if_false, prod_const_one,
    CharP.cast_eq_zero] at h0
  have hMeq : (Matrix.of fun i jj : Fin n => M i jj) = M := by ext; rfl
  rw [hMeq] at h0
  rw [_root_.zpow_neg, zpow_natCast]
  calc ((n : ℝ) ^ n)⁻¹ * (n ! : ℝ) = c := by rw [hc, div_eq_inv_mul]
    _ ≤ M.permanent := h0

end Reduction

end OMA.Erdos499Vdw

theorem OMA.solution : type_of% @Erdos499.vanDerWaerden :=
  OMA.Erdos499Vdw.Reduction.main
    OMA.Erdos499Vdw.H1Impl.proof
    OMA.Erdos499Vdw.H2Impl.proof
    OMA.Erdos499Vdw.H3Impl.proof
