import FormalConjectures.Wikipedia.DeterminantalConjecture

/-!
# Marcus–de Oliveira via variation of one eigenvalue

For a set of retained rows, vary the diagonal entry in one of these rows.
Both the determinant and each permutation product are affine in this complex
parameter. The leading coefficient is the problem with that row deleted.

Lift the slope and constant term to a pair of complex numbers. A separating
linear functional can be varied while fixing the separation from one vertex.
Each step adds a tied vertex until the maximizers span a facet relative to
the vertex configuration, or every vertex ties. Functionals supported on
the slope coordinate follow by deleting the varied row. The induction stops
with a finite probability coupling on at most two marked rows.
Equality of their image marginals suffices by expansion over subsets.

Every subset incidence function has nonnegative signed weight by the
positive semidefiniteness of the corresponding compressed projection.
This removes the entire nonnegative span of these functions from the facet test.

The signed weights follow the determinant expansion of Merikoski and Virtanen,
Linear Algebra Appl. 121 (1989), 345–352. Kovačec's two-row argument motivates the
finite marginal problem at the base of the induction. Drury used subset incidence
certificates for a class of supporting half-spaces in dimension four.

* https://doi.org/10.1016/0024-3795(89)90709-X
* https://doi.org/10.1016/0024-3795(94)90107-4
* https://doi.org/10.13001/1081-3810.1131
-/

namespace OMA.R_DeterminantalConjecture_determinantal_conjecture_R1

open Matrix

private theorem orient_direction {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (l : ι → E →ₗ[ℝ] ℝ) (s : ι) (A : Set ι)
    (hinf : ∀ u, ∃ j, 0 ≤ l j u) (u : E)
    (hflat : ∀ i ∈ A, l i u = l s u) (j : ι) (hj : l j u ≠ l s u) :
    ∃ v, (∀ i ∈ A, l i v = l s v) ∧ l s v ≤ 0 ∧ ∃ i, l s v < l i v := by
  have hn : ∀ i ∈ A, l i (-u) = l s (-u) := by simpa using hflat
  rcases lt_trichotomy (l s u) 0 with hs | hs | hs
  · obtain ⟨i, hi⟩ := hinf u
    exact ⟨u, hflat, hs.le, i, hs.trans_le hi⟩
  · rcases lt_or_gt_of_ne hj with hj | hj
    · exact ⟨-u, hn, by simp [hs], j, by simpa using hj⟩
    · exact ⟨u, hflat, hs.le, j, hj⟩
  · obtain ⟨i, hi⟩ := hinf (-u)
    have hs' : l s (-u) < 0 := by simpa using hs
    exact ⟨-u, hn, hs'.le, i, hs'.trans_le hi⟩

private theorem upper_envelope_test {ι E : Type*} [Fintype ι] [Nonempty ι]
    [AddCommGroup E] [Module ℝ E] (l : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hinf : ∀ u, ∃ j, 0 ≤ l j u)
    (hface : ∀ z s, (∀ i, l i z + c i ≤ l s z + c s) →
      (∀ u, (∀ i, l i z + c i = l s z + c s → l i u = l s u) →
        ∀ i, l i u = l s u) → 0 ≤ l s z + c s)
    (x : E) : ∃ i, 0 ≤ l i x + c i := by
  classical
  by_contra! hbad
  let F (z : E) (i : ι) := l i z + c i
  obtain ⟨s, -, hs⟩ := Finset.univ.exists_max_image (F x) Finset.univ_nonempty
  let A (z : E) := Finset.univ.filter (fun i => F z i = F z s)
  have memA (z : E) (i : ι) : i ∈ A z ↔ F z i = F z s := by simp [A]
  let S : Set (Finset ι) := {T | ∃ z, F z s < 0 ∧ (∀ i, F z i ≤ F z s) ∧ T = A z}
  have hS : S.Nonempty := ⟨A x, x, hbad s, fun i => hs i (Finset.mem_univ _), rfl⟩
  obtain ⟨T, hT, hmax⟩ := S.toFinite.exists_maximal hS
  obtain ⟨z, hz, hzmax, rfl⟩ := hT
  apply hz.not_ge
  apply hface z s hzmax
  intro u hu j
  by_contra hj
  obtain ⟨v, hv, hsv, i₀, hi₀⟩ := orient_direction l s (↑(A z)) hinf u
    (fun i hi => hu i ((memA z i).mp hi)) j hj
  let inc := Finset.univ.filter (fun i => l s v < l i v)
  have memInc (i : ι) : i ∈ inc ↔ l s v < l i v := by simp [inc]
  let cross (i : ι) := (F z s - F z i) / (l i v - l s v)
  obtain ⟨k, hk, hmin⟩ := inc.exists_min_image cross ⟨i₀, (memInc _).2 hi₀⟩
  have hk' := (memInc _).1 hk
  have hkn : k ∉ A z := fun h => hk'.ne (hv k h).symm
  have ht : 0 < cross k := div_pos
    (sub_pos.mpr (lt_of_le_of_ne (hzmax k) (fun h => hkn ((memA z k).2 h))))
    (sub_pos.mpr hk')
  let y := z + (cross k) • v
  have hy (i : ι) : F y i = F z i + cross k * l i v := by
    simp only [F, y, map_add, map_smul, smul_eq_mul]
    ring
  have hymax (i : ι) : F y i ≤ F y s := by
    rw [hy, hy]
    by_cases hi : i ∈ inc
    · have h := (le_div_iff₀ (sub_pos.mpr ((memInc _).1 hi))).mp (hmin i hi)
      linarith only [h]
    · have h := mul_le_mul_of_nonneg_left (le_of_not_gt (fun h => hi ((memInc _).2 h))) ht.le
      linarith only [h, hzmax i]
  have hsub : A z ⊆ A y := by
    intro i hi
    exact (memA y i).2 (by rw [hy, hy, (memA z i).1 hi, hv i hi])
  have hyneg : F y s < 0 := by
    rw [hy]
    linarith only [mul_nonpos_of_nonneg_of_nonpos ht.le hsv, hz]
  have hknew : k ∈ A y := by
    apply (memA y k).2
    rw [hy, hy]
    have he := div_mul_cancel₀ (F z s - F z k) (sub_ne_zero.mpr hk'.ne')
    change cross k * (l k v - l s v) = _ at he
    linarith only [he]
  exact hkn ((hmax (show A y ∈ S from ⟨y, hyneg, hymax, rfl⟩) hsub) hknew)

/-- Conjugation invariance does not require inverting a possibly singular determinant. -/
private theorem det_unitary_conj {n : Type} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (M : Matrix n n ℂ) :
    (U.val * M * star U.val).det = M.det := by
  have h := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at h ⊢
  linear_combination M.det * h

private theorem relative_det {n : Type} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (U V : unitary (Matrix n n ℂ)) :
    (U.val * diagonal a * star U.val + V.val * diagonal b * star V.val).det =
      (diagonal a + (star U * V).val * diagonal b * star (star U * V).val).det := by
  rw [← det_unitary_conj U (diagonal a + _)]
  congr 1
  have hu : U.val * star U.val = 1 := Unitary.coe_mul_star_self U
  simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, mul_add, add_mul, mul_assoc, hu, mul_one]
  rw [← mul_assoc U.val (star U.val), hu, one_mul]

/-- A separating functional can be moved until its maximizing vertices
span a facet relative to the affine hull, or all vertices tie. -/
private theorem lifted_facet_test {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℂ × ℂ) (x : ℂ × ℂ)
    (test : ∀ (f : (ℂ × ℂ) →ₗ[ℝ] ℝ) (s : ι),
      (∀ i, f (v i) ≤ f (v s)) →
      (∀ g : (ℂ × ℂ) →ₗ[ℝ] ℝ,
        (∀ i, f (v i) = f (v s) → g (v i) = g (v s)) →
        ∃ r : ℝ, ∀ i, g (v i) - g (v s) = r * (f (v i) - f (v s))) →
      f x ≤ f (v s)) : x ∈ convexHull ℝ (Set.range v) := by
  classical
  by_contra hx
  obtain ⟨f₀, t, ht, hx'⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) ((Set.finite_range v).isCompact_convexHull ℝ).isClosed hx
  let F := f₀.toLinearMap
  have bad (i : ι) : F (v i) < F x :=
    (ht _ (subset_convexHull ℝ _ ⟨i, rfl⟩)).trans hx'
  let b : ι := Classical.arbitrary ι
  let d := x - v b
  let N : Submodule ℝ ((ℂ × ℂ) →ₗ[ℝ] ℝ) :=
    { carrier := {g | g d = 0}
      zero_mem' := rfl
      add_mem' := fun h₁ h₂ => by simp_all
      smul_mem' := fun r h => by simp_all }
  let l (i : ι) : N →ₗ[ℝ] ℝ :=
    { toFun := fun h => h.val (v i - x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let c (i : ι) := F (v i - x)
  have infBound (u : N) : ∃ i, 0 ≤ l i u := by
    refine ⟨b, ?_⟩
    have h : u.val (x - v b) = 0 := u.property
    change 0 ≤ u.val (v b - x)
    simp only [map_sub] at h ⊢
    linarith
  have contact (z : N) (s : ι) (hs : ∀ i, l i z + c i ≤ l s z + c s)
      (span : ∀ u : N, (∀ i, l i z + c i = l s z + c s → l i u = l s u) →
        ∀ i, l i u = l s u) : 0 ≤ l s z + c s := by
    let f := F + z.val
    have ev (i : ι) : l i z + c i = f (v i) - f x := by
      change z.val (v i - x) + F (v i - x) = _ - _
      simp only [f, map_sub, LinearMap.add_apply]
      ring
    have maxv (i : ι) : f (v i) ≤ f (v s) := by simpa only [ev, sub_le_sub_iff_right] using hs i
    have fd : f d ≠ 0 := by
      have hz : z.val d = 0 := z.property
      change F d + z.val d ≠ 0
      rw [hz, add_zero]
      exact (show 0 < F (x - v b) by rw [map_sub]; exact sub_pos.mpr (bad b)).ne'
    rw [ev, sub_nonneg]
    apply test f s maxv
    intro g hg
    let r := g d / f d
    let h := g - r • f
    have hd : h d = 0 := by
      simp only [h, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, r]
      rw [div_mul_cancel₀ _ fd, sub_self]
    let u : N := ⟨h, hd⟩
    have flat (i : ι) (hi : l i z + c i = l s z + c s) : l i u = l s u := by
      have he : f (v i) = f (v s) := by simpa only [ev, sub_left_inj] using hi
      change h (v i - x) = h (v s - x)
      simp only [map_sub, h, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, he, hg i he]
    refine ⟨r, fun i => ?_⟩
    have hi : h (v i - x) = h (v s - x) := span u flat i
    simp only [map_sub, h, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hi
    linarith only [hi]
  obtain ⟨i, hi⟩ := upper_envelope_test l c infBound contact (0 : N)
  simp only [map_zero, zero_add, c, map_sub, sub_nonneg] at hi
  exact (bad i).not_ge hi

open scoped ComplexConjugate

private theorem mask_transpose {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset n) (A : Matrix n n ℂ) :
    Matrix.det (fun i => if i ∈ S then A.transpose i else (1 : Matrix n n ℂ) i) =
      Matrix.det (fun i => if i ∈ S then A i else (1 : Matrix n n ℂ) i) := by
  let P : Matrix n n ℂ := diagonal (fun i => if i ∈ S then 1 else 0)
  have mask (M : Matrix n n ℂ) :
      ((fun i => if i ∈ S then M i else (1 : Matrix n n ℂ) i) : Matrix n n ℂ) =
        (1 : Matrix n n ℂ) + P * (M - (1 : Matrix n n ℂ)) := by
    ext i j
    by_cases hi : i ∈ S <;> simp [P, diagonal_mul, hi]
  have hP : P.transpose = P := diagonal_transpose _
  rw [mask, mask, det_one_add_mul_comm, ← det_transpose (1 + (A.transpose - 1) * P)]
  simp only [transpose_add, transpose_one, transpose_mul, transpose_sub, transpose_transpose, hP]

private theorem signed_expansion_complex {n : Type} [Fintype n] [DecidableEq n]
    (V W : Matrix n n ℂ) (hWV : W * V = 1) (a b : n → ℂ) (S : Finset n) :
    let M : Matrix n n ℂ := fun i => if i ∈ S then (diagonal a + V * diagonal b * W) i else (1 : Matrix n n ℂ) i
    M.det = ∑ σ : Equiv.Perm n, (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (∏ i, V i (σ i)) * W.det) * ∏ i ∈ S, (a i + b (σ i)) := by
  classical
  intro M
  have entries (i j : n) : (M * V) i j = (if i ∈ S then a i + b j else 1) * V i j := by
    have e : (diagonal a + V * diagonal b * W) * V = diagonal a * V + V * diagonal b := by
      rw [add_mul, Matrix.mul_assoc (V * diagonal b), hWV, mul_one]
    by_cases hi : i ∈ S
    · calc
        (M * V) i j = ((diagonal a + V * diagonal b * W) * V) i j := by rw [Matrix.mul_apply, Matrix.mul_apply]; simp only [M, hi, if_true]
        _ = _ := by rw [e]; simp [hi, Matrix.diagonal_mul, Matrix.mul_diagonal]; ring
    · calc
        (M * V) i j = ((1 : Matrix n n ℂ) * V) i j := by rw [Matrix.mul_apply, Matrix.mul_apply]; simp only [M, hi, if_false]
        _ = _ := by simp [hi]
  have hv := congrArg Matrix.det hWV
  simp only [det_mul, det_one] at hv
  calc
    M.det = (M * V).transpose.det * W.det := by rw [det_transpose, det_mul]; linear_combination -M.det * hv
    _ = _ := by
      rw [det_apply', Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [transpose_apply, entries, Finset.prod_mul_distrib]
      rw [Finset.prod_ite_mem]
      simp
      ring

private theorem signed_compression {n : Type} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) :
    let w (σ : Equiv.Perm n) :=
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
    (∑ σ, w σ) = 1 ∧
      ∀ (a b : n → ℂ) (S : Finset n),
      let M : Matrix n n ℂ := fun i =>
        if i ∈ S then (diagonal a + U.val * diagonal b * star U.val) i else (1 : Matrix n n ℂ) i
      M.det = ∑ σ, w σ • (∏ i ∈ S, (a i + b (σ i))) := by
  classical
  let V := U.val
  let W := star U.val
  let h (σ : Equiv.Perm n) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, V i (σ i)) * W.det
  have hWV : W * V = 1 := Unitary.coe_star_mul_self U
  have hs : ∑ σ, h σ = 1 := by
    have e := signed_expansion_complex V W hWV (fun _ => 0) (fun _ => 0) ∅
    simpa [h] using e.symm
  change (∑ σ, (h σ).re) = 1 ∧ _
  constructor
  · simpa only [Complex.re_sum, Complex.one_re] using congrArg Complex.re hs
  intro a b S M
  let Z (σ : Equiv.Perm n) := ∏ i ∈ S, (a i + b (σ i))
  change M.det = ∑ σ, (h σ).re • Z σ
  have e : M.det = ∑ σ, h σ * Z σ := signed_expansion_complex V W hWV a b S
  have et := signed_expansion_complex W.transpose V.transpose
    (show V.transpose * W.transpose = 1 by rw [← transpose_mul, hWV, transpose_one]) a b S
  have ht : diagonal a + W.transpose * diagonal b * V.transpose =
      (diagonal a + V * diagonal b * W).transpose := by
    simp only [transpose_add, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
  dsimp only at et
  rw [ht, mask_transpose] at et
  have hw (σ : Equiv.Perm n) :
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, W.transpose i (σ i)) * V.transpose.det = conj (h σ) := by
    simp only [h, V, W, Matrix.star_eq_conjTranspose, transpose_apply, conjTranspose_apply,
      det_transpose, det_conjTranspose, map_mul, map_prod, map_intCast, Complex.star_def, Complex.conj_conj]
  change M.det = ∑ σ : Equiv.Perm n, _ * Z σ at et
  simp_rw [hw] at et
  apply (mul_right_inj' (show (2 : ℂ) ≠ 0 by norm_num)).mp
  calc
    2 * M.det = (∑ σ, h σ * Z σ) + (∑ σ, conj (h σ) * Z σ) := by rw [← e, ← et]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [← add_mul, Complex.add_conj]
      simp [Complex.real_smul, Z, mul_assoc]

open scoped ComplexOrder NNReal

private theorem compression_nonneg {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset n) (A : Matrix n n ℂ) (ha : A.PosSemidef) :
    0 ≤ Matrix.det (fun i => if i ∈ S then A i else (1 : Matrix n n ℂ) i) := by
  let P : Matrix n n ℂ := diagonal (fun i => if i ∈ S then 1 else 0)
  let Q : Matrix n n ℂ := diagonal (fun i => if i ∈ S then 0 else 1)
  have hPP : P * P = P := by
    ext i j
    by_cases he : i = j
    · subst j; by_cases hi : i ∈ S <;> simp [P, hi]
    · simp [P, he]
  have hQ : Q.PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by split <;> simp)
  have hPstar : P.conjTranspose = P := by
    ext i j
    by_cases he : i = j
    · subst j; by_cases hi : i ∈ S <;> simp [P, hi]
    · simp [P, conjTranspose_apply, he, Ne.symm he]
  have hQP : (1 : Matrix n n ℂ) - P = Q := by
    ext i j
    by_cases he : i = j
    · subst j; by_cases hi : i ∈ S <;> simp [P, Q, hi]
    · simp [P, Q, one_apply, he]
  have m : ((fun i => if i ∈ S then A i else (1 : Matrix n n ℂ) i) : Matrix n n ℂ) =
      (1 : Matrix n n ℂ) + P * (A - (1 : Matrix n n ℂ)) := by
    ext i j
    by_cases hi : i ∈ S <;> simp [P, diagonal_mul, hi]
  rw [m]
  have hswap : det (1 + P * (A - 1)) = det (1 + P * (A - 1) * P) := by
    rw [det_one_add_mul_comm (P * (A - 1)) P, ← Matrix.mul_assoc P P, hPP]
  have he : 1 + P * (A - 1) * P = Q + P * A * P := by
    rw [mul_sub, sub_mul, mul_one, hPP, ← hQP]
    abel
  rw [hswap, he]
  simpa only [hPstar] using (hQ.add (ha.conjTranspose_mul_mul_same P)).det_nonneg

private theorem block_marginals {n : Type} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (w : Equiv.Perm n → ℝ)
    (hexp : ∀ (a b : n → ℂ) (S : Finset n),
      let M : Matrix n n ℂ := fun i =>
        if i ∈ S then (diagonal a + U.val * diagonal b * star U.val) i else (1 : Matrix n n ℂ) i
      M.det = ∑ σ, w σ • (∏ i ∈ S, (a i + b (σ i)))) (I J : Finset n) :
    0 ≤ ∑ σ : Equiv.Perm n, w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0) := by
  classical
  let b (i : n) : ℂ := if i ∈ J then 1 else 0
  have hd : (diagonal b).PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by simp [b]; split <;> simp)
  have h := compression_nonneg I _ (hd.mul_mul_conjTranspose_same U.val)
  have e := hexp (fun _ => 0) b I
  simp only [diagonal_zero, zero_add, Matrix.star_eq_conjTranspose] at e
  rw [e] at h
  have r := (Complex.nonneg_iff.mp h).1
  simp only [b, Finset.prod_boole, Complex.re_sum, Complex.real_smul] at r
  convert r using 1
  apply Finset.sum_congr rfl
  intro σ _
  split <;> simp_all

private theorem certificate_nonneg {ι κ : Type} [Fintype ι] (w : ι → ℝ) (B : κ → ι → ℝ)
    (hB : ∀ j, 0 ≤ ∑ i, w i * B j i) {d : ι → ℝ}
    (hd : d ∈ Submodule.span ℝ≥0 (Set.range B)) : 0 ≤ ∑ i, w i * d i := by
  induction hd using Submodule.span_induction with
  | mem x hx => obtain ⟨j,rfl⟩ := hx; exact hB j
  | zero => simp
  | add x y _ _ hx hy => simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib] using add_nonneg hx hy
  | smul r x _ hx =>
    simpa only [Pi.smul_apply, NNReal.smul_def, smul_eq_mul, mul_left_comm (w _),
      ← Finset.mul_sum] using mul_nonneg r.coe_nonneg hx

private theorem fiber_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (v : ι → κ) (F : κ → ℂ) (w : ι → ℝ) :
    (∑ i, w i • F (v i)) = ∑ j, (∑ i, if v i = j then w i else 0) • F j := by
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem products_of_marginals {n : Type} [Fintype n] [DecidableEq n]
    (T : Finset n) (w t : Equiv.Perm n → ℝ)
    (h : ∀ S ⊆ T, ∀ J : Finset n, (∑ σ : Equiv.Perm n, if S.image σ = J then w σ else 0) =
      ∑ σ : Equiv.Perm n, if S.image σ = J then t σ else 0) (a b : n → ℂ) :
    (∑ σ, w σ • (∏ i ∈ T, (a i + b (σ i)))) =
      ∑ σ, t σ • (∏ i ∈ T, (a i + b (σ i))) := by
  classical
  let F (S J : Finset n) : ℂ := (∏ i ∈ S, a i) * ∏ j ∈ J, b j
  have expn (σ : Equiv.Perm n) : (∏ i ∈ T, (a i + b (σ i))) =
      ∑ S ∈ T.powerset, F S ((T \ S).image σ) := by
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro S _
    simp only [F, Finset.prod_image σ.injective.injOn]
  simp_rw [expn, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := T.powerset)]
  apply Finset.sum_congr rfl
  intro S _
  rw [fiber_sum (fun σ : Equiv.Perm n => (T \ S).image σ) (F S) w,
      fiber_sum (fun σ : Equiv.Perm n => (T \ S).image σ) (F S) t]
  simp_rw [h (T \ S) Finset.sdiff_subset]

/-- A finite marginal problem on at most two marked rows. Given normalized
signed masses with nonnegative subset-incidence sums, realize the same
unordered image marginals on the marked rows by a probability distribution. -/
def H1 : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (w : Equiv.Perm n → ℝ),
    (∑ σ, w σ) = 1 →
    (∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0)) →
    ∀ T : Finset n, T.card ≤ 2 →
    ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
      ∀ S ⊆ T, ∀ J : Finset n,
        (∑ σ : Equiv.Perm n, if S.image σ = J then w σ else 0) =
          ∑ σ : Equiv.Perm n, if S.image σ = J then t σ else 0

/-- For a fixed row and retained spectrum, the paired coefficients of the
permutation products form a polytope in two complex coordinates. On a proper
facet test the signed permutation sum of the gaps below the supporting plane.
Only facets involving the second coordinate and with a negative weight off
the face require a test. A nonnegative linear combination of subset
indicators certifies a gap for every unitary. Such gaps are excluded. -/
def H2 : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (a b : n → ℂ)
    (U : unitary (Matrix n n ℂ)) (T : Finset n) (k : n), 3 ≤ T.card → k ∈ T →
    let w (σ : Equiv.Perm n) :=
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
    let v (σ : Equiv.Perm n) : ℂ × ℂ :=
      let p := ∏ i ∈ T.erase k, (a i + b (σ i))
      (p, b (σ k) * p)
    let block (IJ : Finset n × Finset n) (σ : Equiv.Perm n) : ℝ :=
      if ∀ i ∈ IJ.1, σ i ∈ IJ.2 then 1 else 0
    ∀ (f : (ℂ × ℂ) →ₗ[ℝ] ℝ) (s : Equiv.Perm n), (∃ z : ℂ, f (0, z) ≠ 0) →
      (∀ σ, f (v σ) ≤ f (v s)) →
      (∀ g : (ℂ × ℂ) →ₗ[ℝ] ℝ,
        (∀ σ, f (v σ) = f (v s) → g (v σ) = g (v s)) →
        ∃ r : ℝ, ∀ σ, g (v σ) - g (v s) = r * (f (v σ) - f (v s))) →
      (∃ σ, w σ < 0 ∧ f (v σ) < f (v s)) →
      (fun σ => f (v s) - f (v σ)) ∉ Submodule.span ℝ≥0 (Set.range block) →
      0 ≤ ∑ σ, w σ * (f (v s) - f (v σ))

theorem main : H1 → H2 → type_of% @DeterminantalConjecture.determinantal_conjecture := by
  classical
  intro small facet n _ _ a b U V
  simp only [Unitary.coe_star]
  rw [relative_det]
  let W := star U * V
  let w (σ : Equiv.Perm n) :=
    (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, W.val i (σ i)) * (star W.val).det).re
  let Z (T : Finset n) (σ : Equiv.Perm n) := ∏ i ∈ T, (a i + b (σ i))
  obtain ⟨weight_sum, det_sum⟩ := signed_compression W
  change (∑ σ, w σ) = 1 at weight_sum
  have encl (T : Finset n) : (∑ σ, w σ • Z T σ) ∈ convexHull ℝ (Set.range (Z T)) := by
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      by_cases hsmall : T.card ≤ 2
      · obtain ⟨t, ht, ht1, hm⟩ := small n w weight_sum (block_marginals W w det_sum) T hsmall
        change (∑ σ, w σ • (∏ i ∈ T, (a i + b (σ i)))) ∈ _
        rw [products_of_marginals T w t hm]
        exact (convex_convexHull ℝ _).sum_mem (fun σ _ => ht σ) ht1
          (fun σ _ => subset_convexHull ℝ _ ⟨σ, rfl⟩)
      have hlarge : 3 ≤ T.card := by omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
      let p := Z (T.erase k)
      let v (σ : Equiv.Perm n) : ℂ × ℂ := (p σ, b (σ k) * p σ)
      let x := ∑ σ, w σ • v σ
      have joint : x ∈ convexHull ℝ (Set.range v) := by
        apply lifted_facet_test
        intro f s hs hface
        have gap : (∑ σ, w σ * (f (v s) - f (v σ))) = f (v s) - f x := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, weight_sum,
            one_mul, x, map_sum, map_smul, smul_eq_mul]
        by_cases hn : ∃ z : ℂ, f (0, z) ≠ 0
        · rw [← sub_nonneg, ← gap]
          by_cases hneg : ∃ σ, w σ < 0 ∧ f (v σ) < f (v s)
          · let block (IJ : Finset n × Finset n) (σ : Equiv.Perm n) : ℝ :=
              if ∀ i ∈ IJ.1, σ i ∈ IJ.2 then 1 else 0
            by_cases hcert : (fun σ => f (v s) - f (v σ)) ∈ Submodule.span ℝ≥0 (Set.range block)
            · exact certificate_nonneg w block
                (fun IJ => block_marginals W w det_sum IJ.1 IJ.2) hcert
            · exact facet n a b W T k hlarge hk f s hn hs hface hneg hcert
          · apply Finset.sum_nonneg
            intro σ _
            by_cases hm : f (v σ) = f (v s)
            · rw [hm, sub_self, mul_zero]
            · exact mul_nonneg (le_of_not_gt fun hw => hneg ⟨σ, hw, lt_of_le_of_ne (hs σ) hm⟩)
                (sub_nonneg.mpr (hs σ))
        · push Not at hn
          let g := f.comp (LinearMap.inl ℝ ℂ ℂ)
          have fst (u q : ℂ) : f (u,q) = g u := by
            have he : (u,q) = (u,0) + (0,q) := by simp
            rw [he, map_add, hn, add_zero]
            rfl
          have hp (σ : Equiv.Perm n) : g (p σ) ≤ g (p s) := by
            simpa only [v, fst] using hs σ
          have incl : convexHull ℝ (Set.range p) ⊆ {y | g y ≤ g (p s)} :=
            convexHull_min (by rintro _ ⟨σ, rfl⟩; exact hp σ) (convex_halfSpace_le g.isLinear _)
          have lower := incl (ih (T.erase k) (Finset.erase_ssubset hk))
          change g (∑ σ, w σ • p σ) ≤ g (p s) at lower
          change f (∑ σ, w σ • v σ) ≤ f (v s)
          rw [map_sum]
          simp_rw [map_smul]
          simpa only [map_sum, map_smul, v, fst] using lower
      let e : (ℂ × ℂ) →ₗ[ℝ] ℂ :=
        (LinearMap.mulLeft ℝ (a k)).comp (LinearMap.fst ℝ ℂ ℂ) + LinearMap.snd ℝ ℂ ℂ
      have eval (σ : Equiv.Perm n) : e (v σ) = Z T σ := by
        change a k * p σ + b (σ k) * p σ = ∏ i ∈ T, (a i + b (σ i))
        rw [← add_mul, ← Finset.mul_prod_erase _ _ hk]
      have h : e x ∈ convexHull ℝ (Set.range (e ∘ v)) := by
        rw [Set.range_comp, ← e.image_convexHull]
        exact ⟨_, joint, rfl⟩
      simpa only [x, map_sum, map_smul, Function.comp_def, eval] using h
  have hd := det_sum a b Finset.univ
  simp only [Finset.mem_univ, if_true] at hd
  rw [hd]
  exact encl Finset.univ

end OMA.R_DeterminantalConjecture_determinantal_conjecture_R1
