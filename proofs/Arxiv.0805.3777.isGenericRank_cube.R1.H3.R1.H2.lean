import OMAReductions.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1

/-! Spanning tangent spaces for the perfect quasicubic tensor formats.

For a block of three rows and two or three columns, put one central point
per column. Variations from the other cells in the same row or column enter
as partial tangent spaces. Two pencil configurations and six additional
integer matrix certificates cover the possible blocks. Repeating the three-slice
certificates gives all required dimensions. The matrix entries encode the
tangent spaces themselves, and Lean verifies every scaled right inverse.

A different specialization can certify each cell. A product of determinant
polynomials puts all cells at a common specialization over the complex numbers.
The grid then gives a full-rank tangent configuration meeting any prescribed
nonempty principal open.

The quasicubic formats are due to V. Strassen, Rank and optimal computation
of generic tensors (1983), Corollary 3.10. For the statement and the
tangent-space grid method, see T. Lickteig, Typical tensorial rank (1985),
Proposition 4.2 and Sections 2–4.
-/

namespace TensorRankCore

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩

abbrev Row (d e : ℕ) := Fin d × Fin d × Fin e
abbrev Param (d e s : ℕ) := Fin s × (Fin d ⊕ (Fin d ⊕ Fin e))

noncomputable def tangent (d e s : ℕ) : Matrix (Row d e) (Param d e s)
    (MvPolynomial (Param d e s) ℂ)
  | (i,j,k), (t, Sum.inl h) =>
      if h = i then X (t, Sum.inr (Sum.inl j)) * X (t, Sum.inr (Sum.inr k)) else 0
  | (i,j,k), (t, Sum.inr (Sum.inl h)) =>
      if h = j then X (t, Sum.inl i) * X (t, Sum.inr (Sum.inr k)) else 0
  | (i,j,k), (t, Sum.inr (Sum.inr h)) =>
      if h = k then X (t, Sum.inl i) * X (t, Sum.inr (Sum.inl j)) else 0

lemma tangent_action {d e s : ℕ} (x y : Param d e s → ℂ) (i j : Fin d) (k : Fin e) :
    ((tangent d e s).map (eval x)).mulVec y (i,j,k) =
      ∑ t, (y (t, Sum.inl i) * (x (t, Sum.inr (Sum.inl j)) * x (t, Sum.inr (Sum.inr k))) +
        x (t, Sum.inl i) * (y (t, Sum.inr (Sum.inl j)) * x (t, Sum.inr (Sum.inr k))) +
        x (t, Sum.inl i) * (x (t, Sum.inr (Sum.inl j)) * y (t, Sum.inr (Sum.inr k)))) := by
  classical
  change (∑ z : Param d e s, eval x (tangent d e s (i,j,k) z) * y z) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [tangent, apply_ite, ite_mul, Finset.sum_ite_eq']
  ring

def Spans {d e s : ℕ} (x : Param d e s → ℂ) : Prop :=
  ∀ T : Fin d → Fin d → Fin e → ℂ,
    ∃ u v : Fin s → Fin d → ℂ, ∃ w : Fin s → Fin e → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i * (x (t, Sum.inr (Sum.inl j)) * x (t, Sum.inr (Sum.inr k))) +
        x (t, Sum.inl i) * (v t j * x (t, Sum.inr (Sum.inr k))) +
        x (t, Sum.inl i) * (x (t, Sum.inr (Sum.inl j)) * w t k))

lemma spans_iff {d e s : ℕ} (x : Param d e s → ℂ) :
    Spans x ↔ Function.Surjective ((tangent d e s).map (eval x)).mulVec := by
  constructor
  · intro h T
    obtain ⟨u, v, w, huv⟩ := h fun i j k => T (i,j,k)
    let y : Param d e s → ℂ := fun z => Sum.elim (u z.1) (Sum.elim (v z.1) (w z.1)) z.2
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨i,j,k⟩ := z
    rw [tangent_action]
    exact (huv i j k).symm
  · intro h T
    obtain ⟨y, hy⟩ := h fun z => T z.1 z.2.1 z.2.2
    refine ⟨fun t i => y (t, Sum.inl i), fun t j => y (t, Sum.inr (Sum.inl j)),
      fun t k => y (t, Sum.inr (Sum.inr k)), ?_⟩
    intro i j k
    exact (congrFun hy (i,j,k)).symm.trans (tangent_action x y i j k)

/-- For a rectangular tangent map, one spanning configuration is enough to meet
every nonempty principal open in the space of factor vectors. -/
lemma dense_spanning {d e s : ℕ} (x₀ : Param d e s → ℂ) (h₀ : Spans x₀)
    (P : MvPolynomial (Param d e s) ℂ) (hP : P ≠ 0) :
    ∃ x : Param d e s → ℂ, eval x P ≠ 0 ∧ Spans x := by
  obtain ⟨Q, hQ, h⟩ := surjectivity_polynomial (tangent d e s) x₀ ((spans_iff _).mp h₀)
  obtain ⟨x, hxP, hxQ⟩ := avoid_two hP hQ
  exact ⟨x, hxP, (spans_iff _).mpr (h x hxQ)⟩

def Dense (d e s : ℕ) : Prop :=
  ∀ P : MvPolynomial (Param d e s) ℂ, P ≠ 0 →
    ∃ x : Param d e s → ℂ, eval x P ≠ 0 ∧ Spans x

lemma core_of_quasicubic_witnesses
    (hplus : ∀ d : ℕ, 3 ≤ d → d % 3 ≠ 2 →
      ∃ x : Param d (d + 2) (d * (d + 2) / 3) → ℂ, Spans x)
    (hminus : ∀ d : ℕ, 9 ≤ d → d % 3 = 0 →
      ∃ x : Param d (d - 1) (d * d / 3) → ℂ, Spans x) :
    OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1.H2 := by
  intro n hn h7
  change Dense (if n % 3 = 1 then n - 1 else n - 2) (if n % 3 = 1 then n - 2 else n)
    ((if n % 3 = 1 then n - 1 else n - 2) *
      (if n % 3 = 1 then (if n % 3 = 1 then n - 1 else n - 2) else n) / 3)
  by_cases hc : n % 3 = 1
  · simp only [if_pos hc]
    have hw := hminus (n - 1) (by omega) (by omega)
    have he : n - 1 - 1 = n - 2 := by omega
    rw [he] at hw
    obtain ⟨x, hx⟩ := hw
    exact fun P hP => dense_spanning x hx P hP
  · simp only [if_neg hc]
    have he : n - 2 + 2 = n := by omega
    have hw := hplus (n - 2) (by omega) (by omega)
    rw [he] at hw
    obtain ⟨x, hx⟩ := hw
    exact fun P hP => dense_spanning x hx P hP

end TensorRankCore

namespace TensorRankCore

lemma of_reindexed_config {I J K R : Type} [Fintype R] {d e s : ℕ}
    (ei : Fin d ≃ I) (ej : Fin d ≃ J) (ek : Fin e ≃ K) (er : Fin s ≃ R)
    (a : R → I → ℂ) (b : R → J → ℂ) (c : R → K → ℂ)
    (H : ∀ T : I → J → K → ℂ, ∃ u : R → I → ℂ, ∃ v : R → J → ℂ, ∃ w : R → K → ℂ, ∀ i j k,
      T i j k = ∑ z, (u z i * (b z j * c z k) + a z i * (v z j * c z k) +
        a z i * (b z j * w z k))) :
    ∃ x : Param d e s → ℂ, Spans x := by
  let x : Param d e s → ℂ := fun p => Sum.elim (fun i => a (er p.1) (ei i))
    (Sum.elim (fun j => b (er p.1) (ej j)) (fun k => c (er p.1) (ek k))) p.2
  refine ⟨x, ?_⟩
  intro T
  obtain ⟨u,v,w,hT⟩ := H fun i j k => T (ei.symm i) (ej.symm j) (ek.symm k)
  refine ⟨fun t i => u (er t) (ei i), fun t j => v (er t) (ej j), fun t k => w (er t) (ek k), ?_⟩
  intro i j k
  have he := hT (ei i) (ej j) (ek k)
  simp only [Equiv.symm_apply_apply] at he
  exact he.trans ((er.sum_comp (fun z => u z (ei i) * (b z (ej j) * c z (ek k)) +
    a z (ei i) * (v z (ej j) * c z (ek k)) + a z (ei i) * (b z (ej j) * w z (ek k)))).symm)


end TensorRankCore

namespace TensorRankFlexible

open MvPolynomial

abbrev Slot (G : Type) {H : Type} (J : H → Type) := G × Sigma J
abbrev Parameters (G : Type) {H : Type} (J : H → Type) (W : Type) :=
  (Slot G J) × (Fin 3 ⊕ (Sigma J ⊕ W))
abbrev Columns (G : Type) {H : Type} (J : H → Type) (W : Type) (h : H) :=
  (G × J h × Fin 3) ⊕ ((Sigma J × J h) ⊕ (J h × W))

def Config (A B C R : Type) [Fintype R] : Prop :=
  ∃ a : R → A → ℂ, ∃ b : R → B → ℂ, ∃ c : R → C → ℂ,
    ∀ T : A → B → C → ℂ, ∃ u : R → A → ℂ, ∃ v : R → B → ℂ, ∃ w : R → C → ℂ,
      ∀ i j k, T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
        a t i * (b t j * w t k))

/-- Restrict the tangent equations to one output block. Variations of the first
factor come from every row in its column, variations of the second factor
from every column in its row, and the third factor varies in its own cell. -/
def Local {G H W : Type} {J : H → Type} [Fintype G] [Fintype H] [∀ h, Fintype (J h)]
    (a : Slot G J → Fin 3 → ℂ) (b : Slot G J → Sigma J → ℂ) (c : Slot G J → W → ℂ)
    (g : G) (h : H) : Prop :=
  ∀ T : Fin 3 → J h → W → ℂ,
    ∃ u : G → J h → Fin 3 → ℂ, ∃ v : Sigma J → J h → ℂ, ∃ w : J h → W → ℂ, ∀ i j k,
      T i j k =
        (∑ l, ∑ t, u l t i * (b (l,⟨h,t⟩) ⟨h,j⟩ * c (l,⟨h,t⟩) k)) +
        (∑ z, a (g,z) i * (v z j * c (g,z) k)) +
        ∑ t, a (g,⟨h,t⟩) i * (b (g,⟨h,t⟩) ⟨h,j⟩ * w t k)

def padA {G : Type} [DecidableEq G] (g : G) (f : Fin 3 → ℂ) (i : G × Fin 3) : ℂ :=
  if g = i.1 then f i.2 else 0
def padB {H : Type} {J : H → Type} [DecidableEq H] (h : H) (f : Sigma J → ℂ) (j : Sigma J) : ℂ :=
  if h = j.1 then f j else 0

lemma sum_at {H : Type} {J : H → Type} [Fintype H] [∀ h, Fintype (J h)] (h : H)
    (F : Sigma J → ℂ) (hzero : ∀ u, u ≠ h → ∀ j : J u, F ⟨u,j⟩ = 0) :
    ∑ z, F z = ∑ j : J h, F ⟨h,j⟩ := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_eq_single h
  · intro u _ hu
    simp [hzero u hu]
  · simp

/-- Pad the first and second factors in their assigned blocks. Each output block
can then use its own variation coefficients. -/
lemma assemble {G H W : Type} {J : H → Type} [Fintype G] [Fintype H] [∀ h, Fintype (J h)]
    [DecidableEq G] [DecidableEq H] (a : Slot G J → Fin 3 → ℂ)
    (b : Slot G J → Sigma J → ℂ) (c : Slot G J → W → ℂ) (hc : ∀ g h, Local a b c g h) :
    Config (G × Fin 3) (Sigma J) W (Slot G J) := by
  classical
  refine ⟨fun z => padA z.1 (a z), fun z => padB z.2.1 (b z), c, ?_⟩
  intro T
  choose U V Z good using fun g h => hc g h (fun i j k => T (g,i) ⟨h,j⟩ k)
  refine ⟨fun z i => U i.1 z.2.1 z.1 z.2.2 i.2, fun z j => V z.1 j.1 z.2 j.2,
    fun z => Z z.1 z.2.1 z.2.2, ?_⟩
  rintro ⟨g,i⟩ ⟨h,j⟩ k
  rw [good g h i j k]
  simp only [Finset.sum_add_distrib]
  congr 1
  · congr 1
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro l _
      symm
      refine (sum_at h _ ?_).trans ?_
      · intro z hz t
        simp [padB, hz]
      · simp [padB]
    · simp [Fintype.sum_prod_type, padA, ite_mul, Finset.sum_ite_irrel]
  · rw [Fintype.sum_prod_type]
    simp only [padA, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    symm
    refine (sum_at h _ ?_).trans ?_
    · intro z hz t
      simp [padB, hz]
    · simp [padB]

def av {G H W : Type} {J : H → Type} (x : Parameters G J W → ℂ) (z : Slot G J) (i : Fin 3) := x (z, Sum.inl i)
def bv {G H W : Type} {J : H → Type} (x : Parameters G J W → ℂ) (z : Slot G J) (j : Sigma J) := x (z, Sum.inr (Sum.inl j))
def cv {G H W : Type} {J : H → Type} (x : Parameters G J W → ℂ) (z : Slot G J) (k : W) := x (z, Sum.inr (Sum.inr k))

noncomputable def mat {G H W : Type} {J : H → Type} [∀ h, DecidableEq (J h)] [DecidableEq W]
    (g : G) (h : H) : Matrix (Fin 3 × J h × W) (Columns G J W h) (MvPolynomial (Parameters G J W) ℂ)
  | (i,j,k), Sum.inl (l,t,q) =>
    if q=i then X ((l,⟨h,t⟩), Sum.inr (Sum.inl ⟨h,j⟩)) * X ((l,⟨h,t⟩), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inl (z,q)) =>
    if q=j then X ((g,z), Sum.inl i) * X ((g,z), Sum.inr (Sum.inr k)) else 0
  | (i,j,k), Sum.inr (Sum.inr (t,q)) =>
    if q=k then X ((g,⟨h,t⟩), Sum.inl i) * X ((g,⟨h,t⟩), Sum.inr (Sum.inl ⟨h,j⟩)) else 0

lemma act {G H W : Type} {J : H → Type} [Fintype G] [Fintype H] [Fintype W]
    [∀ h, Fintype (J h)] [∀ h, DecidableEq (J h)] [DecidableEq W]
    (g : G) (h : H) (x : Parameters G J W → ℂ) (y : Columns G J W h → ℂ) (i : Fin 3) (j : J h) (k : W) :
    ((mat g h).map (eval x)).mulVec y (i,j,k) =
      (∑ l, ∑ t, y (Sum.inl (l,t,i)) * (bv x (l,⟨h,t⟩) ⟨h,j⟩ * cv x (l,⟨h,t⟩) k)) +
      (∑ z, av x (g,z) i * (y (Sum.inr (Sum.inl (z,j))) * cv x (g,z) k)) +
      ∑ t, av x (g,⟨h,t⟩) i * (bv x (g,⟨h,t⟩) ⟨h,j⟩ * y (Sum.inr (Sum.inr (t,k)))) := by
  classical
  change (∑ z : Columns G J W h, eval x (mat g h (i,j,k) z) * y z) = _
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, mat, av, bv, cv, apply_ite,
    Finset.sum_ite_eq', mul_assoc, mul_comm, add_assoc]

lemma local_iff {G H W : Type} {J : H → Type} [Fintype G] [Fintype H] [Fintype W]
    [∀ h, Fintype (J h)] [∀ h, DecidableEq (J h)] [DecidableEq W]
    (g : G) (h : H) (x : Parameters G J W → ℂ) :
    Local (av x) (bv x) (cv x) g h ↔ Function.Surjective ((mat g h).map (eval x)).mulVec := by
  constructor
  · intro hT T
    obtain ⟨u,v,w,hv⟩ := hT fun i j k => T (i,j,k)
    let y : Columns G J W h → ℂ := Sum.elim (fun z => u z.1 z.2.1 z.2.2)
      (Sum.elim (fun z => v z.1 z.2) (fun z => w z.1 z.2))
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨i,j,k⟩ := z
    exact (act g h x y i j k).trans (hv i j k).symm
  · intro hT T
    obtain ⟨y,hy⟩ := hT fun z => T z.1 z.2.1 z.2.2
    refine ⟨fun l t i => y (Sum.inl (l,t,i)), fun z j => y (Sum.inr (Sum.inl (z,j))),
      fun t k => y (Sum.inr (Sum.inr (t,k))), ?_⟩
    intro i j k
    exact (congrFun hy (i,j,k)).symm.trans (act g h x y i j k)

lemma grid_config {G H W : Type} {J : H → Type} [Fintype G] [Fintype H] [Fintype W]
    [∀ h, Fintype (J h)] [∀ h, DecidableEq (J h)] [DecidableEq W] [DecidableEq G] [DecidableEq H]
    (hw : ∀ g h, ∃ x : Parameters G J W → ℂ, Local (av x) (bv x) (cv x) g h) :
    Config (G × Fin 3) (Sigma J) W (Slot G J) := by
  classical
  have hs (p : G × H) : ∃ x : Parameters G J W → ℂ, Function.Surjective ((mat p.1 p.2).map (eval x)).mulVec := by
    obtain ⟨x,hx⟩ := hw p.1 p.2
    exact ⟨x,(local_iff _ _ _).mp hx⟩
  obtain ⟨x,_,hx⟩ := TensorRankCore.simultaneous_surjectivity (fun p : G × H => mat p.1 p.2) hs 1 one_ne_zero
  exact assemble _ _ _ fun g h => (local_iff g h x).mpr (hx (g,h))

end TensorRankFlexible


namespace TensorRankFlexible

/-- A coordinate cell with complete tangent spaces at its own points and
partial variations arriving from the other rows and columns of the grid. -/
def Cell (C W U V : Type) [Fintype C] [Fintype U] [Fintype V] : Prop :=
  ∃ a : C → Fin 3 → ℂ, ∃ b : C → C → ℂ, ∃ c : C → W → ℂ,
    ∃ bu : U → C → ℂ, ∃ cu : U → W → ℂ, ∃ av : V → Fin 3 → ℂ, ∃ cv : V → W → ℂ,
    ∀ T : Fin 3 → C → W → ℂ,
      ∃ u₀ : C → Fin 3 → ℂ, ∃ v₀ : C → C → ℂ, ∃ w : C → W → ℂ,
        ∃ u : U → Fin 3 → ℂ, ∃ v : V → C → ℂ, ∀ i j k,
        T i j k =
          ((∑ t, u₀ t i * (b t j * c t k)) + ∑ q, u q i * (bu q j * cu q k)) +
          ((∑ t, a t i * (v₀ t j * c t k)) + ∑ q, av q i * (v q j * cv q k)) +
          ∑ t, a t i * (b t j * w t k)

def splitColumn {H : Type} {J : H → Type} [DecidableEq H] (h : H) :
    Sigma J ≃ J h ⊕ {z : Sigma J // z.1 ≠ h} where
  toFun z := if e : z.1 = h then Sum.inl (e ▸ z.2) else Sum.inr ⟨z,e⟩
  invFun := Sum.elim (fun t => ⟨h,t⟩) Subtype.val
  left_inv := by
    rintro ⟨l,t⟩
    by_cases e : l = h
    · subst h
      simp
    · simp [e]
  right_inv := by
    rintro (t | ⟨⟨l,t⟩,he⟩)
    · simp
    · simp [he]

lemma splitColumn_self {H : Type} {J : H → Type} [DecidableEq H] (h : H) (t : J h) :
    splitColumn h ⟨h,t⟩ = Sum.inl t := by simp [splitColumn]

lemma extend_cell {G H W : Type} {J : H → Type} [Fintype G] [Fintype H] [∀ h, Fintype (J h)]
    [DecidableEq G] [DecidableEq H] (g : G) (h : H)
    (hs : Cell (J h) W ({l : G // l ≠ g} × J h) {z : Sigma J // z.1 ≠ h}) :
    ∃ x : Parameters G J W → ℂ, Local (av x) (bv x) (cv x) g h := by
  classical
  obtain ⟨a,b,c,bu,cu,aa,cc,solve⟩ := hs
  let r := (Equiv.optionSubtypeNe g).symm
  let e := @splitColumn H J _ h
  let A (z : Slot G J) (i : Fin 3) : ℂ := (e z.2).elim (fun t => a t i) (fun v => aa v i)
  let B (z : Slot G J) (j : Sigma J) : ℂ := (e j).elim
    (fun j => (e z.2).elim (fun t => (r z.1).elim (b t j) (fun l => bu (l,t) j)) (fun _ => 0))
    (fun _ => 0)
  let D (z : Slot G J) (k : W) : ℂ := (e z.2).elim
    (fun t => (r z.1).elim (c t k) (fun l => cu (l,t) k)) (fun v => cc v k)
  let x : Parameters G J W → ℂ := fun p => Sum.elim (A p.1) (Sum.elim (B p.1) (D p.1)) p.2
  refine ⟨x, ?_⟩
  intro T
  obtain ⟨u₀,v₀,w,u,v,ht⟩ := solve T
  refine ⟨fun l t i => (r l).elim (u₀ t i) (fun l => u (l,t) i),
    fun z j => (e z).elim (fun t => v₀ t j) (fun q => v q j), w, ?_⟩
  intro i j k
  have er : r g = none := Equiv.optionSubtypeNe_symm_self g
  have ee (t : J h) : e ⟨h,t⟩ = Sum.inl t := splitColumn_self h t
  have hu := r.sum_comp (fun o => ∑ t : J h,
    o.elim (u₀ t i) (fun l => u (l,t) i) * (o.elim (b t j) (fun l => bu (l,t) j) *
      o.elim (c t k) (fun l => cu (l,t) k)))
  have hv := e.sum_comp (fun o => o.elim (fun t => a t i) (fun q => aa q i) *
    (o.elim (fun t => v₀ t j) (fun q => v q j) * o.elim (fun t => c t k) (fun q => cc q k)))
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some] at hu
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hv
  rw [ht i j k]
  simp only [av, bv, cv, x, A, B, D, Sum.elim_inl, Sum.elim_inr, ee, er, Option.elim_none,
    Fintype.sum_prod_type]
  rw [hu]
  congr 1
  congr 1
  exact hv.symm

end TensorRankFlexible


namespace TensorRankFlexible

def tagA {p : ℕ} (t : Fin p) (i : Fin 3) : ℂ := if i.val = t.val then 1 else 0
def tagB {p : ℕ} (t j : Fin p) : ℂ := if t = j then 1 else 0

lemma diagonal {p : ℕ} (i : Fin 3) (j : Fin p) (d : Fin p → ℂ) :
    (∑ t, tagA t i * (tagB t j * d t)) = if i.val = j.val then d j else 0 := by
  simp [tagA, tagB, ite_mul, mul_ite, Finset.sum_ite_eq']

/-- The first two factors of the p central points are matching coordinate
vectors. The sets U and V index the partial tangent spaces from other cells. -/
def Tile (p : ℕ) (W U V : Type) [Fintype U] [Fintype V] (c : Fin p → W → ℂ) : Prop :=
  ∃ bu : U → Fin p → ℂ, ∃ cu : U → W → ℂ, ∃ av : V → Fin 3 → ℂ, ∃ cv : V → W → ℂ,
    ∀ T : Fin 3 → Fin p → W → ℂ,
      ∃ u₀ : Fin p → Fin 3 → ℂ, ∃ v₀ : Fin p → Fin p → ℂ, ∃ d : Fin p → W → ℂ,
        ∃ u : U → Fin 3 → ℂ, ∃ v : V → Fin p → ℂ, ∀ i j k,
        T i j k =
          ((∑ t, u₀ t i * (tagB t j * c t k)) + ∑ q, u q i * (bu q j * cu q k)) +
          ((∑ t, tagA t i * (v₀ t j * c t k)) + ∑ q, av q i * (v q j * cv q k)) +
          (if i.val = j.val then d j k else 0)

lemma tile_cell {p : ℕ} {W U V : Type} [Fintype U] [Fintype V] {c : Fin p → W → ℂ}
    (tile : Tile p W U V c) : Cell (Fin p) W U V := by
  obtain ⟨bu,cu,av,cv,hs⟩ := tile
  refine ⟨tagA,tagB,c,bu,cu,av,cv,?_⟩
  intro T
  obtain ⟨u₀,v₀,d,u,v,h⟩ := hs T
  exact ⟨u₀,v₀,d,u,v,fun i j k => by simpa only [diagonal] using h i j k⟩

/-- Adjoin independent slices on which the central third factors vanish. The
variations of those third factors still provide all diagonal directions. -/
lemma tile_add {p : ℕ} {W U V X S R : Type} [Fintype U] [Fintype V] [Fintype S] [Fintype R]
    {c : Fin p → W → ℂ} (h : Tile p W U V c) (r : Tile p X S R (fun _ _ => 0)) :
    Tile p (W ⊕ X) (U ⊕ S) (V ⊕ R) (fun t => Sum.elim (c t) (fun _ => 0)) := by
  obtain ⟨bu,cu,av,cv,f⟩ := h
  obtain ⟨bs,cs,ar,cr,g⟩ := r
  refine ⟨Sum.elim bu bs, Sum.elim (fun q => Sum.elim (cu q) (fun _ => 0))
    (fun q => Sum.elim (fun _ => 0) (cs q)), Sum.elim av ar,
    Sum.elim (fun q => Sum.elim (cv q) (fun _ => 0)) (fun q => Sum.elim (fun _ => 0) (cr q)), ?_⟩
  intro T
  obtain ⟨u₀,v₀,d,u,v,ht⟩ := f fun i j k => T i j (Sum.inl k)
  obtain ⟨_,_,dr,ur,vr,hr⟩ := g fun i j k => T i j (Sum.inr k)
  refine ⟨u₀,v₀,fun j => Sum.elim (d j) (dr j), Sum.elim u ur, Sum.elim v vr, ?_⟩
  intro i j k
  cases k with
  | inl k => simpa [Fintype.sum_sum_type] using ht i j k
  | inr k => simpa [Fintype.sum_sum_type] using hr i j k

lemma tile_repeat {p : ℕ} {W U V : Type} [Fintype U] [Fintype V] (L : Type)
    [Fintype L] [DecidableEq L] (h : Tile p W U V (fun _ _ => 0)) :
    Tile p (L × W) (L × U) (L × V) (fun _ _ => 0) := by
  classical
  obtain ⟨bu,cu,av,cv,hs⟩ := h
  refine ⟨fun q => bu q.2, fun q k => if q.1 = k.1 then cu q.2 k.2 else 0,
    fun q => av q.2, fun q k => if q.1 = k.1 then cv q.2 k.2 else 0, ?_⟩
  intro T
  choose u₀ v₀ d u v hT using fun l : L => hs (fun i j k => T i j (l,k))
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun j k => d k.1 j k.2,
    fun q => u q.1 q.2, fun q => v q.1 q.2, ?_⟩
  rintro i j ⟨l,k⟩
  simpa [Fintype.sum_prod_type, mul_ite, Finset.sum_ite_irrel] using hT l i j k

lemma transport_cell {C W U V X S R : Type} [Fintype C] [Fintype U] [Fintype V]
    [Fintype S] [Fintype R] (ew : X ≃ W) (eu : S ≃ U) (ev : R ≃ V)
    (h : Cell C W U V) : Cell C X S R := by
  obtain ⟨a,b,c,bu,cu,av,cv,hs⟩ := h
  refine ⟨a,b,fun t k => c t (ew k), fun q => bu (eu q), fun q k => cu (eu q) (ew k),
    fun q => av (ev q), fun q k => cv (ev q) (ew k), ?_⟩
  intro T
  obtain ⟨u₀,v₀,w,u,v,hT⟩ := hs fun i j k => T i j (ew.symm k)
  refine ⟨u₀,v₀,fun t k => w t (ew k), fun q => u (eu q), fun q => v (ev q), ?_⟩
  intro i j k
  have hu := eu.sum_comp (fun q => u q i * (bu q j * cu q (ew k)))
  have hv := ev.sum_comp (fun q => av q i * (v q j * cv q (ew k)))
  simpa only [Equiv.symm_apply_apply, hu, hv] using hT i j (ew k)

end TensorRankFlexible


namespace TensorRankFlexible.Finite

abbrev Row (p w : ℕ) := Fin 3 × Fin p × Fin w
abbrev Column (p w u v : ℕ) := (Fin p × Fin 3) ⊕ ((Fin u × Fin 3) ⊕
  ((Fin p × Fin p) ⊕ ((Fin v × Fin p) ⊕ (Fin p × Fin w))))

/-- The five consecutive groups of columns are the two first-factor
variations, the two second-factor variations, and the diagonal directions. -/
def colIndex {p w u v : ℕ} : Column p w u v → ℕ
  | Sum.inl (t,h) => t.val * 3 + h.val
  | Sum.inr (Sum.inl (t,h)) => 3*p + t.val * 3 + h.val
  | Sum.inr (Sum.inr (Sum.inl (t,h))) => 3*p + 3*u + t.val * p + h.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (t,h)))) => 3*p + 3*u + p*p + t.val * p + h.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (t,h)))) => 3*p + 3*u + p*p + v*p + t.val * w + h.val

def unpack {p w u v : ℕ} (A : Array ℤ) : Matrix (Column p w u v) (Row p w) ℤ :=
  fun q ⟨i,j,k⟩ => A[colIndex q * (3*p*w) + (i.val*p+j.val)*w+k.val]?.getD 0

def matrix {p w u v : ℕ} (c : Fin p → Fin w → ℤ) (b₁ : Fin u → Fin p → ℤ)
    (c₁ : Fin u → Fin w → ℤ) (a₂ : Fin v → Fin 3 → ℤ) (c₂ : Fin v → Fin w → ℤ) :
    Matrix (Row p w) (Column p w u v) ℤ
  | (i,j,k), Sum.inl (t,h) => if h=i then (if t=j then c t k else 0) else 0
  | (i,j,k), Sum.inr (Sum.inl (t,h)) => if h=i then b₁ t j * c₁ t k else 0
  | (i,j,k), Sum.inr (Sum.inr (Sum.inl (t,h))) =>
      if h=j then (if i.val=t.val then c t k else 0) else 0
  | (i,j,k), Sum.inr (Sum.inr (Sum.inr (Sum.inl (t,h)))) =>
      if h=j then a₂ t i * c₂ t k else 0
  | (i,j,k), Sum.inr (Sum.inr (Sum.inr (Sum.inr (t,h)))) =>
      if h=k then (if t=j then (if i.val=j.val then 1 else 0) else 0) else 0

lemma of_scaled_inverse {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
    (A : Matrix I K ℤ) (B : Matrix K I ℤ) (d : ℤ) (hd : d ≠ 0) (h : A * B = d • 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let φ := Int.castRingHom ℂ
  have hc : A.map φ * B.map φ = (d : ℂ) • (1 : Matrix I I ℂ) := by
    rw [← Matrix.map_mul, h]
    ext i j
    change φ (d • ((1 : Matrix I I ℤ) i j)) = (d : ℂ) • ((1 : Matrix I I ℂ) i j)
    by_cases he : i=j <;> simp [φ, Matrix.one_apply, he]
  change Function.Surjective (A.map φ).mulVec
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨(d : ℂ)⁻¹ • B.map φ, ?_⟩
  rw [Matrix.mul_smul, hc, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hd), one_smul]

lemma tile_of_matrix {p w u v : ℕ} (c : Fin p → Fin w → ℤ) (bu : Fin u → Fin p → ℤ)
    (cu : Fin u → Fin w → ℤ) (av : Fin v → Fin 3 → ℤ) (cv : Fin v → Fin w → ℤ)
    (hs : Function.Surjective ((matrix c bu cu av cv).map (Int.castRingHom ℂ)).mulVec) :
    Tile p (Fin w) (Fin u) (Fin v) (fun t k => (c t k : ℂ)) := by
  classical
  refine ⟨fun t j => bu t j, fun t k => cu t k, fun t i => av t i, fun t k => cv t k, ?_⟩
  intro T
  obtain ⟨y,hy⟩ := hs fun z => T z.1 z.2.1 z.2.2
  refine ⟨fun t i => y (Sum.inl (t,i)), fun t j => y (Sum.inr (Sum.inr (Sum.inl (t,j)))),
    fun t k => y (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t,k))))), fun t i => y (Sum.inr (Sum.inl (t,i))),
    fun t j => y (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t,j))))), ?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : Column p w u v, ((matrix c bu cu av cv (i,j,k) z : ℤ) : ℂ) * y z) = _
  simp [matrix, Fintype.sum_sum_type, Fintype.sum_prod_type, tagA, tagB, apply_ite, ite_mul,
    Finset.sum_ite_eq', mul_assoc, mul_comm, mul_left_comm, add_assoc]
  by_cases he : i.val = j.val <;> simp [he]

def values {m n : ℕ} (a : Array ℤ) (i : Fin m) (j : Fin n) : ℤ := a[i.val*n+j.val]?.getD 0

end TensorRankFlexible.Finite


namespace TensorRankFlexible.Finite

def pencilC {p : ℕ} (t : Fin p) (k : Fin 2) : ℤ := if k = 0 then 1 else (t.val : ℤ)

namespace ExtraThreeA

def c : Fin 3 → Fin 1 → ℤ := fun _ _ => 0
def bu : Fin 0 → Fin 3 → ℤ := values #[]
def cu : Fin 0 → Fin 1 → ℤ := values #[]
def av : Fin 2 → Fin 3 → ℤ := values #[0, 1, 1, 1, 0, 1]
def cv : Fin 2 → Fin 1 → ℤ := values #[1, 1]

def entries : Array ℤ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 0, 0,
  0, -1, 0, 0, 0, 0, 0, 1, 0,
  0, 0, 0, 0, 0, 1, 0, 0, 0,
  0, 0, 0, -1, 0, 0, 1, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 1, 0, 0, -1, 0, 0,
  0, 1, 0, 0, 1, 0, 0, -1, 0,
  0, 0, -1, 0, 0, -1, 0, 0, 1]

def inverse : Matrix (Column 3 1 0 2) (Row 3 1) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (1 : ℤ) • (1 : Matrix (Row 3 1) (Row 3 1) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 3) (k : Fin 1) (r : Fin 3) (s : Fin 3) (t : Fin 1),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((1 : ℤ) • (1 : Matrix (Row 3 1) (Row 3 1) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 3 (Fin 1) (Fin 0) (Fin 2) (fun _ _ => 0) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 1 (by decide) checked
  simpa only [c, Int.cast_zero] using tile_of_matrix c bu cu av cv hs

end ExtraThreeA

namespace ExtraThreeB

def c : Fin 3 → Fin 2 → ℤ := fun _ _ => 0
def bu : Fin 3 → Fin 3 → ℤ := values #[0, 2, 1, 2, 1, 2, 1, 2, 2]
def cu : Fin 3 → Fin 2 → ℤ := values #[2, 2, 2, 1, 0, 1]
def av : Fin 1 → Fin 3 → ℤ := values #[2, 1, 2]
def cv : Fin 1 → Fin 2 → ℤ := values #[2, 0]

def entries : Array ℤ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, -24, 32, 20, -32, 60, -80, 0, 0, -40, 40, -30, 48, 24, -24, 0, 0,
  0, 0, -20, 24, 16, -24, 50, -72, 0, 0, -32, 36, -25, 40, 20, -20, 0, 0,
  0, 0, -30, 36, 24, -36, 72, -96, 0, 0, -48, 48, -36, 56, 30, -28, 0, 0,
  0, 0, -48, 56, 40, -56, 120, -160, 0, 0, -80, 80, -60, 96, 48, -48, 0, 0,
  0, 0, -20, 24, 16, -24, 50, -64, 0, 0, -32, 32, -25, 40, 20, -20, 0, 0,
  0, 0, -40, 48, 32, -48, 96, -128, 0, 0, -64, 64, -48, 80, 40, -40, 0, 0,
  0, 0, 72, -88, -60, 92, -180, 240, 0, 0, 120, -120, 90, -144, -72, 72, 0, 0,
  0, 0, 40, -48, -32, 48, -100, 136, 0, 0, 64, -64, 50, -80, -40, 40, 0, 0,
  0, 0, 80, -96, -64, 96, -192, 256, 0, 0, 128, -128, 96, -152, -80, 80, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 40, -48, -32, 48, -96, 128, 0, 0, 64, -64, 50, -80, -40, 40, 0, 0,
  0, 0, 50, -60, -40, 60, -120, 160, 0, 0, 80, -80, 60, -96, -48, 48, 0, 0,
  0, 0, 60, -72, -48, 72, -150, 200, 0, 0, 100, -100, 75, -120, -60, 60, 0, 0,
  8, 0, 32, -32, -32, 32, -96, 128, 0, 0, 64, -64, 40, -64, -32, 32, 0, 0,
  0, 8, 24, -24, -20, 20, -60, 80, 0, 0, 40, -40, 30, -48, -24, 24, 0, 0,
  0, 0, 20, -24, -16, 24, -60, 96, 8, 0, 32, -48, 30, -48, -24, 24, 0, 0,
  0, 0, 20, -24, -16, 24, -50, 80, 0, 8, 32, -48, 25, -40, -20, 20, 0, 0,
  0, 0, -20, 24, 16, -24, 72, -96, 0, 0, -48, 48, -36, 48, 20, -24, 8, 0,
  0, 0, -20, 24, 16, -24, 48, -64, 0, 0, -32, 32, -24, 32, 20, -24, 0, 8]

def inverse : Matrix (Column 3 2 3 1) (Row 3 2) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (8 : ℤ) • (1 : Matrix (Row 3 2) (Row 3 2) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 3) (k : Fin 2) (r : Fin 3) (s : Fin 3) (t : Fin 2),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((8 : ℤ) • (1 : Matrix (Row 3 2) (Row 3 2) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 3 (Fin 2) (Fin 3) (Fin 1) (fun _ _ => 0) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 8 (by decide) checked
  simpa only [c, Int.cast_zero] using tile_of_matrix c bu cu av cv hs

end ExtraThreeB

namespace ExtraTwoA

def c : Fin 2 → Fin 1 → ℤ := fun _ _ => 0
def bu : Fin 0 → Fin 2 → ℤ := values #[]
def cu : Fin 0 → Fin 1 → ℤ := values #[]
def av : Fin 2 → Fin 3 → ℤ := values #[1, 1, 0, 0, 1, 1]
def cv : Fin 2 → Fin 1 → ℤ := values #[1, 1]

def entries : Array ℤ := #[
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 1, 0, -1, 0,
  0, 1, 0, 0, 0, 0,
  0, 0, 0, 0, 1, 0,
  0, 0, 0, 0, 0, 1,
  1, 0, -1, 0, 1, 0,
  0, -1, 0, 1, 0, -1]

def inverse : Matrix (Column 2 1 0 2) (Row 2 1) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (1 : ℤ) • (1 : Matrix (Row 2 1) (Row 2 1) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 2) (k : Fin 1) (r : Fin 3) (s : Fin 2) (t : Fin 1),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((1 : ℤ) • (1 : Matrix (Row 2 1) (Row 2 1) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 2 (Fin 1) (Fin 0) (Fin 2) (fun _ _ => 0) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 1 (by decide) checked
  simpa only [c, Int.cast_zero] using tile_of_matrix c bu cu av cv hs

end ExtraTwoA

namespace ExtraTwoB

def c : Fin 2 → Fin 2 → ℤ := fun _ _ => 0
def bu : Fin 2 → Fin 2 → ℤ := values #[1, 1, 2, 1]
def cu : Fin 2 → Fin 2 → ℤ := values #[1, 0, 0, 2]
def av : Fin 1 → Fin 3 → ℤ := values #[1, 2, 2]
def cv : Fin 1 → Fin 2 → ℤ := values #[2, 2]

def entries : Array ℤ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 4, 0, 0, 0, 0, 0, -2, 2, 2, -4,
  0, 0, 0, 0, 4, 0, 0, 0, -8, 4, 8, -8,
  0, 0, 0, 0, 0, 0, 0, 0, -4, 4, 8, -8,
  0, 0, 0, 2, 0, 0, 0, 0, -1, 1, 1, -2,
  0, 0, 0, 0, 0, 1, 0, 0, -2, 1, 2, -2,
  0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, -2,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 2, -1, -2, 2,
  0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 2,
  4, 0, -4, 0, 0, 0, 0, 0, -2, 0, 2, 0,
  0, 4, 0, -8, 0, 0, 0, 0, 0, -2, 0, 4,
  0, 0, 0, 0, -4, 0, 4, 0, 4, 0, -4, 0,
  0, 0, 0, 0, 0, -2, 0, 4, 0, 2, 0, -4]

def inverse : Matrix (Column 2 2 2 1) (Row 2 2) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (4 : ℤ) • (1 : Matrix (Row 2 2) (Row 2 2) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 2) (k : Fin 2) (r : Fin 3) (s : Fin 2) (t : Fin 2),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((4 : ℤ) • (1 : Matrix (Row 2 2) (Row 2 2) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 2 (Fin 2) (Fin 2) (Fin 1) (fun _ _ => 0) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 4 (by decide) checked
  simpa only [c, Int.cast_zero] using tile_of_matrix c bu cu av cv hs

end ExtraTwoB

namespace CommonTwo

def c : Fin 2 → Fin 3 → ℤ := fun _ _ => 0
def bu : Fin 2 → Fin 2 → ℤ := values #[1, 1, 1, 1]
def cu : Fin 2 → Fin 3 → ℤ := values #[1, 0, 0, 1, 0, 1]
def av : Fin 3 → Fin 3 → ℤ := values #[0, 1, 1, 1, 0, 1, 1, 1, 1]
def cv : Fin 3 → Fin 3 → ℤ := values #[0, 1, 0, 1, 1, 1, 1, 1, 0]

def entries : Array ℤ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1,
  0, 0, 0, 0, -1, 0, 1, -1, -1, 0, 0, 0, -1, 1, 0, 1, 0, 0,
  0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1, -1, 1, 0, 0,
  0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1,
  0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0,
  0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
  0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1,
  0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, -1, 0, 0,
  0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1,
  1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0,
  0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0,
  0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1,
  0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, -1, -1, 0, 1,
  0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, -1, 0, -1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0]

def inverse : Matrix (Column 2 3 2 3) (Row 2 3) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (1 : ℤ) • (1 : Matrix (Row 2 3) (Row 2 3) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 2) (k : Fin 3) (r : Fin 3) (s : Fin 2) (t : Fin 3),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((1 : ℤ) • (1 : Matrix (Row 2 3) (Row 2 3) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 2 (Fin 3) (Fin 2) (Fin 3) (fun _ _ => 0) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 1 (by decide) checked
  simpa only [c, Int.cast_zero] using tile_of_matrix c bu cu av cv hs

end CommonTwo

namespace CommonThree

def c : Fin 3 → Fin 3 → ℤ := fun _ _ => 0
def bu : Fin 3 → Fin 3 → ℤ := values #[0, 1, 1, 1, 1, 1, 1, 1, 0]
def cu : Fin 3 → Fin 3 → ℤ := values #[1, 1, 0, 1, 1, 1, 1, 0, 0]
def av : Fin 3 → Fin 3 → ℤ := values #[1, 1, 0, 1, 1, 1, 1, 0, 1]
def cv : Fin 3 → Fin 3 → ℤ := values #[0, 0, 1, 0, 1, 0, 0, 1, 1]

def entries : Array ℤ := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, 0, 0, 0, 1, -1, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, -1, 1, 0, 1, 0, 0, 0, 0, -1, 1, -1, 0, -1, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, -1, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 1, -1, 1, 1, 1, -1, -1, 1, -1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, -1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 1, -1, 0, 0, 0, 0,
  0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, -1, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, -1, 0, 0, 0, 1, -1, 0, -1, 0, 0, 0, 0, 1, -1, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 0, -1, 0, 0, 1, -1, 0, -1, 0, 0, 0, 0, 1, -1, 1, 1, 0, -1, -1, 1, 0, 0, 0, 0,
  0, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, -1, 0, 0, 0, 1, -1, 1, 1, 0, -1, -1, 1, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1, 0, 0, 1, -1, 1, 0, 0, 0,
  0, 0, 0, 0, 1, -1, 0, -1, 1, 0, 0, 0, 0, 0, 1, -1, 1, -1, -1, 0, 0, 1, -1, 1, 0, 0, 0,
  0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0,
  0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0,
  0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 1, -1, 0, 0, 0, 1]

def inverse : Matrix (Column 3 3 3 3) (Row 3 3) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (1 : ℤ) • (1 : Matrix (Row 3 3) (Row 3 3) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 3) (k : Fin 3) (r : Fin 3) (s : Fin 3) (t : Fin 3),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((1 : ℤ) • (1 : Matrix (Row 3 3) (Row 3 3) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 3 (Fin 3) (Fin 3) (Fin 3) (fun _ _ => 0) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 1 (by decide) checked
  simpa only [c, Int.cast_zero] using tile_of_matrix c bu cu av cv hs

end CommonThree

namespace PencilThree

def c : Fin 3 → Fin 2 → ℤ := pencilC
def bu : Fin 0 → Fin 3 → ℤ := values #[]
def cu : Fin 0 → Fin 2 → ℤ := values #[]
def av : Fin 0 → Fin 3 → ℤ := values #[]
def cv : Fin 0 → Fin 2 → ℤ := values #[]

def entries : Array ℤ := #[
  2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0, 0, 0,
  0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -2, 0, 0,
  0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -2, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def inverse : Matrix (Column 3 2 0 0) (Row 3 2) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (2 : ℤ) • (1 : Matrix (Row 3 2) (Row 3 2) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 3) (k : Fin 2) (r : Fin 3) (s : Fin 3) (t : Fin 2),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((2 : ℤ) • (1 : Matrix (Row 3 2) (Row 3 2) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 3 (Fin 2) (Fin 0) (Fin 0) (fun t k => (pencilC t k : ℂ)) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 2 (by decide) checked
  exact tile_of_matrix c bu cu av cv hs

end PencilThree

namespace PencilTwo

def c : Fin 2 → Fin 2 → ℤ := pencilC
def bu : Fin 0 → Fin 2 → ℤ := values #[]
def cu : Fin 0 → Fin 2 → ℤ := values #[]
def av : Fin 1 → Fin 3 → ℤ := values #[0, 0, 1]
def cv : Fin 1 → Fin 2 → ℤ := values #[0, 1]

def entries : Array ℤ := #[
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def inverse : Matrix (Column 2 2 0 1) (Row 2 2) ℤ := unpack entries

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
lemma checked : matrix c bu cu av cv * inverse = (1 : ℤ) • (1 : Matrix (Row 2 2) (Row 2 2) ℤ) := by
  have h : ∀ (i : Fin 3) (j : Fin 2) (k : Fin 2) (r : Fin 3) (s : Fin 2) (t : Fin 2),
      (matrix c bu cu av cv * inverse) (i,j,k) (r,s,t) =
        ((1 : ℤ) • (1 : Matrix (Row 2 2) (Row 2 2) ℤ)) (i,j,k) (r,s,t) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨r,s,t⟩ => h i j k r s t

lemma spans : Tile 2 (Fin 2) (Fin 0) (Fin 1) (fun t k => (pencilC t k : ℂ)) := by
  have hs := of_scaled_inverse (matrix c bu cu av cv) inverse 1 (by decide) checked
  exact tile_of_matrix c bu cu av cv hs

end PencilTwo

end TensorRankFlexible.Finite

namespace TensorRankFlexible

lemma cell_three_a (l : ℕ) {W U V : Type} [Fintype W] [Fintype U] [Fintype V]
    (hw : Fintype.card W = 3*l+3) (hu : Fintype.card U = 3*l) (hv : Fintype.card V = 3*l+2) :
    Cell (Fin 3) W U V := by
  have raw := tile_cell (tile_add (tile_add Finite.PencilThree.spans Finite.ExtraThreeA.spans)
    (tile_repeat (Fin l) Finite.CommonThree.spans))
  refine transport_cell ?_ ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega

lemma cell_two_a (l : ℕ) {W U V : Type} [Fintype W] [Fintype U] [Fintype V]
    (hw : Fintype.card W = 3*l+3) (hu : Fintype.card U = 2*l) (hv : Fintype.card V = 3*l+3) :
    Cell (Fin 2) W U V := by
  have raw := tile_cell (tile_add (tile_add Finite.PencilTwo.spans Finite.ExtraTwoA.spans)
    (tile_repeat (Fin l) Finite.CommonTwo.spans))
  refine transport_cell ?_ ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega

lemma cell_three_b (l : ℕ) {W U V : Type} [Fintype W] [Fintype U] [Fintype V]
    (hw : Fintype.card W = 3*l+4) (hu : Fintype.card U = 3*l+3) (hv : Fintype.card V = 3*l+1) :
    Cell (Fin 3) W U V := by
  have raw := tile_cell (tile_add (tile_add Finite.PencilThree.spans Finite.ExtraThreeB.spans)
    (tile_repeat (Fin l) Finite.CommonThree.spans))
  refine transport_cell ?_ ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega

lemma cell_two_b (l : ℕ) {W U V : Type} [Fintype W] [Fintype U] [Fintype V]
    (hw : Fintype.card W = 3*l+4) (hu : Fintype.card U = 2*l+2) (hv : Fintype.card V = 3*l+2) :
    Cell (Fin 2) W U V := by
  have raw := tile_cell (tile_add (tile_add Finite.PencilTwo.spans Finite.ExtraTwoB.spans)
    (tile_repeat (Fin l) Finite.CommonTwo.spans))
  refine transport_cell ?_ ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega

def width {a b : ℕ} : Fin a ⊕ Fin b → ℕ := Sum.elim (fun _ => 3) (fun _ => 2)
abbrev Fibers (a b : ℕ) (h : Fin a ⊕ Fin b) := Fin (width h)

lemma card_fibers (a b : ℕ) : Fintype.card (Sigma (Fibers a b)) = 3*a+2*b := by
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  change (∑ _ : Fin a, Fintype.card (Fin 3)) + (∑ _ : Fin b, Fintype.card (Fin 2)) = _
  simp [Nat.mul_comm]

lemma card_off_row {G : Type} [Fintype G] [DecidableEq G] (g : G) :
    Fintype.card {l : G // l ≠ g} + 1 = Fintype.card G := by
  simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe g)

lemma card_off_col {H : Type} {J : H → Type} [Fintype H] [∀ h, Fintype (J h)] [DecidableEq H] (h : H) :
    Fintype.card (J h) + Fintype.card {z : Sigma J // z.1 ≠ h} = Fintype.card (Sigma J) := by
  simpa only [Fintype.card_sum] using (Fintype.card_congr (@splitColumn _ J _ h)).symm

lemma config_a (l : ℕ) :
    Config ((Fin (l+1)) × Fin 3) (Sigma (Fibers (l+1) 1)) (Fin (3*l+3))
      (Slot (Fin (l+1)) (Fibers (l+1) 1)) := by
  apply grid_config
  intro g h
  apply extend_cell
  have hr := card_off_row g
  simp only [Fintype.card_fin] at hr
  have hc := @card_off_col _ (Fibers (l+1) 1) _ _ _ h
  rw [card_fibers] at hc
  cases h with
  | inl a =>
    change 3 + _ = _ at hc
    apply cell_three_a l
    · simp
    · simp only [Fintype.card_prod, Fintype.card_fin, width, Sum.elim_inl]
      omega
    · omega
  | inr b =>
    change 2 + _ = _ at hc
    apply cell_two_a l
    · simp
    · simp only [Fintype.card_prod, Fintype.card_fin, width, Sum.elim_inr]
      omega
    · omega

lemma config_b (l : ℕ) :
    Config ((Fin (l+2)) × Fin 3) (Sigma (Fibers l 2)) (Fin (3*l+4))
      (Slot (Fin (l+2)) (Fibers l 2)) := by
  apply grid_config
  intro g h
  apply extend_cell
  have hr := card_off_row g
  simp only [Fintype.card_fin] at hr
  have hc := @card_off_col _ (Fibers l 2) _ _ _ h
  rw [card_fibers] at hc
  cases h with
  | inl a =>
    change 3 + _ = _ at hc
    apply cell_three_b l
    · simp
    · simp only [Fintype.card_prod, Fintype.card_fin, width, Sum.elim_inl]
      omega
    · omega
  | inr b =>
    change 2 + _ = _ at hc
    apply cell_two_b l
    · simp
    · simp only [Fintype.card_prod, Fintype.card_fin, width, Sum.elim_inr]
      omega
    · omega

end TensorRankFlexible


namespace TensorRankFlexible

lemma cell_three_minus (l : ℕ) {W U V : Type} [Fintype W] [Fintype U] [Fintype V]
    (hw : Fintype.card W = 3*l+2) (hu : Fintype.card U = 3*l) (hv : Fintype.card V = 3*l) :
    Cell (Fin 3) W U V := by
  have raw := tile_cell (tile_add Finite.PencilThree.spans (tile_repeat (Fin l) Finite.CommonThree.spans))
  refine transport_cell ?_ ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega

lemma config_minus (l : ℕ) :
    Config ((Fin (l+1)) × Fin 3) (Sigma (Fibers (l+1) 0)) (Fin (3*l+2))
      (Slot (Fin (l+1)) (Fibers (l+1) 0)) := by
  apply grid_config
  intro g h
  apply extend_cell
  have hr := card_off_row g
  simp only [Fintype.card_fin] at hr
  have hc := @card_off_col _ (Fibers (l+1) 0) _ _ _ h
  rw [card_fibers] at hc
  cases h with
  | inl a =>
    change 3 + _ = _ at hc
    apply cell_three_minus l
    · simp
    · simp only [Fintype.card_prod, Fintype.card_fin, width, Sum.elim_inl]
      omega
    · omega
  | inr b => exact Fin.elim0 b

lemma swap_tail {A B C R : Type} [Fintype R] (h : Config A B C R) : Config A C B R := by
  obtain ⟨a,b,c,hs⟩ := h
  refine ⟨a,c,b,?_⟩
  intro T
  obtain ⟨u,v,w,hT⟩ := hs fun i j k => T i k j
  refine ⟨u,w,v,?_⟩
  intro i j k
  rw [hT i k j]
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma cycle_axes {A B C R : Type} [Fintype R] (h : Config A B C R) : Config B C A R := by
  obtain ⟨a,b,c,hs⟩ := h
  refine ⟨b,c,a,?_⟩
  intro T
  obtain ⟨u,v,w,hT⟩ := hs fun i j k => T j k i
  refine ⟨v,w,u,?_⟩
  intro i j k
  rw [hT k i j]
  apply Finset.sum_congr rfl
  intro t _
  ring

open TensorRankCore in
lemma witness_a (l : ℕ) :
    let d := 3*l+3
    ∃ x : Param d (d+2) (d*(d+2)/3) → ℂ, Spans x := by
  obtain ⟨a,b,c,hs⟩ := swap_tail (config_a l)
  dsimp only
  refine of_reindexed_config ?_ ?_ ?_ ?_ a b c hs <;> apply Fintype.equivOfCardEq
  · simp
    omega
  · simp
  · rw [Fintype.card_fin, card_fibers]
    omega
  · simp only [Slot, Fintype.card_prod, Fintype.card_fin, card_fibers]
    rw [show (3*l+3)*(3*l+3+2) = ((l+1)*(3*(l+1)+2*1))*3 by ring]
    exact Nat.mul_div_cancel _ (by decide)

open TensorRankCore in
lemma witness_b (l : ℕ) :
    let d := 3*l+4
    ∃ x : Param d (d+2) (d*(d+2)/3) → ℂ, Spans x := by
  obtain ⟨a,b,c,hs⟩ := cycle_axes (config_b l)
  dsimp only
  refine of_reindexed_config ?_ ?_ ?_ ?_ a b c hs <;> apply Fintype.equivOfCardEq
  · rw [Fintype.card_fin, card_fibers]
  · simp
  · simp
    omega
  · simp only [Slot, Fintype.card_prod, Fintype.card_fin, card_fibers]
    rw [show (3*l+4)*(3*l+4+2) = ((l+2)*(3*l+2*2))*3 by ring]
    exact Nat.mul_div_cancel _ (by decide)

open TensorRankCore in
lemma witness_minus (l : ℕ) :
    let d := 3*l+3
    ∃ x : Param d (d-1) (d*d/3) → ℂ, Spans x := by
  obtain ⟨a,b,c,hs⟩ := config_minus l
  dsimp only
  refine of_reindexed_config ?_ ?_ ?_ ?_ a b c hs <;> apply Fintype.equivOfCardEq
  · simp
    omega
  · rw [Fintype.card_fin, card_fibers]
    omega
  · simp
  · simp only [Slot, Fintype.card_prod, Fintype.card_fin, card_fibers]
    rw [show (3*l+3)*(3*l+3) = ((l+1)*(3*(l+1)+2*0))*3 by ring]
    exact Nat.mul_div_cancel _ (by decide)

end TensorRankFlexible

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1.H2 := by
  apply TensorRankCore.core_of_quasicubic_witnesses
  · intro d hd hr
    by_cases he : d % 3 = 0
    · obtain ⟨l,rfl⟩ : ∃ l, d = 3*l+3 := ⟨d/3-1, by omega⟩
      exact TensorRankFlexible.witness_a l
    · obtain ⟨l,rfl⟩ : ∃ l, d = 3*l+4 := ⟨d/3-1, by omega⟩
      exact TensorRankFlexible.witness_b l
  · intro d hd hr
    obtain ⟨l,rfl⟩ : ∃ l, d = 3*l+3 := ⟨d/3-1, by omega⟩
    exact TensorRankFlexible.witness_minus l
