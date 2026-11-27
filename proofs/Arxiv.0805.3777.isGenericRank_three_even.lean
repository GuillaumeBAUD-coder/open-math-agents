import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! The generic complex rank of a three-by-even-by-even tensor.

Split each even axis into two-dimensional blocks and put three simple
tensors in each diagonal block. The twelve tangent equations for a diagonal
or off-diagonal block have explicit integer certificates. A product of
determinant polynomials gives a single choice of factors for which every
block spans. The generic upper bound follows from the differential of the
sum map and the constructibility of its image.

Normalizing the first two factors in a rank-one summand gives the dimension
lower bound. The dense open sets for the two bounds intersect at rank 3p.
The generic rank is due to V. Strassen, Rank and optimal computation of
generic tensors (1983); see also [Friedland, equation (5.3)](https://arxiv.org/abs/0805.3777).
-/

namespace ThreeEven

/-- The tangent spaces at three points per two-dimensional block span the
entire space of tensors with three slices. -/
def Spans (p : ℕ) : Prop :=
  ∃ a : Fin (3*p) → Fin 3 → ℂ, ∃ b c : Fin (3*p) → Fin (2*p) → ℂ,
    ∀ T : Fin 3 → Fin (2*p) → Fin (2*p) → ℂ, ∃ u : Fin (3*p) → Fin 3 → ℂ,
      ∃ v w : Fin (3*p) → Fin (2*p) → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
          a t i * (b t j * w t k))

end ThreeEven

namespace ThreeEven

/-- Restriction to one two-by-two pair of coordinate blocks. The first term
is present when both block labels coincide. -/
def Cell (diagonal : Prop) [Decidable diagonal] (a₁ a₂ : Fin 3 → Fin 3 → ℂ)
    (b c : Fin 3 → Fin 2 → ℂ) : Prop :=
  ∀ T : Fin 3 → Fin 2 → Fin 2 → ℂ, ∃ u : Fin 3 → Fin 3 → ℂ, ∃ v w : Fin 3 → Fin 2 → ℂ, ∀ i j k,
    T i j k = ∑ t, (u t i * (if diagonal then b t j * c t k else 0) +
      a₂ t i * (v t j * c t k) + a₁ t i * (b t j * w t k))

end ThreeEven

namespace ThreeEven.Grid
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
end ThreeEven.Grid

namespace ThreeEven.Grid

open MvPolynomial

abbrev Param (G : Type) := (G × Fin 3) × (Fin 3 ⊕ (Fin 2 ⊕ Fin 2))
abbrev Row := Fin 3 × Fin 2 × Fin 2
abbrev Col := Fin 3 × (Fin 3 ⊕ (Fin 2 ⊕ Fin 2))

def a {G K : Type} (z : Param G → K) (g : G) (t i : Fin 3) := z ((g,t),Sum.inl i)
def b {G K : Type} (z : Param G → K) (g : G) (t : Fin 3) (j : Fin 2) := z ((g,t),Sum.inr (Sum.inl j))
def c {G K : Type} (z : Param G → K) (g : G) (t : Fin 3) (k : Fin 2) := z ((g,t),Sum.inr (Sum.inr k))

def mat {G K : Type} [DecidableEq G] [CommSemiring K] (z : Param G → K) (g h : G) : Matrix Row Col K
  | (i,j,k),(t,Sum.inl u) =>
      if u=i then (if g=h then b z g t j*c z h t k else 0) else 0
  | (i,j,k),(t,Sum.inr (Sum.inl u)) => if u=j then a z h t i*c z h t k else 0
  | (i,j,k),(t,Sum.inr (Sum.inr u)) => if u=k then a z g t i*b z g t j else 0

lemma action {G : Type} [DecidableEq G] (z : Param G → ℂ) (g h : G) (y : Col → ℂ)
    (i : Fin 3) (j k : Fin 2) : (mat z g h).mulVec y (i,j,k) =
      ∑ t, (y (t,Sum.inl i)*(if g=h then b z g t j*c z h t k else 0) +
        a z h t i*(y (t,Sum.inr (Sum.inl j))*c z h t k) + a z g t i*(b z g t j*y (t,Sum.inr (Sum.inr k)))) := by
  change (∑ q : Col, mat z g h (i,j,k) q*y q)=_
  by_cases he : g=h <;>
    simp [Fintype.sum_prod_type,Fintype.sum_sum_type,mat,he,Finset.sum_ite_eq',
      mul_comm,mul_left_comm,add_assoc]

lemma cell_iff {G : Type} [DecidableEq G] (z : Param G → ℂ) (g h : G) :
    Cell (g=h) (a z g) (a z h) (b z g) (c z h) ↔ Function.Surjective (mat z g h).mulVec := by
  constructor
  · intro hs T
    obtain ⟨u,v,w,ht⟩ := hs fun i j k => T (i,j,k)
    let y : Col → ℂ := fun q => q.2.elim (u q.1) (Sum.elim (v q.1) (w q.1))
    refine ⟨y,?_⟩
    funext r
    obtain ⟨i,j,k⟩ := r
    exact (action z g h y i j k).trans (ht i j k).symm
  · intro hs T
    obtain ⟨y,hy⟩ := hs fun r => T r.1 r.2.1 r.2.2
    refine ⟨fun t i => y (t,Sum.inl i),fun t j => y (t,Sum.inr (Sum.inl j)),
      fun t k => y (t,Sum.inr (Sum.inr k)),?_⟩
    intro i j k
    exact (congrFun hy (i,j,k)).symm.trans (action z g h y i j k)

lemma eval_matrix {G : Type} [DecidableEq G] (z : Param G → ℂ) (g h : G) :
    (mat (MvPolynomial.X : Param G → MvPolynomial (Param G) ℂ) g h).map (eval z)=mat z g h := by
  ext ⟨i,j,k⟩ ⟨t,u⟩
  rcases u with u | u | u
  · by_cases hu : u=i <;> by_cases he : g=h <;> simp [Matrix.map_apply,mat,b,c,hu,he]
  · by_cases hu : u=j <;> simp [Matrix.map_apply,mat,a,c,hu]
  · by_cases hu : u=k <;> simp [Matrix.map_apply,mat,a,b,hu]

lemma common {G : Type} [Fintype G] [DecidableEq G]
    (diag : ∃ a : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell True a a b c)
    (off : ∃ a₁ a₂ : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell False a₁ a₂ b c) :
    ∃ z : Param G → ℂ, ∀ g h : G, Cell (g=h) (a z g) (a z h) (b z g) (c z h) := by
  classical
  have separate (r : G×G) : ∃ z : Param G → ℂ, Function.Surjective
      ((mat (MvPolynomial.X : Param G → MvPolynomial (Param G) ℂ) r.1 r.2).map (eval z)).mulVec := by
    obtain ⟨g,h⟩ := r
    by_cases he : g=h
    · subst h
      obtain ⟨aa,bb,cc,hh⟩ := diag
      let z : Param G → ℂ := fun t => t.2.elim (aa t.1.2) (Sum.elim (bb t.1.2) (cc t.1.2))
      refine ⟨z,?_⟩
      rw [eval_matrix,← cell_iff]
      simpa [Cell,z,a,b,c] using hh
    · obtain ⟨a₁,a₂,bb,cc,hh⟩ := off
      let z : Param G → ℂ := fun t => t.2.elim (fun i => if t.1.1=g then a₁ t.1.2 i else a₂ t.1.2 i)
        (Sum.elim (bb t.1.2) (cc t.1.2))
      refine ⟨z,?_⟩
      rw [eval_matrix,← cell_iff]
      simpa [Cell,z,a,b,c,he,Ne.symm he] using hh
  obtain ⟨z,_,hz⟩ := simultaneous_surjectivity (fun r : G×G => mat (MvPolynomial.X : Param G → MvPolynomial (Param G) ℂ) r.1 r.2) separate 1 one_ne_zero
  refine ⟨z,fun g h => (cell_iff z g h).mpr ?_⟩
  simpa only [eval_matrix] using hz (g,h)

def pad {G : Type} [DecidableEq G] (g : G) (f : Fin 2 → ℂ) (i : G×Fin 2) := if g=i.1 then f i.2 else 0

lemma assemble {G : Type} [Fintype G] [DecidableEq G] (z : Param G → ℂ)
    (hc : ∀g h, Cell (g=h) (a z g) (a z h) (b z g) (c z h))
    (T : Fin 3 → (G×Fin 2) → (G×Fin 2) → ℂ) :
    ∃ u : (G×Fin 3) → Fin 3 → ℂ, ∃ v w : (G×Fin 3) → (G×Fin 2) → ℂ, ∀ i j k,
    T i j k = ∑ t : G×Fin 3, (u t i * (pad t.1 (b z t.1 t.2) j * pad t.1 (c z t.1 t.2) k) +
      a z t.1 t.2 i * (v t j * pad t.1 (c z t.1 t.2) k) +
      a z t.1 t.2 i * (pad t.1 (b z t.1 t.2) j * w t k)) := by
  classical
  choose U V W hh using fun g h => hc g h (fun i j k => T i (g,j) (h,k))
  refine ⟨fun t => U t.1 t.1 t.2,fun t j => V j.1 t.1 t.2 j.2,fun t k => W t.1 k.1 t.2 k.2,?_⟩
  rintro i ⟨g,j⟩ ⟨h,k⟩
  rw [hh g h i j k]
  by_cases he : g=h
  · subst h
    simp [Fintype.sum_prod_type,pad,Finset.sum_add_distrib,ite_mul,mul_ite,Finset.sum_ite_irrel]
  · simp [Fintype.sum_prod_type,pad,he,Ne.symm he,Finset.sum_add_distrib,ite_mul,mul_ite,Finset.sum_ite_irrel]

lemma spans_of_cells (p : ℕ)
    (diag : ∃ a : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell True a a b c)
    (off : ∃ a₁ a₂ : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell False a₁ a₂ b c) :
    Spans p := by
  classical
  obtain ⟨z,hz⟩ := common (G:=Fin p) diag off
  let er : Fin (3*p) ≃ Fin p × Fin 3 := Fintype.equivOfCardEq (by simp [Nat.mul_comm])
  let ei : Fin (2*p) ≃ Fin p × Fin 2 := Fintype.equivOfCardEq (by simp [Nat.mul_comm])
  let a₀ (t : Fin (3*p)) := a z (er t).1 (er t).2
  let b₀ (t : Fin (3*p)) (j : Fin (2*p)) := pad (er t).1 (b z (er t).1 (er t).2) (ei j)
  let c₀ (t : Fin (3*p)) (k : Fin (2*p)) := pad (er t).1 (c z (er t).1 (er t).2) (ei k)
  refine ⟨a₀,b₀,c₀,?_⟩
  intro T
  obtain ⟨u,v,w,hu⟩ := assemble z hz (fun i j k => T i (ei.symm j) (ei.symm k))
  refine ⟨fun t => u (er t),fun t j => v (er t) (ei j),fun t k => w (er t) (ei k),?_⟩
  intro i j k
  have h := hu i (ei j) (ei k)
  simp only [Equiv.symm_apply_apply] at h
  exact h.trans ((er.sum_comp fun t => u t i * (pad t.1 (b z t.1 t.2) (ei j) * pad t.1 (c z t.1 t.2) (ei k)) +
    a z t.1 t.2 i * (v t (ei j) * pad t.1 (c z t.1 t.2) (ei k)) +
    a z t.1 t.2 i * (pad t.1 (b z t.1 t.2) (ei j) * w t (ei k))).symm)

end ThreeEven.Grid

namespace ThreeEven

private def delta (t i : Fin 3) : ℂ := if t=i then 1 else 0

private def direction (t : Fin 3) (j : Fin 2) : ℤ :=
  (![![1,0],![0,1],![1,1]] : Fin 3 → Fin 2 → ℤ) t j

private lemma vec_two {α : Type} (a : α) (f : Fin 2 → α) :
    Matrix.vecCons a f (2 : Fin 3) = f 1 := rfl

/-- For each slice the two diagonal entries are free. At the last point the
two variations in the second factor fix both off-diagonal entries. -/
lemma diagonal_cell :
    ∃ a : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell True a a b c := by
  refine ⟨delta,fun t j => (direction t j : ℂ),fun t k => (direction t k : ℂ),?_⟩
  intro T
  let u : Fin 3 → Fin 3 → ℂ :=
    ![![T 0 0 0,T 1 0 0,T 2 0 0-T 2 0 1],![T 0 1 1,T 1 1 1,T 2 1 1-T 2 1 0],![0,0,0]]
  let v : Fin 3 → Fin 2 → ℂ := ![![0,T 0 1 0],![T 1 0 1,0],![T 2 0 1,T 2 1 0]]
  let w : Fin 3 → Fin 2 → ℂ := ![![0,T 0 0 1],![T 1 1 0,0],![0,0]]
  refine ⟨u,v,w,?_⟩
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp (disch := decide) [Fin.sum_univ_three,u,v,w,delta,direction,vec_two]

private abbrev R := Fin 3 × Fin 2 × Fin 2
private abbrev Q := Fin 2 × Fin 3 × Fin 2

private def A (t i : Fin 3) : ℤ := (![![1,0,1],![1,1,0],![1,1,1]] : Fin 3 → Fin 3 → ℤ) t i
private def B (t : Fin 3) (j : Fin 2) : ℤ := (![![0,1],![1,0],![1,1]] : Fin 3 → Fin 2 → ℤ) t j

private def M : Matrix R Q ℤ := fun ⟨i,j,k⟩ ⟨q,t,h⟩ =>
  if q=0 then (if h=j then (if t=i then direction t k else 0) else 0)
  else (if h=k then A t i * B t j else 0)

private def entries : Array ℤ := #[
  1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 1,
  0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, -1, 1, 1, -1, 0, 0,
  0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0,
  0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1, -1,
  0, 0, 0, 1, 0, 0, -1, 0, 1, -1, 0, 0,
  0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, -1, 0, 1, -1, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, -1, 1, 0, 0]

private def N : Matrix Q R ℤ := fun ⟨q,t,h⟩ ⟨i,j,k⟩ =>
  entries[((q.val*3+t.val)*2+h.val)*12 + (i.val*2+j.val)*2+k.val]?.getD 0

private lemma exact_inverse : M * N = 1 := by
  have h : ∀ (i : Fin 3) (j k : Fin 2) (a : Fin 3) (b c : Fin 2),
      (M * N) (i,j,k) (a,b,c) = (1 : Matrix R R ℤ) (i,j,k) (a,b,c) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨a,b,c⟩ => h i j k a b c


/-- The two independent three-point families give complementary directions
on the twelve coordinates of a pair of distinct blocks. -/
lemma off_diagonal_cell :
    ∃ a₁ a₂ : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell False a₁ a₂ b c := by
  classical
  have hs : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
    apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    refine ⟨N.map (Int.castRingHom ℂ), ?_⟩
    rw [← Matrix.map_mul,exact_inverse,← RingHom.mapMatrix_apply,map_one]
  refine ⟨fun t i => (A t i : ℂ),delta,fun t j => (B t j : ℂ),fun t k => (direction t k : ℂ),?_⟩
  intro T
  obtain ⟨y,hy⟩ := hs fun z => T z.1 z.2.1 z.2.2
  refine ⟨0,fun t j => y (0,t,j),fun t k => y (1,t,k),?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : Q, ((M (i,j,k) z : ℤ) : ℂ) * y z) = _
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  simp [Fintype.sum_prod_type,M,delta,apply_ite,ite_mul,Finset.sum_ite_eq',Finset.sum_add_distrib,
    mul_comm,mul_left_comm]

end ThreeEven

namespace ThreeEven

open Arxiv.«0805.3777» Set Filter
open scoped Topology

namespace Dimension

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
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

lemma vanishing_on_polynomial_image {I J : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (F : J → MvPolynomial I ℂ) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : I → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P = 0 := by
  classical
  have hn : ¬ AlgebraicIndependent ℂ F := by
    intro h
    have hc := h.cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain] at hc
    have : Fintype.card J ≤ Fintype.card I := by simpa [Cardinal.mk_fintype] using hc
    omega
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  obtain ⟨P, ha, hP⟩ := hn
  refine ⟨P, hP, ?_⟩
  intro x
  rw [← eval_substitution F x P, ha, map_zero]

/-- Agreement with a lower-dimensional chart on a product of infinite subsets
extends to a polynomial identity on the entire parameter space. -/
lemma generic_chart_relation {I J K : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (chart : J → MvPolynomial I ℂ)
    (full : J → MvPolynomial K ℂ)
    (hnormal : ∀ x : K → ℂ, (∀ i, x i ≠ 0) →
      ∃ y : I → ℂ, ∀ j, MvPolynomial.eval x (full j) = MvPolynomial.eval y (chart j)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : K → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (full j)) P = 0 := by
  classical
  obtain ⟨P, hP, hvanish⟩ := vanishing_on_polynomial_image hd chart
  have hpoly : MvPolynomial.aeval full P = 0 := by
    apply MvPolynomial.funext_set (fun _ : K => ({0}ᶜ : Set ℂ))
      (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro x hx
    have hx0 (i : K) : x i ≠ 0 := hx i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := hnormal x hx0
    rw [eval_substitution full x P, funext hy, map_zero]
    exact hvanish y
  refine ⟨P, hP, fun x => ?_⟩
  rw [← eval_substitution full x P, hpoly, map_zero]

def index_cons_equiv (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds where
  toFun
    | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
    | ⟨[], h⟩ => nomatch h
  invFun q := ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => cases h
    | cons i is => rfl
  right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl

def vector_index_equiv (n : ℕ) : HolorIndex [n] ≃ Fin n where
  toFun i := ((index_cons_equiv n []) i).1
  invFun i := ⟨[i.val], .cons i.isLt .nil⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases h with
    | cons _ h => cases h; rfl
  right_inv := by intro i; rfl

def indexEquiv (n : ℕ) : HolorIndex [3, n, n] ≃ Fin 3 × Fin n × Fin n :=
  (index_cons_equiv 3 [n, n]).trans (Equiv.prodCongr (Equiv.refl _)
    ((index_cons_equiv n [n]).trans (Equiv.prodCongr (Equiv.refl _) (vector_index_equiv n))))

lemma zero_is_simple (ds : List ℕ) : Holor.CPRankMax1 (0 : Holor ℂ ds) := by
  induction ds with
  | nil => exact .nil _
  | cons n ds ih =>
    have h := Holor.CPRankMax1.cons (0 : Holor ℂ [n]) (0 : Holor ℂ ds) ih
    have he : Holor.mul (0 : Holor ℂ [n]) (0 : Holor ℂ ds) = (0 : Holor ℂ (n :: ds)) := by
      funext i
      change (0 : ℂ) * 0 = 0
      simp
    rwa [he] at h

lemma decomposition_of_rank_bound {ds : List ℕ} (T : Holor ℂ ds) (r : ℕ) (hr : T.cprank ≤ r) :
    Holor.CPRankMax r T := by
  classical
  have hmin : Holor.CPRankMax T.cprank T :=
    Nat.find_spec (p := fun k => Holor.CPRankMax k T) ⟨ds.prod, Holor.cprankMax_upper_bound T⟩
  induction r, hr using Nat.le_induction with
  | base => exact hmin
  | succ k _ ih => simpa using Holor.CPRankMax.succ k 0 T (zero_is_simple ds) ih

lemma finite_sum_of_simple {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : Holor.CPRankMax r T) :
    ∃ u : Fin r → Holor ℂ ds, (∀ i, Holor.CPRankMax1 (u i)) ∧ ∑ i, u i = T := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ k x y hx hy ih =>
    obtain ⟨u, hu, hs⟩ := ih
    refine ⟨Fin.cons x u, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hu j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hs]

/-- Absorb the trailing scalar of a simple tensor into the last vector. -/
lemma simple_coordinates {n : ℕ} {T : Holor ℂ [3,n,n]} (h : Holor.CPRankMax1 T) :
    ∃ (a : Fin 3 → ℂ) (b c : Fin n → ℂ),
      ∀ i j k, T ((indexEquiv n).symm (i,j,k)) = a i * b j * c k := by
  cases h with
  | cons a yz hyz =>
    cases hyz with
    | cons b zs hzs =>
      cases hzs with
      | cons c z hz =>
        refine ⟨fun i => a ((vector_index_equiv 3).symm i),
          fun j => b ((vector_index_equiv n).symm j),
          fun k => c ((vector_index_equiv n).symm k) * z ⟨[], .nil⟩, ?_⟩
        intro i j k
        change a _ * (b _ * (c _ * z _)) = a _ * b _ * (c _ * z _)
        rw [mul_assoc]
        rfl

abbrev Raw (m r : ℕ) := Fin r × (Fin 3 ⊕ (Fin (m+1) ⊕ Fin (m+1)))
abbrev Chart (m r : ℕ) := Fin r × (Fin 2 ⊕ (Fin m ⊕ Fin (m+1)))

noncomputable def rawCoordinate (m r : ℕ) (q : HolorIndex [3,m+1,m+1]) :
    MvPolynomial (Raw m r) ℂ :=
  let v := indexEquiv (m+1) q
  ∑ t : Fin r, MvPolynomial.X (t, Sum.inl v.1) * MvPolynomial.X (t, Sum.inr (Sum.inl v.2.1)) *
    MvPolynomial.X (t, Sum.inr (Sum.inr v.2.2))

noncomputable def chartCoordinate (m r : ℕ) (q : HolorIndex [3,m+1,m+1]) :
    MvPolynomial (Chart m r) ℂ :=
  let v := indexEquiv (m+1) q
  ∑ t : Fin r, Fin.cases 1 (fun i => MvPolynomial.X (t, Sum.inl i)) v.1 *
    Fin.cases 1 (fun j => MvPolynomial.X (t, Sum.inr (Sum.inl j))) v.2.1 *
    MvPolynomial.X (t, Sum.inr (Sum.inr v.2.2))

/-- Normalize the first coordinates of the first two vectors of each term. -/
lemma normalize (m r : ℕ) (x : Raw m r → ℂ) (hx : ∀ i, x i ≠ 0) :
    ∃ y : Chart m r → ℂ, ∀ q,
      MvPolynomial.eval x (rawCoordinate m r q) = MvPolynomial.eval y (chartCoordinate m r q) := by
  classical
  let y : Chart m r → ℂ := fun (t,s) => match s with
    | .inl i => x (t,.inl i.succ) / x (t,.inl 0)
    | .inr (.inl j) => x (t,.inr (.inl j.succ)) / x (t,.inr (.inl 0))
    | .inr (.inr k) => x (t,.inr (.inr k)) * x (t,.inl 0) * x (t,.inr (.inl 0))
  refine ⟨y,?_⟩
  intro q
  simp only [rawCoordinate,chartCoordinate,map_sum,map_mul,MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro t _
  have ha (i : Fin 3) :
      MvPolynomial.eval y (Fin.cases 1 (fun i : Fin 2 => MvPolynomial.X (t,Sum.inl i)) i) =
        x (t,.inl i) / x (t,.inl 0) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hx]
    · simp [y]
  have hb (j : Fin (m+1)) :
      MvPolynomial.eval y (Fin.cases 1 (fun j : Fin m => MvPolynomial.X (t,Sum.inr (Sum.inl j))) j) =
        x (t,.inr (.inl j)) / x (t,.inr (.inl 0)) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [hx]
    · simp [y]
  rw [ha,hb]
  dsimp only [y]
  field_simp [hx]

lemma representation (m r : ℕ) (T : Holor ℂ [3,m+1,m+1]) (hr : T.cprank ≤ r) :
    ∃ x : Raw m r → ℂ, ∀ q, MvPolynomial.eval x (rawCoordinate m r q) = T q := by
  classical
  obtain ⟨u,hu,hT⟩ := finite_sum_of_simple (decomposition_of_rank_bound T r hr)
  choose a b c habc using fun t => simple_coordinates (hu t)
  let x : Raw m r → ℂ := fun (t,s) => match s with
    | .inl i => a t i
    | .inr (.inl j) => b t j
    | .inr (.inr k) => c t k
  refine ⟨x,?_⟩
  intro q
  let v := indexEquiv (m+1) q
  have term (t : Fin r) : u t q = a t v.1 * b t v.2.1 * c t v.2.2 := by
    have ht := habc t v.1 v.2.1 v.2.2
    change u t ((indexEquiv (m+1)).symm v) = _ at ht
    simpa only [v,Equiv.symm_apply_apply] using ht
  have hcoord : (∑ t : Fin r, u t q) = T q := by
    have eqAt := Finset.sum_apply (M := fun _ : HolorIndex [3,m+1,m+1] => ℂ) q
      (Finset.univ : Finset (Fin r)) (fun t => fun v => u t v)
    exact eqAt.symm.trans (congrFun hT q)
  calc
    _ = ∑ t : Fin r, a t v.1 * b t v.2.1 * c t v.2.2 := by simp [rawCoordinate,v,x]
    _ = ∑ t : Fin r, u t q := Finset.sum_congr rfl fun t _ => (term t).symm
    _ = T q := hcoord

end Dimension

open Dimension in
/-- The closure of the smaller-rank tensors has empty interior. The scaled
parameter chart for one summand has two fewer coordinates than the three
vectors that determine it. -/
theorem lower (p : ℕ) (hp : 2 ≤ p) :
    interior (closure {T : Holor ℂ [3,2*p,2*p] | T.cprank ≤ 3*p-1}) = ∅ := by
  classical
  let m := 2*p-1
  let r := 3*p-1
  have hm : m+1=2*p := by dsimp [m]; omega
  have hr : r+1=3*p := by dsimp [r]; omega
  rw [← hm]
  let _ : Fintype (HolorIndex [3,m+1,m+1]) :=
    Fintype.ofEquiv _ (indexEquiv (m+1)).symm
  have hj : Fintype.card (HolorIndex [3,m+1,m+1]) = 3*((2*p)*(2*p)) := by
    rw [Fintype.card_congr (indexEquiv (m+1))]
    simp [hm]
  have hi : Fintype.card (Chart m r) = r*(4*p+1) := by
    have h : 4*p+1 = 2 + (m+(m+1)) := by omega
    rw [h]
    simp [Chart]
  have hd : Fintype.card (Chart m r) < Fintype.card (HolorIndex [3,m+1,m+1]) := by
    rw [hi,hj]
    have he := congrArg (fun k => k*(4*p+1)) hr
    nlinarith
  obtain ⟨P,hP,hzero⟩ := generic_chart_relation hd (chartCoordinate m r)
    (rawCoordinate m r) (normalize m r)
  let Z := {T : Holor ℂ [3,m+1,m+1] | MvPolynomial.eval T P = 0}
  have hclosed : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
  have hsub : {T : Holor ℂ [3,m+1,m+1] | T.cprank ≤ r} ⊆ Z := by
    intro T hT
    obtain ⟨x,hx⟩ := representation m r T hT
    have he : (fun j => MvPolynomial.eval x (rawCoordinate m r j)) = T := funext hx
    change MvPolynomial.eval T P = 0
    simpa only [he] using hzero x
  have hempty : interior Z = ∅ := interior_polynomial_zero_locus P hP
  apply Set.subset_empty_iff.mp
  simpa only [hempty] using interior_mono (closure_minimal hsub hclosed)

end ThreeEven

namespace ThreeEven.Dominance

open Set Filter
open ThreeEven.Dimension (interior_polynomial_zero_locus eval_substitution index_cons_equiv)
open scoped Topology Classical

lemma vector_is_simple {n : ℕ} (v : Holor ℂ [n]) : Holor.CPRankMax1 v := by
  let oneScalar : Holor ℂ [] := fun _ => 1
  have he : Holor.mul v oneScalar = v := by
    funext t
    change v t.take * (1 : ℂ) = v t
    rw [mul_one]
    congr 1
    apply Subtype.ext
    exact List.take_of_length_le t.property.length_eq.le
  rw [← he]
  exact Holor.CPRankMax1.cons _ _ (.nil _)

lemma tensor_sum_rank {d e f r : ℕ} (a : Fin r → Holor ℂ [d])
    (b : Fin r → Holor ℂ [e]) (c : Fin r → Holor ℂ [f]) :
    Holor.CPRankMax r (∑ i, Holor.mul (a i) (Holor.mul (b i) (c i))) := by
  have hs (i : Fin r) : Holor.CPRankMax1 (Holor.mul (a i) (Holor.mul (b i) (c i))) :=
    .cons _ _ (.cons _ _ (vector_is_simple (c i)))
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i => Holor.mul (a i) (Holor.mul (b i) (c i))) (fun i _ => Holor.cprankMax_1 (hs i))

/-- A constructible spectral image containing the generic point contains a
principal open neighborhood of it. -/
lemma open_in_spectral_image {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ f : A, f ≠ 0 ∧ ∀ q : PrimeSpectrum A, f ∉ q.asIdeal →
      q ∈ Set.range (PrimeSpectrum.comap φ) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hg : PrimeSpectrum.comap φ w = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hz : z ∈ T.toSet := by rw [hT]; exact ⟨w, hg⟩
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  change z ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    z ∉ PrimeSpectrum.zeroLocus {C.f} at hzC
  have hg0 (i : Fin C.n) : C.g i = 0 := by
    have h := (PrimeSpectrum.mem_zeroLocus z _).mp hzC.1 (Set.mem_range_self i)
    exact (Ideal.mem_bot : C.g i ∈ (⊥ : Ideal A) ↔ _).mp h
  have hf0 : C.f ≠ 0 := by
    intro e
    apply hzC.2
    exact (PrimeSpectrum.mem_zeroLocus z _).mpr (Set.singleton_subset_iff.mpr (e ▸ z.asIdeal.zero_mem))
  refine ⟨C.f, hf0, ?_⟩
  intro q hq
  rw [← hT]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    rintro _ ⟨i, rfl⟩
    rw [hg0 i]
    exact q.asIdeal.zero_mem
  · intro e
    exact hq ((PrimeSpectrum.mem_zeroLocus q _).mp e (Set.mem_singleton _))

/-- Hilbert's Nullstellensatz converts the principal open in the spectral image
to actual complex points in the image of the polynomial map. -/
lemma principal_open_in_image {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧ ∀ y : J → ℂ, MvPolynomial.eval y P ≠ 0 →
      ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (F j) = y j := by
  classical
  let φ : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ := MvPolynomial.aeval F
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial J ℂ))
    have he : φ.toRingHom.comp (algebraMap ℂ (MvPolynomial J ℂ)) =
        algebraMap ℂ (MvPolynomial I ℂ) :=
      RingHom.ext (fun a => φ.commutes a)
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨P, hP, hU⟩ := open_in_spectral_image φ.toRingHom hinj hfp
  refine ⟨P, hP, ?_⟩
  intro y hy
  let m := MvPolynomial.pointToPoint (k := ℂ) y
  have hy' : P ∉ m.asIdeal := fun h => hy ((MvPolynomial.mem_vanishingIdeal_singleton_iff y P).mp h)
  obtain ⟨q, hq⟩ := hU m hy'
  obtain ⟨M, hM, hle⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  intro j
  let v : MvPolynomial J ℂ := MvPolynomial.X j - MvPolynomial.C (y j)
  have hv : v ∈ m.asIdeal := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr
    simp [v]
  have hvq : φ v ∈ q.asIdeal := by
    change v ∈ (PrimeSpectrum.comap φ.toRingHom q).asIdeal
    rwa [hq]
  have hMx := hle hvq
  rw [hx] at hMx
  have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hMx
  simpa [φ, v, MvPolynomial.aeval_eq_eval, sub_eq_zero] using he

lemma dense_image_interior_of_nonempty {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))).Nonempty) :
    Dense (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))) := by
  classical
  let image := Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j))
  have hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ) := by
    apply algebraicIndependent_iff_injective_aeval.mp
    apply algebraicIndependent_iff.mpr
    intro Q hQ
    by_contra hne
    have hs : image ⊆ {y : J → ℂ | MvPolynomial.eval y Q = 0} := by
      rintro _ ⟨x, rfl⟩
      change MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) Q = 0
      rw [← eval_substitution F x Q, hQ, map_zero]
    obtain ⟨y, hy⟩ := h
    have bad := interior_mono hs hy
    rw [interior_polynomial_zero_locus Q hne] at bad
    exact bad
  obtain ⟨P, hP, hsurj⟩ := principal_open_in_image F hinj
  let Z := {y : J → ℂ | MvPolynomial.eval y P = 0}
  have ho : IsOpen Zᶜ := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hd : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (interior_polynomial_zero_locus P hP)
  apply hd.mono
  apply interior_maximal _ ho
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y hy
  exact ⟨x, funext hx⟩

/-- The derivative of each coordinate is the sum of its three factor variations. -/
lemma trilinear_image_has_interior {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (a b c : S → J → I) (base : I → ℂ)
    (hspan : ∀ y : J → ℂ, ∃ z : I → ℂ, ∀ j,
      y j = ∑ t : S, (z (a t j) * (base (b t j) * base (c t j)) +
        base (a t j) * (z (b t j) * base (c t j)) +
        base (a t j) * (base (b t j) * z (c t j)))) :
    (interior (Set.range (fun x : I → ℂ => fun j : J =>
      ∑ t : S, x (a t j) * (x (b t j) * x (c t j))))).Nonempty := by
  classical
  let φ (x : I → ℂ) (j : J) := ∑ t : S, x (a t j) * (x (b t j) * x (c t j))
  let pr (i : I) : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let D : (I → ℂ) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi fun j =>
    ∑ t : S, (base (a t j) • (base (b t j) • pr (c t j) + base (c t j) • pr (b t j)) +
      (base (b t j) * base (c t j)) • pr (a t j))
  have hder : HasStrictFDerivAt φ D base := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    apply HasStrictFDerivAt.fun_sum
    intro t _
    exact (pr (a t j)).hasStrictFDerivAt.fun_mul
      ((pr (b t j)).hasStrictFDerivAt.fun_mul (pr (c t j)).hasStrictFDerivAt)
  have hsurj : Function.Surjective D := by
    intro y
    obtain ⟨z, hz⟩ := hspan y
    refine ⟨z, funext fun j => ?_⟩
    rw [hz j]
    simp only [D, ContinuousLinearMap.pi_apply, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, pr,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hN : Set.range φ ∈ 𝓝 (φ base) := by
    rw [← hder.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)]
    exact Filter.range_mem_map
  exact ⟨φ base, mem_interior_iff_mem_nhds.mpr hN⟩

def index_nil_equiv : HolorIndex [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], .nil⟩
  left_inv := by rintro ⟨l, h⟩; cases h; rfl
  right_inv := by intro x; cases x; rfl

lemma finite_index (ds : List ℕ) : Finite (HolorIndex ds) := by
  induction ds with
  | nil => exact Finite.of_equiv Unit index_nil_equiv.symm
  | cons n ds ih =>
    let _ : Finite (HolorIndex ds) := ih
    exact Finite.of_equiv (Fin n × HolorIndex ds) (index_cons_equiv n ds).symm

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

def point {d e f : ℕ} (i : Fin d) (j : Fin e) (k : Fin f) : HolorIndex [d,e,f] :=
  ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩

lemma point_surjective {d e f : ℕ} (z : HolorIndex [d,e,f]) :
    ∃ i j k, z = point i j k := by
  obtain ⟨⟨i,z⟩,rfl⟩ := (index_cons_equiv d [e,f]).symm.surjective z
  obtain ⟨⟨j,z⟩,rfl⟩ := (index_cons_equiv e [f]).symm.surjective z
  obtain ⟨⟨k,z⟩,rfl⟩ := (index_cons_equiv f []).symm.surjective z
  obtain ⟨⟨⟩,rfl⟩ := index_nil_equiv.symm.surjective z
  exact ⟨i,j,k,rfl⟩

abbrev Coordinate (p : ℕ) := HolorIndex [3,2*p,2*p]
abbrev Parameter (p : ℕ) := Fin (3*p) × (Fin 3 ⊕ (Fin (2*p) ⊕ Fin (2*p)))

def entry {n : ℕ} (i : HolorIndex [n]) : Fin n := (index_cons_equiv n [] i).1

def first {p : ℕ} (t : Fin (3*p)) (z : Coordinate p) : Parameter p :=
  (t, Sum.inl (entry (HolorIndex.take (ds₁ := [3]) (ds₂ := [2*p,2*p]) z)))

def second {p : ℕ} (t : Fin (3*p)) (z : Coordinate p) : Parameter p :=
  (t, Sum.inr (.inl (entry (HolorIndex.take (ds₁ := [2*p]) (ds₂ := [2*p])
    (HolorIndex.drop (ds₁ := [3]) (ds₂ := [2*p,2*p]) z)))))

def third {p : ℕ} (t : Fin (3*p)) (z : Coordinate p) : Parameter p :=
  (t, Sum.inr (.inr (entry (HolorIndex.drop (ds₁ := [2*p]) (ds₂ := [2*p])
    (HolorIndex.drop (ds₁ := [3]) (ds₂ := [2*p,2*p]) z)))))

def pack {p : ℕ} (a : Fin (3*p) → Fin 3 → ℂ) (b c : Fin (3*p) → Fin (2*p) → ℂ)
    (q : Parameter p) : ℂ :=
  q.2.elim (a q.1) (Sum.elim (b q.1) (c q.1))

end ThreeEven.Dominance

namespace ThreeEven

open Set Dominance Arxiv.«0805.3777»

/-- Surjectivity of the tangent map at one parameter gives a dense open
set of tensors expressible as sums of at most 3p simple tensors. -/
theorem upper (p : ℕ) (hs : Spans p) : ∃ U : Set (Holor ℂ [3,2*p,2*p]),
    IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ 3*p := by
  classical
  obtain ⟨a,b,c,hspan⟩ := hs
  let _ : Finite (Coordinate p) := finite_index _
  let _ : Fintype (Coordinate p) := Fintype.ofFinite _
  let φ (x : Parameter p → ℂ) (j : Coordinate p) :=
    ∑ t : Fin (3*p), x (first t j) * (x (second t j) * x (third t j))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply trilinear_image_has_interior first second third (pack a b c)
    intro y
    obtain ⟨u,v,w,h⟩ := hspan fun i j k => y (point i j k)
    refine ⟨pack u v w, ?_⟩
    intro z
    obtain ⟨i,j,k,rfl⟩ := point_surjective z
    exact h i j k
  let F (j : Coordinate p) : MvPolynomial (Parameter p) ℂ :=
    ∑ t : Fin (3*p), MvPolynomial.X (first t j) *
      (MvPolynomial.X (second t j) * MvPolynomial.X (third t j))
  have he : (fun x : Parameter p → ℂ => fun j => MvPolynomial.eval x (F j)) = φ := by
    funext x j
    simp [F, φ]
  have hd := dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ), isOpen_interior, hd, ?_⟩
  intro T hT
  obtain ⟨x,rfl⟩ := interior_subset hT
  let xa (t : Fin (3*p)) (i : HolorIndex [3]) := x (t, Sum.inl (entry i))
  let xb (t : Fin (3*p)) (j : HolorIndex [2*p]) := x (t, Sum.inr (.inl (entry j)))
  let xc (t : Fin (3*p)) (k : HolorIndex [2*p]) := x (t, Sum.inr (.inr (entry k)))
  have hx : (φ x : Holor ℂ [3,2*p,2*p]) = ∑ t, Holor.mul (xa t) (Holor.mul (xb t) (xc t)) := by
    funext j
    rw [eval_holor_sum]
    rfl
  rw [hx]
  exact Nat.find_min' _ (tensor_sum_rank xa xb xc)

end ThreeEven

namespace ThreeEven
open Arxiv.«0805.3777» Set
open scoped Topology

lemma ceiling (p : ℕ) (hp : 1 ≤ p) : 12*p^2 ⌈/⌉ (4*p+1) = 3*p := by
  have hd : 0<4*p+1 := by omega
  apply Nat.le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr (by nlinarith))
  by_contra! h
  have hle : 12*p^2 ⌈/⌉ (4*p+1) ≤ 3*p-1 := by omega
  have hbad := (ceilDiv_le_iff_le_mul hd).mp hle
  have hp' : 3*p-1+1=3*p := by omega
  nlinarith [congrArg (fun k : ℕ => (4*p+1)*k) hp']

end ThreeEven

open Arxiv.«0805.3777» Set ThreeEven in
theorem OMA.solution : type_of% @Arxiv.«0805.3777».isGenericRank_three_even := by
  intro p hp
  rw [ceiling p (by omega)]
  obtain ⟨U,hopen,hdense,hupper⟩ := upper p (Grid.spans_of_cells p diagonal_cell off_diagonal_cell)
  let K := closure {T : Holor ℂ [3,2*p,2*p] | T.cprank ≤ 3*p-1}
  have hd : Dense Kᶜ := interior_eq_empty_iff_dense_compl.mp (lower p hp)
  refine ⟨U ∩ Kᶜ,hopen.inter isClosed_closure.isOpen_compl,hdense.inter_of_isOpen_left hd hopen,?_⟩
  intro T hT
  have hi := hupper T hT.1
  have lo : ¬ T.cprank ≤ 3*p-1 := fun he => hT.2 (subset_closure he)
  change T.cprank=3*p
  omega
