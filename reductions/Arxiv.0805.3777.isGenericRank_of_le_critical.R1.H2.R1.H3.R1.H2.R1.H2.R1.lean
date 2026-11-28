import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1

-- Credit: @mattdorman
/-!
# Remaining endpoint certificates for the strict generic-rank conjecture

For fixed first dimensions a,b and trial rank r, it suffices to treat the
largest third dimension in the integer interval with that dimension count.
A finite grid of factor coordinates suffices for each remaining tangent
certificate. Both implications are proved below.

The first construction splits any even axis into matrix pencils. Cyclic
pairings and separate first- and second-factor variations give a local
spanning tangent under the stated integer inequality. Taking a product of
nonzero minors makes a single choice of factors work on every block.
For first dimension three a second construction uses two compressed
diagonal commutators and connected cyclic frequency graphs.

The problem is Friedland, arXiv:0805.3777, Conjecture 5.1. The coordinate
specialization is related to Abo, Ottaviani and Peterson, arXiv:math/0607191,
section 3. The imported project reductions supply the finite-grid lemma,
the formal generic-rank transfer from PR 3300, and the higher-normal
equivalence from PR 12200.
-/

namespace CriticalHigher

theorem count_le_iff {A d n r : ℕ} (hd : 0<d) (hr : r<A) :
    A*n ⌈/⌉ (d+n) ≤ r ↔ n ≤ r*d/(A-r) := by
  rw [ceilDiv_le_iff_le_mul (by omega : 0<d+n), Nat.le_div_iff_mul_le (by omega : 0<A-r)]
  have split := congrArg (fun z : ℕ => z*n) (Nat.sub_add_cancel hr.le)
  constructor <;> intro h <;> nlinarith only [split,h]

/-- Both endpoints are exact, including ranks for which the integer interval
is empty. -/
theorem count_interval {A d n r : ℕ} (hd : 0<d) (hr : 0<r) (proper : r<A) :
    A*n ⌈/⌉ (d+n) = r ↔ (r-1)*d/(A-(r-1)) < n ∧ n ≤ r*d/(A-r) := by
  have hi := count_le_iff (n:=n) hd proper
  have lo := count_le_iff (n:=n) hd (by omega : r-1<A)
  omega

theorem endpoint_count {A d n r : ℕ} (hd : 0<d) (hr : 0<r) (proper : r<A)
    (count : A*n ⌈/⌉ (d+n)=r) :
    let N := r*d/(A-r)
    n≤N ∧ A*N ⌈/⌉ (d+N)=r := by
  obtain ⟨lo,hi⟩ := (count_interval hd hr proper).mp count
  exact ⟨hi,(count_interval hd hr proper).mpr ⟨lo.trans_le hi,le_rfl⟩⟩

/-- The dimension budget for normal planes of arbitrary dimension.
The common annihilator has dimension A−r. Each point contributes A−r−d
scalar unknowns, and the third vectors supply r−n relations. -/
theorem normal_budget {A d n r : ℕ} (hd : 0<d) (proper : r<A) (small : d≤A-r)
    (count : A*n ⌈/⌉ (d+n)=r) :
    n≤r ∧ (A-r-d)*r ≤ (r-n)*(A-r) := by
  have upper := (count_le_iff hd proper).mp count.le
  have product := (Nat.le_div_iff_mul_le (by omega : 0<A-r)).mp upper
  have size : n≤r :=
    Nat.le_of_mul_le_mul_right (product.trans (Nat.mul_le_mul_left r small)) (by omega)
  have lhs := congrArg (fun z : ℕ => r*z) (Nat.sub_add_cancel small)
  have rhs := congrArg (fun z : ℕ => z*(A-r)) (Nat.sub_add_cancel size)
  exact ⟨size,by nlinarith only [lhs,rhs,product]⟩

end CriticalHigher

namespace CriticalLastSlice.TwoPlanes

open MvPolynomial Arxiv.«0805.3777»

/-- A complex spanning tangent witness exists exactly when the normal tuples
at the independent rational-function coordinates are detected by the third-factor relations. -/
theorem witness_iff_normals {a b n r : ℕ} (enough : n ≤ r) :
    (∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q (s : V) := algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := q (t,.inl i)
    let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
    ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j*F t (i,j)=0) → (∀ t j, ∑ i, x t i*F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0 := by
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
  let R := MvPolynomial V ℂ
  let K := FractionRing R
  let q (s : V) := algebraMap R K (X s)
  let x (t : Fin r) (i : Fin a) := q (t,.inl i)
  let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
  let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
  let P : Matrix ((Fin a × Fin b) × Fin n) V R := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
      (Sum.elim (fun j => if j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
        (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  have specialized := CriticalJacobian.restricted_tangent_iff (a:=a) (b:=b) (c:=n) (r:=r) id P
    (fun _ _ _ _ _ => rfl)
  apply specialized.trans ((CriticalTensor.Unrestricted.generic_surjective_iff P).symm.trans ?_)
  apply LastSliceRelation.tangent_iff_normal_relations x y z (CriticalLastSlice.third_span a b n r enough)
  intro i j k t v
  change algebraMap R K (P ((i,j),k) (t,v)) = _
  rcases v with i' | j' | k'
  · by_cases hi : i'=i <;> simp [P,x,y,z,q,hi]
  · by_cases hj : j'=j <;> simp [P,x,y,z,q,hj]
  · by_cases hk : k'=k <;> simp [P,x,y,z,q,hk]

/-- A spanning witness at the parameter-count ceiling gives the original
complex generic-rank conclusion in balanced dimensions. -/
theorem generic_rank_of_witness {a b n r : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hbn : b ≤ n)
    (count : r = a*b*n ⌈/⌉ (a+b+n-2))
    (witness : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    IsGenericRank [a,b,n] r := by
  subst r
  exact OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b n ha hab hbn
    (CriticalReduction.bounded_of_witness witness)

end CriticalLastSlice.TwoPlanes

namespace CriticalHigher

/-- A spanning witness on the seed slice space restricts to every smaller
third dimension, preserving the number of points. -/
theorem project {a b k e w : ℕ} (hk : k≤e)
    (seed : ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin e → ℂ,
      ∀ T : Fin a → Fin b → Fin e → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin e → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin k → ℂ,
      ∀ T : Fin a → Fin b → Fin k → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin k → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)) := by
  obtain ⟨x,y,z,span⟩ := seed
  refine ⟨x,y,fun t l => z t (Fin.castLE hk l),?_⟩
  intro T
  let extT (i : Fin a) (j : Fin b) (l : Fin e) := if hl : l.val<k then T i j ⟨l.val,hl⟩ else 0
  obtain ⟨u,v,s,hs⟩ := span extT
  refine ⟨u,v,fun t l => s t (Fin.castLE hk l),?_⟩
  intro i j l
  simpa [extT,l.isLt] using hs i j (Fin.castLE hk l)

end CriticalHigher

namespace CriticalHigher

theorem available_normals {a b r : ℕ} (ha : 3≤a) (hab : a≤b)
    (level : r+1<(a-1)*(b-1)) : r<a*b ∧ a+b-2≤a*b-r := by
  have identity : (a-1)*(b-1)+(a+b-1)=a*b := by
    obtain ⟨i,rfl⟩ : ∃ i : ℕ, a=i+1 := ⟨a-1,by omega⟩
    obtain ⟨j,rfl⟩ : ∃ j : ℕ, b=j+1 := ⟨b-1,by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show i+1+(j+1)-1=i+j+1 by omega]
    ring
  omega

theorem witness_at_count
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2)
    {a b n r : ℕ} (ha : 3≤a) (hab : a≤b) (start : b+2≤n)
    (level : r+1<(a-1)*(b-1)) (count : a*b*n ⌈/⌉ ((a+b-2)+n)=r) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  obtain ⟨proper,small⟩ := available_normals ha hab level
  have enough := (normal_budget (by omega : 0<a+b-2) proper small count).1
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have denom : (a+b-2)+(c+1)=a+b+(c+1)-2 := by omega
  rw [denom] at count
  subst r
  exact (CriticalLastSlice.TwoPlanes.witness_iff_normals (a:=a) (b:=b) enough).mpr
    (higher a b c ha hab (by omega) (by omega) level)

/-- For fixed a,b,r the entire registered normal-space problem is equivalent
to one complex spanning tangent at the largest integer third dimension of the
rank interval. Empty intervals and endpoints outside the strict rectangle
do not require witnesses. -/
theorem higher_iff_endpoints :
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2 ↔
    ∀ a b r : ℕ, 3≤a → a≤b → 0<r → r+1<(a-1)*(b-1) →
      let A := a*b
      let d := a+b-2
      let N := r*d/(A-r)
      b+2≤N → (r-1)*d/(A-(r-1))<N →
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
        ∀ T : Fin a → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin a → ℂ,
          ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
            T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  constructor
  · intro parent a b r ha hab hr level A d N start present
    have proper := (available_normals ha hab level).1
    apply witness_at_count parent ha hab start level
    exact (count_interval (by omega : 0<a+b-2) hr proper).mpr ⟨present,le_rfl⟩
  · intro endpoints a b c ha hab hbc region w r level
    change r+1<(a-1)*(b-1) at level
    have denom : (a+b-2)+(c+1)=a+b+(c+1)-2 := by omega
    have count : a*b*(c+1) ⌈/⌉ ((a+b-2)+(c+1))=r := by rw [denom]
    obtain ⟨proper,small⟩ := available_normals ha hab level
    have hd : 0<a+b-2 := by omega
    have enough := (normal_budget hd proper small count).1
    have hr : 0<r := by omega
    obtain ⟨lo,hi⟩ := (count_interval hd hr proper).mp count
    have witness := endpoints a b r ha hab hr level ((by omega : b+2≤c+1).trans hi) (lo.trans_le hi)
    exact (CriticalLastSlice.TwoPlanes.witness_iff_normals (a:=a) (b:=b) enough).mp
      (CriticalHigher.project hi witness)

end CriticalHigher

namespace CriticalHigher.Blocks

open MvPolynomial

/-- A full-row-rank specialization gives a nonzero determinant polynomial.
Taking the product gives one specialization for a finite family of matrices. -/
theorem common_surjective {G V : Type*} [Fintype G] {I J : G → Type*}
    [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (M : ∀ g, Matrix (I g) (J g) (MvPolynomial V ℂ))
    (each : ∀ g, ∃ v : V → ℂ, Function.Surjective ((M g).map (eval v)).mulVec) :
    ∃ p : V → ℂ, ∀ g, Function.Surjective ((M g).map (eval p)).mulVec := by
  classical
  choose v good using each
  choose B inverse using fun g => Matrix.mulVec_surjective_iff_exists_right_inverse.mp (good g)
  let P (g : G) := (B g).map (C : ℂ →+* MvPolynomial V ℂ)
  let Q (g : G) := (M g*P g).det
  have spec (g : G) (u : V → ℂ) :
      eval u (Q g) = ((M g).map (eval u)*B g).det := by
    have constant : (P g).map (eval u)=B g := by ext; simp [P,Matrix.map_apply]
    change eval u (M g*P g).det = _
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,constant]
  have nz (g : G) : Q g≠0 := by
    intro zero
    have atPoint := spec g (v g)
    rw [zero,map_zero,inverse g,Matrix.det_one] at atPoint
    exact zero_ne_one atPoint
  have allnz : (∏ g,Q g)≠0 := Finset.prod_ne_zero_iff.mpr fun g _ => nz g
  obtain ⟨p,hp⟩ : ∃ p : V → ℂ, eval p (∏ g,Q g)≠0 := by
    by_contra! vanish
    exact allnz (MvPolynomial.funext fun q => by rw [vanish q,map_zero])
  have eachnz : (∏ g,eval p (Q g))≠0 := by simpa only [map_prod] using hp
  refine ⟨p,fun g => ?_⟩
  have hdet := Finset.prod_ne_zero_iff.mp eachnz g (Finset.mem_univ g)
  rw [spec] at hdet
  have onto := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro t
  obtain ⟨s,hs⟩ := onto t
  exact ⟨(B g).mulVec s,(Matrix.mulVec_mulVec _ _ _).trans hs⟩

/-- In one block all sampled products have free variations in the last
factor. Only the samples assigned to the block have their first two
variations present. Each separately verified block can use different
factors before common specialization. -/
theorem common_tangents {A B C P G : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype P] [Fintype G] [DecidableEq G] (label : P → G) :
    let D (g : G) (x : P → A → ℂ) (y : P → B → ℂ) (z : P → C → ℂ) :=
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, ((if label t=g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))
    (∀ g, ∃ x y z, D g x y z) → ∃ x y z, ∀ g, D g x y z := by
  classical
  intro D each
  let V := P × (A ⊕ (B ⊕ C))
  let M (g : G) : Matrix ((A × B) × C) V (MvPolynomial V ℂ) := fun row col => col.2.elim
    (fun i => if label col.1=g ∧ i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
    (Sum.elim
      (fun j => if label col.1=g ∧ j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
      (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  let pack (x : P → A → ℂ) (y : P → B → ℂ) (z : P → C → ℂ) : V → ℂ :=
    fun (t,q) => q.elim (x t) (Sum.elim (y t) (z t))
  have action (g : G) (p q : V → ℂ) (i : A) (j : B) (k : C) :
      ((M g).map (eval p)).mulVec q ((i,j),k) = ∑ t,
        ((if label t=g then q (t,.inl i)*(p (t,.inr (.inl j))*p (t,.inr (.inr k))) +
           p (t,.inl i)*(q (t,.inr (.inl j))*p (t,.inr (.inr k))) else 0) +
           p (t,.inl i)*(p (t,.inr (.inl j))*q (t,.inr (.inr k)))) := by
    change (∑ s : V, eval p (M g ((i,j),k) s)*q s) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    by_cases hit : label t=g <;> simp [M,hit,apply_ite,ite_mul,Finset.sum_ite_eq'] <;> ring
  have localFull (g : G) : ∃ p : V → ℂ, Function.Surjective ((M g).map (eval p)).mulVec := by
    obtain ⟨x,y,z,h⟩ := each g
    refine ⟨pack x y z,?_⟩
    intro T
    obtain ⟨u,v,w,cover⟩ := h fun i j k => T ((i,j),k)
    refine ⟨pack u v w,?_⟩
    funext ⟨⟨i,j⟩,k⟩
    exact (action g (pack x y z) (pack u v w) i j k).trans (cover i j k).symm
  obtain ⟨p,good⟩ := common_surjective M localFull
  refine ⟨fun t i => p (t,.inl i),fun t j => p (t,.inr (.inl j)),fun t k => p (t,.inr (.inr k)),?_⟩
  intro g T
  obtain ⟨q,hq⟩ := good g fun s => T s.1.1 s.1.2 s.2
  exact ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),fun t k => q (t,.inr (.inr k)),
    fun i j k => (congrFun hq ((i,j),k)).symm.trans (action g p q i j k)⟩

/-- Put each point's third vector in its assigned coordinate block. Third
variations can act on all blocks independently, so the local witnesses
produce a spanning tangent for the whole tensor. -/
theorem spans_of_blocks {A B C P G : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype P] [Fintype G] [DecidableEq G] (label : P → G)
    (one : ∀ g, ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∃ z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, ((if label t=g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∃ Z : P → G × C → ℂ,
      ∀ T : A → B → G × C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → G × C → ℂ,
        ∀ i j k, T i j k=∑ t,(u t i*(y t j*Z t k)+x t i*(v t j*Z t k)+x t i*(y t j*w t k)) := by
  classical
  obtain ⟨x,y,z,good⟩ := common_tangents label one
  let Z (t : P) (p : G × C) := if label t=p.1 then z t p.2 else 0
  refine ⟨x,y,Z,?_⟩
  intro T
  choose U V W repr using fun g => good g (fun i j k => T i j (g,k))
  refine ⟨fun t => U (label t) t, fun t => V (label t) t, fun t k => W k.1 t k.2,?_⟩
  rintro i j ⟨g,k⟩
  apply (repr g i j k).trans
  apply Finset.sum_congr rfl
  intro t _
  by_cases hit : label t=g <;> simp [Z,hit]

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

/-- Reindex a full tangent plus an external-product supplement onto any
finite point set, allowing the first two variations only on its marked set. -/
private theorem restricted_tangent_of_split {A B C P M N : Type*}
    [Fintype P] [Fintype M] [Fintype N] (active : P → Prop) [DecidablePred active]
    (e : (M ⊕ N) ≃ P) (marked : ∀ t : M, active (e (.inl t)))
    (one : ∃ x : M → A → ℂ, ∃ y : M → B → ℂ, ∃ z : M → C → ℂ,
      ∃ x' : N → A → ℂ, ∃ y' : N → B → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : M → A → ℂ, ∃ v : M → B → ℂ, ∃ w : M → C → ℂ,
      ∃ w' : N → C → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
      T i j k = ∑ t, ((if active t then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
        X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,x',y',hit⟩ := one
  let X (p : P) := (e.symm p).elim x x'
  let Y (p : P) := (e.symm p).elim y y'
  let Z (p : P) := (e.symm p).elim z 0
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨u,v,w,w',cover⟩ := hit T
  refine ⟨fun p => (e.symm p).elim u 0,fun p => (e.symm p).elim v 0,fun p => (e.symm p).elim w w',?_⟩
  intro i j k
  rw [cover i j k,← e.sum_comp,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    simp only [X,Y,Z,Equiv.symm_apply_apply,Sum.elim_inl,if_pos (marked t)]
  · apply Finset.sum_congr rfl
    intro t _
    simp [X,Y,Z]

/-- Choose a complementary enumeration for one group among the r points.
The designated group is the left summand and every other point is external. -/
private theorem pencil_group_complement {h m r : ℕ} (slots : h*m ≤ r) (g : Fin h) :
    ∃ e : (Fin m ⊕ Fin (r-m)) ≃ ((Fin h × Fin m) ⊕ Fin (r-h*m)),
      ∀ j : Fin m, e (.inl j) = .inl (g,j) := by
  classical
  let P := (Fin h × Fin m) ⊕ Fin (r-h*m)
  let f : Fin m → P := fun j => .inl (g,j)
  have finj : Function.Injective f := fun u v ev => congrArg Prod.snd (Sum.inl.inj ev)
  let front := Equiv.ofInjective f finj
  have size : Fintype.card P = r := by
    simp only [P,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have frontSize : Fintype.card {p : P // p ∈ Set.range f} = m := by
    rw [← Fintype.card_congr front,Fintype.card_fin]
  let rest : {p : P // p ∉ Set.range f} ≃ Fin (r-m) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl,frontSize,size])
  let e := (Equiv.sumCongr front rest.symm).trans (Equiv.sumCompl (fun p => p ∈ Set.range f))
  exact ⟨e,fun _ => rfl⟩

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

theorem tangent_cycle {A B C P : Type*} [Fintype P]
    (one : ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ,
      ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k))) :
    ∃ X : P → C → ℂ, ∃ Y : P → A → ℂ, ∃ Z : P → B → ℂ,
    ∀ T : C → A → B → ℂ, ∃ u : P → C → ℂ, ∃ v : P → A → ℂ,
    ∃ w : P → B → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,cover⟩ := one
  refine ⟨z,x,y,?_⟩
  intro T
  obtain ⟨u,v,w,rep⟩ := cover (fun i j k => T k i j)
  refine ⟨w,u,v,?_⟩
  intro k i j
  rw [rep i j k]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem tangent_swap_last {A B C P : Type*} [Fintype P]
    (one : ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ,
      ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k))) :
    ∃ X : P → A → ℂ, ∃ Y : P → C → ℂ, ∃ Z : P → B → ℂ,
    ∀ T : A → C → B → ℂ, ∃ u : P → A → ℂ, ∃ v : P → C → ℂ,
    ∃ w : P → B → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,cover⟩ := one
  refine ⟨x,z,y,?_⟩
  intro T
  obtain ⟨u,v,w,rep⟩ := cover (fun i j k => T i k j)
  refine ⟨u,w,v,?_⟩
  intro i k j
  rw [rep i j k]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem many_pencil_third (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin (2*h) → ℂ,
    ∀ T : Fin a → Fin b → Fin (2*h) → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
    ∃ w : Fin r → Fin (2*h) → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  by_cases empty : h=0
  · subst h
    exact ⟨0,0,0,fun _ => ⟨0,0,0,fun _ _ k => Fin.elim0 k⟩⟩
  let P := (Fin h × Fin m) ⊕ Fin (r-h*m)
  let label : P → Fin h := Sum.elim Prod.fst (fun _ => ⟨0,Nat.pos_of_ne_zero empty⟩)
  have each (g : Fin h) : ∃ X : P → Fin a → ℂ, ∃ Y : P → Fin b → ℂ, ∃ Z : P → Fin 2 → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : P → Fin a → ℂ, ∃ v : P → Fin b → ℂ, ∃ w : P → Fin 2 → ℂ,
      ∀ i j k, T i j k = ∑ t, ((if label t=g then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
        X t i*(Y t j*w t k)) := by
    obtain ⟨e,he⟩ := pencil_group_complement slots g
    apply restricted_tangent_of_split (fun t => label t=g) e _ one
    intro s
    rw [he s]
    rfl
  obtain ⟨x,y,z,span⟩ := spans_of_blocks label each
  let points : P ≃ Fin r := Fintype.equivFinOfCardEq (by
    simp only [P,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega)
  let coords : (Fin h × Fin 2) ≃ Fin (2*h) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨fun t => x (points.symm t),fun t => y (points.symm t),fun t k => z (points.symm t) (coords.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,hcover⟩ := span fun i j k => T i j (coords k)
  refine ⟨fun t => u (points.symm t),fun t => v (points.symm t),fun t k => w (points.symm t) (coords.symm k),?_⟩
  intro i j k
  have atRow := hcover i j (coords.symm k)
  simp only [Equiv.apply_symm_apply] at atRow
  rw [atRow,← points.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem many_pencil_first (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin (2*h) → ℂ, ∃ Y : Fin r → Fin a → ℂ, ∃ Z : Fin r → Fin b → ℂ,
    ∀ T : Fin (2*h) → Fin a → Fin b → ℂ, ∃ u : Fin r → Fin (2*h) → ℂ, ∃ v : Fin r → Fin a → ℂ,
    ∃ w : Fin r → Fin b → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  exact tangent_cycle (many_pencil_third a b h m r slots one)

theorem many_pencil_second (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin (2*h) → ℂ, ∃ Z : Fin r → Fin b → ℂ,
    ∀ T : Fin a → Fin (2*h) → Fin b → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin (2*h) → ℂ,
    ∃ w : Fin r → Fin b → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  exact tangent_swap_last (many_pencil_third a b h m r slots one)

end CriticalHigher.Blocks

namespace CriticalLastSlice.HigherPencil

/-- Pair consecutive positions in the listing by layer and then label. When
the last position is alone, pair it with the first. Every pair uses two
different labels, and each label's layers occur at distinct primary samples. -/
theorem cyclic_schedule (m n : ℕ) (hm : 2≤ m) :
    let S := Fin ((n*m+1)/2)
    ∃ L R : S → Fin n × Fin m, ∃ sample : Fin m → Fin n → S,
      (∀ s,(L s).2 ≠ (R s).2) ∧ (∀ i,Function.Injective (sample i)) ∧
      ∀ i j,L (sample i j)=(j,i) ∨ R (sample i j)=(j,i) := by
  intro S
  let even (s : S) : Fin (n*m) := ⟨2*s.val,by have := s.isLt; omega⟩
  let next (s : S) : Fin (n*m) := if h : 2*s.val+1<n*m then ⟨2*s.val+1,h⟩
    else ⟨0,by have := s.isLt; omega⟩
  let sample (i : Fin m) (j : Fin n) : S :=
    ⟨(finProdFinEquiv (j,i)).val/2,by have := (finProdFinEquiv (j,i)).isLt; omega⟩
  have next_ne (q : ℕ) : q%m ≠ (q+1)%m := by
    rw [Nat.add_mod,Nat.mod_eq_of_lt (by omega : 1< m)]
    have bound := Nat.mod_lt q (by omega : 0< m)
    by_cases hs : q%m+1< m
    · rw [Nat.mod_eq_of_lt hs]; omega
    · rw [show q%m+1=m by omega,Nat.mod_self]; omega
  refine ⟨fun s => finProdFinEquiv.symm (even s),fun s => finProdFinEquiv.symm (next s),
    sample,?_,?_,?_⟩
  · intro s hg
    apply next_ne (2*s.val)
    have eq := congrArg Fin.val hg
    change (2*s.val)%m=(next s).val%m at eq
    by_cases h : 2*s.val+1<n*m
    · simpa only [next,dif_pos h] using eq
    · have last : 2*s.val+1=n*m := by have := (even s).isLt; change 2*s.val<n*m at this; omega
      simpa [next,h,last] using eq
  · intro i j k eq
    have strict : StrictMono (fun t : ℕ => (i.val+m*t)/2) := by
      apply strictMono_nat_of_lt_succ
      intro t
      have bound : i.val+m*t+2 ≤ i.val+m*(t+1) := by rw [Nat.mul_add]; omega
      omega
    exact Fin.ext (strict.injective (congrArg Fin.val eq))
  · intro i j
    let q := finProdFinEquiv (j,i)
    have hit : (sample i j).val=q.val/2 := rfl
    by_cases h : q.val%2=0
    · left
      have he : even (sample i j)=q := Fin.ext (by change 2*(sample i j).val=q.val; omega)
      exact (congrArg finProdFinEquiv.symm he).trans (finProdFinEquiv.symm_apply_apply _)
    · right
      have he : 2*(sample i j).val+1=q.val := by omega
      have bound : 2*(sample i j).val+1<n*m := he ▸ q.isLt
      have hn : next (sample i j)=q := Fin.ext (by simp only [next,dif_pos bound,he])
      exact (congrArg finProdFinEquiv.symm hn).trans (finProdFinEquiv.symm_apply_apply _)

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- Two pencil coefficients separate the evaluations at different labels.
Vandermonde interpolation at each label's distinct samples recovers both
the complete marked row tail and the complete marked column tail. -/
theorem interpolate_slots {m d e : ℕ} {S : Type*}
    (node : S → ℂ) (hn : Function.Injective node) (μ : Fin m → ℂ) (hμ : Function.Injective μ)
    (L R : S → (Fin e ⊕ Fin d) × Fin m) (sample : Fin m → (Fin e ⊕ Fin d) → S)
    (separate : ∀ s,(L s).2 ≠ (R s).2) (distinct : ∀ i,Function.Injective (sample i))
    (cover : ∀ i j,L (sample i j)=(j,i) ∨ R (sample i j)=(j,i))
    (Y : Fin m → Fin e → ℂ) (X : Fin m → Fin d → ℂ) :
    let value (s : S) (q : (Fin e ⊕ Fin d) × Fin m) := q.1.elim
      (fun _ => ∑ j : Fin e,node s^j.val*Y q.2 j) (fun _ => ∑ i : Fin d,node s^i.val*X q.2 i)
    (∀ s,value s (L s)+value s (R s)=0) →
    (∀ s,μ (L s).2*value s (L s)+μ (R s).2*value s (R s)=0) → Y=0 ∧ X=0 := by
  intro value h₀ h₁
  have zero (s : S) : value s (L s)=0 ∧ value s (R s)=0 := by
    have diff : (μ (L s).2-μ (R s).2)*value s (L s)=0 := by
      linear_combination h₁ s - μ (R s).2 * h₀ s
    have nz : μ (L s).2-μ (R s).2≠0 := sub_ne_zero.mpr (fun eq => separate s (hμ eq))
    have left := (mul_eq_zero.mp diff).resolve_left nz
    exact ⟨left,by simpa only [left,zero_add] using h₀ s⟩
  have sampled (i : Fin m) (j : Fin e ⊕ Fin d) : value (sample i j) (j,i)=0 := by
    rcases cover i j with hl|hr
    · simpa only [hl] using (zero (sample i j)).1
    · simpa only [hr] using (zero (sample i j)).2
  constructor
  · funext i
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (f:=fun j : Fin e => node (sample i (.inl j)))
    · intro j k eq
      exact Sum.inl.inj (distinct i (hn eq))
    · exact fun j => sampled i (.inl j)
  · funext i
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (f:=fun j : Fin d => node (sample i (.inr j)))
    · intro j k eq
      exact Sum.inr.inj (distinct i (hn eq))
    · exact fun j => sampled i (.inr j)

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- A pure bilinear sample on the two off-diagonal blocks splits into its
upper row contributions and its upper column contributions. -/
theorem sample_off_diagonal {m d e : ℕ} (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
    (core : ∀ i j,M (.inl i) (.inl j)=0) (bottom : ∀ i j,M (.inr i) (.inr j)=0)
    (x y : Fin m → ℂ) (x' : Fin d → ℂ) (y' : Fin e → ℂ) :
    (∑ i,∑ j,(Sum.elim x x' i)*(Sum.elim y y' j)*M i j) =
      (∑ i,x i*(∑ j,y' j*M (.inl i) (.inr j))) +
      (∑ j,y j*(∑ i,x' i*M (.inr i) (.inl j))) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,core,bottom,mul_zero,
    Finset.sum_const_zero,zero_add,add_zero]
  congr 1
  · simp only [Finset.mul_sum,mul_assoc]
  · rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- One product reads two evaluation slots at the same Vandermonde node
regardless of whether the slots concern rows, columns, or one of each. -/
theorem two_slot_sample {m d e : ℕ} (z : ℂ) (L R : (Fin e ⊕ Fin d) × Fin m) :
    ∃ x : (Fin m ⊕ Fin d) → ℂ, ∃ y : (Fin m ⊕ Fin e) → ℂ,
      ∀ M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ,
        (∀ i j,M (.inl i) (.inl j)=0) → (∀ i j,M (.inr i) (.inr j)=0) →
        let value (q : (Fin e ⊕ Fin d) × Fin m) := q.1.elim
          (fun _ => ∑ j : Fin e,z^j.val*M (.inl q.2) (.inr j))
          (fun _ => ∑ i : Fin d,z^i.val*M (.inr i) (.inl q.2))
        (∑ i,∑ j,x i*y j*M i j)=value L+value R := by
  classical
  let xw (q : (Fin e ⊕ Fin d) × Fin m) (i : Fin m) : ℂ :=
    q.1.elim (fun _ => if i=q.2 then 1 else 0) (fun _ => 0)
  let yw (q : (Fin e ⊕ Fin d) × Fin m) (i : Fin m) : ℂ :=
    q.1.elim (fun _ => 0) (fun _ => if i=q.2 then 1 else 0)
  let x (i : Fin m) := xw L i+xw R i
  let y (i : Fin m) := yw L i+yw R i
  refine ⟨Sum.elim x (fun i => z^i.val),Sum.elim y (fun j => z^j.val),?_⟩
  intro M core bottom value
  rw [sample_off_diagonal M core bottom]
  rcases L with ⟨i|i,u⟩ <;> rcases R with ⟨j|j,v⟩ <;>
    simp [x,y,xw,yw,value,add_mul,Finset.sum_add_distrib,ite_mul,Finset.sum_ite_eq',add_comm]

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- Place m full points on the diagonal with third vectors (1,λᵢ). A further
d*e + ceil(m*(d+e)/2) pure products force the whole dual pencil to vanish.
Here the two matrix dimensions are m+d and m+e. -/
theorem product_samples {m d e : ℕ} (hm : 2 ≤ m)
    (lam : Fin m → ℂ) (hlam : Function.Injective lam) :
    let S := Fin (((e+d)*m+1)/2)
    let P := (Fin d × Fin e) ⊕ S
    ∃ x : P → (Fin m ⊕ Fin d) → ℂ, ∃ y : P → (Fin m ⊕ Fin e) → ℂ,
      ∀ U V : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ,
        (∀ i,U (.inl i) (.inl i)=0 ∧ V (.inl i) (.inl i)=0) →
        (∀ i j,U (.inl i) j+lam i*V (.inl i) j=0) →
        (∀ i j,U j (.inl i)+lam i*V j (.inl i)=0) →
        (∀ p,∑ i,∑ j,x p i*y p j*U i j=0) →
        (∀ p,∑ i,∑ j,x p i*y p j*V i j=0) → U=0 ∧ V=0 := by
  classical
  intro S P
  obtain ⟨L₀,R₀,pick,ne,dist,cover₀⟩ := cyclic_schedule m (e+d) hm
  let decode (q : Fin (e+d) × Fin m) : (Fin e ⊕ Fin d) × Fin m := (finSumFinEquiv.symm q.1,q.2)
  let L (s : S) := decode (L₀ s)
  let R (s : S) := decode (R₀ s)
  let sample (i : Fin m) (q : Fin e ⊕ Fin d) := pick i (finSumFinEquiv q)
  have cover (i : Fin m) (q : Fin e ⊕ Fin d) :
      L (sample i q)=(q,i) ∨ R (sample i q)=(q,i) := by
    have back : decode (finSumFinEquiv q,i)=(q,i) := by simp [decode]
    rcases cover₀ i (finSumFinEquiv q) with hl|hr
    · exact Or.inl ((congrArg decode hl).trans back)
    · exact Or.inr ((congrArg decode hr).trans back)
  let node (s : S) : ℂ := s.val
  choose xs ys reading using fun s : S => two_slot_sample (node s) (L s) (R s)
  let x : P → (Fin m ⊕ Fin d) → ℂ := Sum.elim (fun q i => if i=.inr q.1 then 1 else 0) xs
  let y : P → (Fin m ⊕ Fin e) → ℂ := Sum.elim (fun q j => if j=.inr q.2 then 1 else 0) ys
  let eval (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ) (s : S) (q : (Fin e ⊕ Fin d) × Fin m) :=
    q.1.elim (fun _ => ∑ j : Fin e,node s^j.val*M (.inl q.2) (.inr j))
      (fun _ => ∑ i : Fin d,node s^i.val*M (.inr i) (.inl q.2))
  have lower (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
      (sampled : ∀ p,∑ i,∑ j,x p i*y p j*M i j=0) (i : Fin d) (j : Fin e) :
      M (.inr i) (.inr j)=0 := by
    have h := sampled (.inl (i,j))
    simpa [x,y,ite_mul,Finset.sum_ite_eq',Finset.sum_ite_irrel] using h
  have evals (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
      (core : ∀ i j,M (.inl i) (.inl j)=0) (sampled : ∀ p,∑ i,∑ j,x p i*y p j*M i j=0)
      (s : S) : eval M s (L s)+eval M s (R s)=0 :=
    (reading s M core (lower M sampled)).symm.trans (sampled (.inr s))
  refine ⟨x,y,?_⟩
  intro U V diag row col testU testV
  have core (i j : Fin m) : U (.inl i) (.inl j)=0 ∧ V (.inl i) (.inl j)=0 := by
    by_cases eq : i=j
    · subst j
      exact diag i
    · have weighted : (lam i-lam j)*V (.inl i) (.inl j)=0 := by
        linear_combination row i (.inl j)-col j (.inl i)
      have vzero := (mul_eq_zero.mp weighted).resolve_left (sub_ne_zero.mpr (fun h => eq (hlam h)))
      exact ⟨by simpa only [vzero,mul_zero,add_zero] using row i (.inl j),vzero⟩
  have rowU (i : Fin m) (j : Fin e) :
      U (.inl i) (.inr j)=(-lam i)*V (.inl i) (.inr j) := by
    linear_combination row i (.inr j)
  have colU (i : Fin m) (j : Fin d) :
      U (.inr j) (.inl i)=(-lam i)*V (.inr j) (.inl i) := by
    linear_combination col i (.inr j)
  have relate (s : S) (q : (Fin e ⊕ Fin d) × Fin m) :
      eval U s q=(-lam q.2)*eval V s q := by
    rcases q with ⟨j|i,k⟩
    · simp only [eval,Sum.elim_inl,Finset.mul_sum,rowU]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [eval,Sum.elim_inr,Finset.mul_sum,colU]
      apply Finset.sum_congr rfl
      intro j _
      ring
  have plain := evals V (fun i j => (core i j).2) testV
  have weighted (s : S) : (-lam (L s).2)*eval V s (L s)+(-lam (R s).2)*eval V s (R s)=0 := by
    rw [← relate,← relate]
    exact evals U (fun i j => (core i j).1) testU s
  obtain ⟨Yzero,Xzero⟩ := interpolate_slots node (fun i j h => Fin.ext (Nat.cast_injective h))
    (fun i => -lam i) (fun i j h => hlam (neg_inj.mp h)) L R sample ne
    (fun i => (dist i).comp finSumFinEquiv.injective) cover
    (fun i j => V (.inl i) (.inr j)) (fun i j => V (.inr j) (.inl i)) plain weighted
  have zero : V=0 := by
    funext i j
    rcases i with i|i <;> rcases j with j|j
    · exact (core i j).2
    · exact congrFun (congrFun Yzero i) j
    · exact congrFun (congrFun Xzero j) i
    · exact lower V testV i j
  refine ⟨?_,zero⟩
  funext i j
  rcases i with i|i <;> rcases j with j|j
  · exact (core i j).1
  · simpa only [zero,Matrix.zero_apply,mul_zero] using rowU i j
  · simpa only [zero,Matrix.zero_apply,mul_zero] using colU j i
  · exact lower U testU i j

end CriticalLastSlice.HigherPencil

namespace HigherPencil

/-- A tensor annihilating the three tangent variations at each marked point
and the third variation at each exterior point detects surjectivity of their sum. -/
theorem augmented_span_of_annihilator {𝕜 I J K P Q : Type*} [Field 𝕜]
    [Fintype I] [Fintype J] [Fintype K] [Fintype P] [Fintype Q]
    (x : P → I → 𝕜) (y : P → J → 𝕜) (z : P → K → 𝕜) (x' : Q → I → 𝕜) (y' : Q → J → 𝕜)
    (detect : ∀ H : I → J → K → 𝕜,
      (∀ t i, ∑ j, ∑ k, (y t j*z t k)*H i j k=0) →
      (∀ t j, ∑ i, ∑ k, (x t i*z t k)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x t i*y t j)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x' t i*y' t j)*H i j k=0) → H=0) :
    ∀ T : I → J → K → 𝕜,
      ∃ u : P → I → 𝕜, ∃ v : P → J → 𝕜, ∃ w : P → K → 𝕜, ∃ w' : Q → K → 𝕜, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  classical
  let C := (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K)))
  let M : Matrix (I × J × K) C 𝕜
    | (i,j,k),.inl (t,h) => if h=i then y t j*z t k else 0
    | (i,j,k),.inr (.inl (t,h)) => if h=j then x t i*z t k else 0
    | (i,j,k),.inr (.inr (.inl (t,h))) => if h=k then x t i*y t j else 0
    | (i,j,k),.inr (.inr (.inr (t,h))) => if h=k then x' t i*y' t j else 0
  have no_rel (v : I × J × K → 𝕜) (hv : M.transpose.mulVec v=0) : v=0 := by
    let H (i : I) (j : J) (k : K) := v (i,j,k)
    have read (c : C) : (∑ q : I × J × K, M q c * v q)=0 := congrFun hv c
    have zero := detect H
      (fun t i => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inl (t,i)))
      (fun t j => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inr (.inl (t,j))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inl (t,k)))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inr (t,k)))))
    funext ⟨i,j,k⟩
    exact congrFun (congrFun (congrFun zero i) j) k
  have ker : LinearMap.ker M.transpose.mulVecLin=⊥ := by
    apply bot_unique
    intro u hu
    exact (Submodule.mem_bot 𝕜).mpr (no_rel u hu)
  have size := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp ker)
  change M.transpose.rank=Module.finrank 𝕜 (I × J × K → 𝕜) at size
  rw [Matrix.rank_transpose] at size
  have onto : Function.Surjective M.mulVec := LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq size)
  intro T
  obtain ⟨p,hp⟩ := onto (fun q => T q.1 q.2.1 q.2.2)
  refine ⟨fun t i => p (.inl (t,i)),fun t j => p (.inr (.inl (t,j))),
    fun t k => p (.inr (.inr (.inl (t,k)))),fun t k => p (.inr (.inr (.inr (t,k)))),?_⟩
  intro i j k
  refine (congrFun hp (i,j,k)).symm.trans ?_
  change (∑ q : (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K))), M (i,j,k) q*p q)=_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,M,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,Finset.sum_add_distrib]
  simp only [mul_assoc,mul_comm,add_assoc]

end HigherPencil

namespace HigherPencil

/-- The pencil dimension budget is equivalent to having enough exterior
labels for the lower rectangle and the paired off-diagonal slots. -/
theorem local_pencil_budget_iff {a b m r : ℕ} (hm : 2 ≤ m) (ha : m ≤ a) (hb : m ≤ b)
    (hr : m ≤ r) :
    2*(a*b-r) ≤ m*(a+b-2) ↔
      (a-m)*(b-m)+(((b-m)+(a-m))*m+1)/2 ≤ r-m := by
  let d := a-m
  let e := b-m
  change 2*(a*b-r) ≤ m*(a+b-2) ↔ d*e+((e+d)*m+1)/2 ≤ r-m
  have sa : a=m+d := by dsimp only [d]; omega
  have sb : b=m+e := by dsimp only [e]; omega
  have arms : m*(a+b-2)+2*m=m*(a+b) := calc
    _ = m*((a+b-2)+2) := by ring
    _ = m*(a+b) := by rw [show a+b-2+2=a+b by omega]
  have count : 2*(a*b)=2*(d*e)+(e+d)*m+2*m+m*(a+b-2) := calc
    _ = 2*(d*e)+(e+d)*m+m*(a+b) := by rw [sa,sb]; ring
    _ = _ := by omega
  constructor
  · intro h
    have above : a*b ≤ r+(a*b-r) := by omega
    omega
  · intro h
    by_cases le : r ≤ a*b
    · have hsub := Nat.sub_add_cancel le
      omega
    · have hsub : a*b-r=0 := by omega
      rw [hsub]
      omega

end HigherPencil

namespace HigherPencil

/-- The marked diagonal pencil and its exterior products span the primal
tangent. The exterior labels beyond the interpolation schedule carry zero factors. -/
theorem local_pencil_blocks {m d e q : ℕ} (hm : 2 ≤ m) (room : d*e+((e+d)*m+1)/2 ≤ q) :
    let A := Fin m ⊕ Fin d
    let B := Fin m ⊕ Fin e
    ∃ x : Fin m → A → ℂ, ∃ y : Fin m → B → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
    ∃ x' : Fin q → A → ℂ, ∃ y' : Fin q → B → ℂ,
    ∀ T : A → B → Fin 2 → ℂ,
      ∃ u : Fin m → A → ℂ, ∃ v : Fin m → B → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin q → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  classical
  intro A B
  let lam (t : Fin m) : ℂ := t.val
  have inject : Function.Injective lam := fun i j h => Fin.ext (Nat.cast_injective h)
  obtain ⟨X,Y,read⟩ := CriticalLastSlice.HigherPencil.product_samples (d:=d) (e:=e) hm lam inject
  let P := (Fin d × Fin e) ⊕ Fin (((e+d)*m+1)/2)
  have enough : Fintype.card P ≤ q := by simpa [P] using room
  let put : P ⊕ Fin (q-Fintype.card P) ≃ Fin q := Fintype.equivOfCardEq (by simp; omega)
  let xp (t : Fin q) : A → ℂ := (put.symm t).elim X 0
  let yp (t : Fin q) : B → ℂ := (put.symm t).elim Y 0
  let x (t : Fin m) (i : A) : ℂ := if Sum.inl t=i then 1 else 0
  let y (t : Fin m) (j : B) : ℂ := if Sum.inl t=j then 1 else 0
  let z (t : Fin m) : Fin 2 → ℂ := ![1,lam t]
  refine ⟨x,y,z,xp,yp,augmented_span_of_annihilator x y z xp yp ?_⟩
  intro H xvar yvar zvar exterior
  let U : Matrix A B ℂ := fun i j => H i j 0
  let V : Matrix A B ℂ := fun i j => H i j 1
  have diagonal (t : Fin m) (k : Fin 2) : H (.inl t) (.inl t) k = 0 := by
    simpa [A,B,x,y,mul_ite,ite_mul] using zvar t k
  have row (t : Fin m) (j : B) : U (.inl t) j+lam t*V (.inl t) j=0 := by
    simpa [A,x,z,U,V,Fin.sum_univ_two,ite_mul,Finset.sum_add_distrib] using yvar t j
  have col (t : Fin m) (i : A) : U i (.inl t)+lam t*V i (.inl t)=0 := by
    simpa [B,y,z,U,V,Fin.sum_univ_two,ite_mul,Finset.sum_add_distrib] using xvar t i
  have sampled (p : P) (k : Fin 2) : (∑ i,∑ j, X p i*Y p j*H i j k)=0 := by
    simpa only [xp,yp,Equiv.symm_apply_apply,Sum.elim_inl] using exterior (put (.inl p)) k
  obtain ⟨hu,hv⟩ := read U V (fun t => ⟨diagonal t 0,diagonal t 1⟩) row col
    (fun p => sampled p 0) (fun p => sampled p 1)
  funext i j k
  refine Fin.cases (congrFun (congrFun hu i) j) (fun h => ?_) k
  fin_cases h
  exact congrFun (congrFun hv i) j

end HigherPencil

namespace HigherPencil

/-- In actual finite coordinates a two-slice local tensor is spanned with
m full marked variations and r−m exterior third-factor variations whenever
the pencil dimension budget holds. -/
theorem local_pencil_fin {a b m r : ℕ} (hm : 2 ≤ m) (ha : m ≤ a) (hb : m ≤ b) (hr : m ≤ r)
    (budget : 2*(a*b-r) ≤ m*(a+b-2)) :
    ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
    ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
    ∀ T : Fin a → Fin b → Fin 2 → ℂ,
      ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  let ea : Fin m ⊕ Fin (a-m) ≃ Fin a := finSumFinEquiv.trans (finCongr (by omega))
  let eb : Fin m ⊕ Fin (b-m) ≃ Fin b := finSumFinEquiv.trans (finCongr (by omega))
  have room := (local_pencil_budget_iff hm ha hb hr).mp budget
  obtain ⟨x,y,z,x',y',span⟩ := local_pencil_blocks (d:=a-m) (e:=b-m) hm room
  refine ⟨fun t i => x t (ea.symm i),fun t j => y t (eb.symm j),z,
    fun t i => x' t (ea.symm i),fun t j => y' t (eb.symm j),?_⟩
  intro T
  obtain ⟨u,v,w,w',hit⟩ := span (fun i j k => T (ea i) (eb j) k)
  refine ⟨fun t i => u t (ea.symm i),fun t j => v t (eb.symm j),w,w',?_⟩
  intro i j k
  simpa only [Equiv.apply_symm_apply] using hit (ea.symm i) (eb.symm j) k

end HigherPencil

namespace CriticalHigher

/-- A two-dimensional block on any axis suffices whenever the marked points
fit and their pencil variations provide the local parameter count. The
criterion is arithmetic in the four dimensions. -/
theorem tangent_of_pencil_screen {a b n r : ℕ}
    (screen :
      let ok (u v w : ℕ) := ∃ h m, w = 2*h ∧ h*m ≤ r ∧ 2 ≤ m ∧ m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
      ok a b n ∨ ok b n a ∨ ok a n b) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  rcases screen with ⟨h,m,rfl,slots,hm,ha,hb,hr,budget⟩ |
    ⟨h,m,rfl,slots,hm,hb,hn,hr,budget⟩ | ⟨h,m,rfl,slots,hm,ha,hn,hr,budget⟩
  · exact Blocks.many_pencil_third a b h m r slots (HigherPencil.local_pencil_fin hm ha hb hr budget)
  · exact Blocks.many_pencil_first b n h m r slots (HigherPencil.local_pencil_fin hm hb hn hr budget)
  · exact Blocks.many_pencil_second a n h m r slots (HigherPencil.local_pencil_fin hm ha hn hr budget)

/-- An integer t with 2≤t≤min(a,b) gives a perfect format whenever
ab=t(h+(a+b−2)/2) in the denominator-free form below. This includes
formats for which the block axis is the only even dimension. -/
theorem perfect_pencil_format {a b h t : ℕ} (ha : 3≤a) (hab : a≤b) (order : b≤2*h)
    (ht : 2 ≤ t) (htA : t≤a) (balance : 2*(a*b)=t*(a+b+2*h-2)) :
    Arxiv.«0805.3777».IsGenericRank [a,b,2*h] (h*t) := by
  have hp : 0<h := by omega
  have den : 0<a+b+2*h-2 := by omega
  have num : a*b*(2*h)=(a+b+2*h-2)*(h*t) := by nlinarith only [congrArg (·*h) balance]
  have count : h*t=a*b*(2*h) ⌈/⌉ (a+b+2*h-2) := by
    rw [num]
    apply le_antisymm
    · exact Nat.le_of_mul_le_mul_left ((ceilDiv_le_iff_le_mul den).mp le_rfl) den
    · exact (ceilDiv_le_iff_le_mul den).mpr le_rfl
  have hr : t ≤ h*t := by
    simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ h from hp)
  have identity : 2*(a*b)=t*(a+b-2)+2*(h*t) := by
    rw [balance,show a+b+2*h-2=(a+b-2)+2*h by omega]
    ring
  have small : h*t≤a*b := by omega
  have budget : 2*(a*b-h*t)≤t*(a+b-2) := by omega
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha hab order count
  apply tangent_of_pencil_screen
  exact Or.inl ⟨h,t,rfl,le_rfl,ht,htA,htA.trans hab,hr,budget⟩

/-- Even the two unsplit axes may both be odd. Taking three marks per
pencil gives unbounded first dimensions in this rectangular family. -/
theorem odd_sides_three_marks (s t : ℕ) (ordered : 2*s+5 ≤ 6*t+3) :
    let h := (4*s+7)*t+s+2
    Arxiv.«0805.3777».IsGenericRank [2*s+5,6*t+3,2*h] (3*h) := by
  intro h
  have positive : 6*t+3 ≤ 2*h := by dsimp [h]; nlinarith
  have den : (2*s+5)+(6*t+3)+2*h-2=(2*s+5)+(6*t+3)+2*((4*s+7)*t+s+1) := by dsimp [h]; omega
  have balance : 2*((2*s+5)*(6*t+3))=3*((2*s+5)+(6*t+3)+2*h-2) := by rw [den]; ring
  simpa only [Nat.mul_comm h 3] using
    (perfect_pencil_format (a:=2*s+5) (b:=6*t+3) (h:=h) (t:=3) (by omega) ordered positive
      (by decide) (by omega) balance)

/-- For equal sides a=3(s+2), three marks in each pencil give rank 3h
at third dimension 2h, where h=a(s+1)+1. On this family the normal-space
dimension (a−1)²+1−3h is a−1, and tends to infinity. -/
theorem square_three_marks (s : ℕ) :
    let a := 3*(s+2)
    let h := a*(s+1)+1
    Arxiv.«0805.3777».IsGenericRank [a,a,2*h] (3*h) ∧ (a-1)*(a-1)+1-3*h=a-1 := by
  intro a h
  have positive : a ≤ 2*h := by dsimp [a,h]; nlinarith
  have den : a+a+2*h-2=a+a+2*(a*(s+1)) := by dsimp [h]; omega
  have balance : 2*(a*a)=3*(a+a+2*h-2) := by rw [den]; dsimp [a]; ring
  have pred : a-1=3*s+5 := by dsimp [a]; omega
  have dimension : (3*s+5)*(3*s+5)+1=3*h+(3*s+5) := by dsimp [h,a]; ring
  refine ⟨?_,by rw [pred]; omega⟩
  simpa only [Nat.mul_comm h 3] using
    (perfect_pencil_format (a:=a) (b:=a) (h:=h) (t:=3) (by dsimp [a]; omega) le_rfl
      positive (by decide) (by dsimp [a]; omega) balance)

end CriticalHigher

namespace CriticalThreeQuotient

/-- The two point equations determine a three-slice normal at each ordered
pair of distinct samples. Its remaining freedom is one scalar per pair. -/
theorem normal_entries {K I : Type*} [Field K] (l m : I → K)
    (distinct : Function.Injective l) (A B C : I → I → K)
    (diag : ∀ s, A s s = 0 ∧ B s s = 0 ∧ C s s = 0)
    (row : ∀ s t, A s t + l s*B s t + m s*C s t = 0)
    (col : ∀ s t, A s t + l t*B s t + m t*C s t = 0) :
    ∃ E : I → I → K, ∀ s t,
      A s t = (l t*m s - l s*m t)*E s t ∧
      B s t = (m t - m s)*E s t ∧ C s t = (l s - l t)*E s t := by
  let E (s t : I) := C s t / (l s - l t)
  refine ⟨E, fun s t => ?_⟩
  by_cases eq : s=t
  · subst t
    simp [diag s]
  have gap : l s - l t ≠ 0 := sub_ne_zero.mpr (distinct.ne eq)
  have hC : C s t = (l s-l t)*E s t := by dsimp [E]; field_simp
  have hB : B s t = (m t-m s)*E s t := by
    apply (mul_left_cancel₀ gap)
    linear_combination (row s t) - (col s t) - (m s-m t)*hC
  exact ⟨by linear_combination (row s t) - l s*hB - m s*hC,hB,hC⟩

/-- Injectivity modulo diagonal matrices of the two compressed diagonal
commutators kills the full normal. The third slice is then forced entrywise. -/
theorem normal_zero_of_commutators {K I U V : Type*} [Field K] [Fintype I]
    (l m : I → K) (distinct : Function.Injective l) (P : U → I → K) (Q : V → I → K)
    (exactPair : ∀ E : I → I → K,
      (∀ u t, ∑ s, P u s*((l s-l t)*E s t) = 0) →
      (∀ u t, ∑ s, P u s*((m s-m t)*E s t) = 0) →
      (∀ v s, ∑ t, ((l s-l t)*E s t)*Q v t = 0) →
      (∀ v s, ∑ t, ((m s-m t)*E s t)*Q v t = 0) →
      ∀ s t, s≠t → E s t=0)
    (A B C : I → I → K)
    (diag : ∀ s, A s s = 0 ∧ B s s = 0 ∧ C s s = 0)
    (row : ∀ s t, A s t + l s*B s t + m s*C s t = 0)
    (col : ∀ s t, A s t + l t*B s t + m t*C s t = 0)
    (leftB : ∀ u t, ∑ s, P u s*B s t = 0)
    (leftC : ∀ u t, ∑ s, P u s*C s t = 0)
    (rightB : ∀ v s, ∑ t, B s t*Q v t = 0)
    (rightC : ∀ v s, ∑ t, C s t*Q v t = 0) :
    ∀ s t, A s t=0 ∧ B s t=0 ∧ C s t=0 := by
  obtain ⟨E,entries⟩ := normal_entries l m distinct A B C diag row col
  have eC (s t) := (entries s t).2.2
  have eB (s t) : (m s-m t)*E s t = -B s t := by
    rw [(entries s t).2.1]
    ring
  have zero := exactPair E
    (fun u t => by simpa only [← eC] using leftC u t)
    (fun u t => by simp only [eB,mul_neg,Finset.sum_neg_distrib,leftB,neg_zero])
    (fun v s => by simpa only [← eC] using rightC v s)
    (fun v s => by simp only [eB,neg_mul,Finset.sum_neg_distrib,rightB,neg_zero])
  intro s t
  by_cases eq : s=t
  · subst t
    exact diag s
  · simpa only [zero s t eq,mul_zero] using entries s t

/-- A three-slice CP tangent spans if the two diagonal commutators have no
off-diagonal common kernel after compression by relations of the two frames. -/
theorem tangent_of_commutators {K U V : Type*} [Field K] {b n r : ℕ}
    (l m : Fin r → K) (distinct : Function.Injective l)
    (Y : Matrix (Fin r) (Fin b) K) (Z : Matrix (Fin r) (Fin n) K)
    (P : Matrix U (Fin r) K) (Q : Matrix V (Fin r) K)
    (pY : P * Y = 0) (qZ : Q * Z = 0)
    (embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) K => Y * N * Z.transpose))
    (exactPair : ∀ E : Fin r → Fin r → K,
      (∀ u t, ∑ s, P u s*((l s-l t)*E s t) = 0) →
      (∀ u t, ∑ s, P u s*((m s-m t)*E s t) = 0) →
      (∀ v s, ∑ t, ((l s-l t)*E s t)*Q v t = 0) →
      (∀ v s, ∑ t, ((m s-m t)*E s t)*Q v t = 0) →
      ∀ s t, s≠t → E s t=0) :
    let x (s : Fin r) : Fin 3 → K := ![1,l s,m s]
    ∀ T : Fin 3 → Fin b → Fin n → K, ∃ u : Fin r → Fin 3 → K,
      ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin n → K, ∀ i j k,
        T i j k=∑ t, (u t i*(Y t j*Z t k) + x t i*(v t j*Z t k) + x t i*(Y t j*w t k)) := by
  classical
  dsimp only
  let x (s : Fin r) : Fin 3 → K := ![1,l s,m s]
  let I := Fin r × (Fin 3 ⊕ (Fin b ⊕ Fin n))
  let M : Matrix ((Fin 3 × Fin b) × Fin n) I K := fun t s =>
    s.2.elim (fun i => if i=t.1.1 then Y s.1 t.1.2 * Z s.1 t.2 else 0)
      (Sum.elim (fun j => if j=t.1.2 then x s.1 t.1.1 * Z s.1 t.2 else 0)
        (fun k => if k=t.2 then x s.1 t.1.1 * Y s.1 t.1.2 else 0))
  have noRelation (H : (Fin 3 × Fin b) × Fin n → K) (relation : M.transpose.mulVec H=0) : H=0 := by
    obtain ⟨outer,diag,col⟩ := (LastSliceDual.transpose_kernel_iff x Y Z M (by intros; rfl) H).mp relation
    let N (i : Fin 3) : Matrix (Fin b) (Fin n) K := fun j k => H ((i,j),k)
    let S (i : Fin 3) := Y * N i * Z.transpose
    have value (i : Fin 3) (s t : Fin r) : S i s t = ∑ j, Y s j*(∑ k, Z t k*H ((i,j),k)) := by
      change (∑ k, (∑ j, Y s j * H ((i,j),k)) * Z t k) = _
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have rowEq (s t : Fin r) : ∑ i, x s i * S i s t = 0 := by
      calc
        _ = ∑ k, Z t k * (∑ ij : Fin 3 × Fin b, (x s ij.1*Y s ij.2)*H (ij,k)) := by
          simp only [value,Fintype.sum_prod_type,Finset.mul_sum]
          calc
            _ = ∑ i, ∑ k, ∑ j, x s i*(Y s j*(Z t k*H ((i,j),k))) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
            _ = _ := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k _
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = 0 := by simp [outer]
    have colEq (s t : Fin r) : ∑ i, x t i * S i s t = 0 := by
      calc
        _ = ∑ j, Y s j * (∑ i, x t i*(∑ k, Z t k*H ((i,j),k))) := by
          simp only [value,Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 0 := by simp [col]
    have leftZero (i : Fin 3) (u : U) (t : Fin r) : ∑ s, P u s*S i s t=0 := by
      have e : P * S i=0 := by simp [S,← Matrix.mul_assoc,pY]
      exact congrFun (congrFun e u) t
    have rightZero (i : Fin 3) (v : V) (s : Fin r) : ∑ t, S i s t*Q v t=0 := by
      have e : S i * Q.transpose=0 := by simp [S,Matrix.mul_assoc,← Matrix.transpose_mul,qZ]
      exact congrFun (congrFun e s) v
    have vanish := normal_zero_of_commutators l m distinct P Q exactPair (S 0) (S 1) (S 2)
      (fun s => ⟨(value 0 s s).trans (diag s 0),(value 1 s s).trans (diag s 1),
        (value 2 s s).trans (diag s 2)⟩)
      (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using rowEq s t)
      (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using colEq s t)
      (leftZero 1) (leftZero 2) (rightZero 1) (rightZero 2)
    have allZero (i : Fin 3) : N i=0 := by
      apply embed
      simp only [Matrix.mul_zero,Matrix.zero_mul]
      ext s t
      fin_cases i
      · exact (vanish s t).1
      · exact (vanish s t).2.1
      · exact (vanish s t).2.2
    funext ⟨⟨i,j⟩,k⟩
    exact congrFun (congrFun (allZero i) j) k
  have surj : Function.Surjective M.mulVec := by
    have hk : LinearMap.ker M.transpose.mulVecLin=⊥ := by
      apply bot_unique
      exact fun t h => (Submodule.mem_bot K).mpr (noRelation t h)
    have hr := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk)
    change M.transpose.rank=Module.finrank K (((Fin 3 × Fin b) × Fin n) → K) at hr
    rw [Matrix.rank_transpose] at hr
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hr)
  intro T
  obtain ⟨p,hp⟩ := surj fun q => T q.1.1 q.1.2 q.2
  refine ⟨fun t i => p (t,.inl i),fun t j => p (t,.inr (.inl j)),fun t k => p (t,.inr (.inr k)),?_⟩
  intro i j k
  refine (congrFun hp ((i,j),k)).symm.trans ?_
  change (∑ v : I, M ((i,j),k) v*p v)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [M,ite_mul,Finset.sum_ite_eq']
  ring

/-- When all three factors use characters, the two compressed commutators
are injective modulo the diagonal as soon as every frequency graph is connected.
The hypotheses state connectivity as propagation of values along its edges. -/
theorem commutators_of_frequency_graphs {G K I U V : Type*} [AddCommGroup G] [Field K] [Fintype I]
    (χ : G → I → K) (law : ∀ a b t, χ (a+b) t=χ a t*χ b t)
    (fourier : Function.Injective (fun N : I → I → K => fun i j : G =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)))
    (one d : G) (distinct : Function.Injective (χ one)) (P : U → G) (Q : V → G)
    (connected : ∀ k : G, ∀ f : G → K,
      (∀ u, f (P u+one)=f (P u) ∧ f (P u+d)=f (P u)) →
      (∀ v, f (k-Q v-one)=f (k-Q v) ∧ f (k-Q v-d)=f (k-Q v)) →
      ∀ i j, f i=f j)
    (E : I → I → K)
    (leftOne : ∀ u t, ∑ s, χ (P u) s*((χ one s-χ one t)*E s t) = 0)
    (leftD : ∀ u t, ∑ s, χ (P u) s*((χ d s-χ d t)*E s t) = 0)
    (rightOne : ∀ v s, ∑ t, ((χ one s-χ one t)*E s t)*χ (Q v) t = 0)
    (rightD : ∀ v s, ∑ t, ((χ d s-χ d t)*E s t)*χ (Q v) t = 0) :
    ∀ s t, s≠t → E s t=0 := by
  let M (i j : G) := ∑ s, ∑ t, χ i s*(E s t*χ j t)
  let C (c i j : G) := ∑ s, ∑ t, χ i s*(((χ c s-χ c t)*E s t)*χ j t)
  have shift (c i j : G) : M (i+c) j-M i (j+c)=C c i j := by
    simp only [M,C,law,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have leftEdge (c : G) (left : ∀ u t, ∑ s, χ (P u) s*((χ c s-χ c t)*E s t)=0)
      (u : U) (j : G) : M (P u+c) j=M (P u) (j+c) := by
    apply sub_eq_zero.mp
    rw [shift]
    change (∑ s, ∑ t, χ (P u) s*(((χ c s-χ c t)*E s t)*χ j t))=0
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, (∑ s, χ (P u) s*((χ c s-χ c t)*E s t)) * χ j t := by
        simp only [Finset.sum_mul,mul_assoc]
      _ = 0 := by simp [left]
  have rightEdge (c : G) (right : ∀ v s, ∑ t, ((χ c s-χ c t)*E s t)*χ (Q v) t=0)
      (v : V) (i : G) : M (i+c) (Q v)=M i (Q v+c) := by
    apply sub_eq_zero.mp
    rw [shift]
    change (∑ s, ∑ t, χ i s*(((χ c s-χ c t)*E s t)*χ (Q v) t))=0
    simp only [← Finset.mul_sum,right,mul_zero,Finset.sum_const_zero]
  have same (k i j : G) : M i (k-i)=M j (k-j) := by
    apply connected k (fun u => M u (k-u))
    · intro u
      have edge (c : G) (hyp : ∀ z, M (P u+c) z=M (P u) (z+c)) :
          M (P u+c) (k-(P u+c))=M (P u) (k-P u) := by
        rw [hyp,show k-(P u+c)+c=k-P u by abel]
      exact ⟨edge one (leftEdge one leftOne u),edge d (leftEdge d leftD u)⟩
    · intro v
      have edge (c : G) (hyp : ∀ z, M (z+c) (Q v)=M z (Q v+c)) :
          M (k-Q v-c) (k-(k-Q v-c))=M (k-Q v) (k-(k-Q v)) := by
        rw [show k-(k-Q v-c)=Q v+c by abel,show k-(k-Q v)=Q v by abel,← hyp,
          show k-Q v-c+c=k-Q v by abel]
      exact ⟨edge one (rightEdge one rightOne v),edge d (rightEdge d rightD v)⟩
  have zero (i j : G) : C one i j=0 := by
    rw [← shift,sub_eq_zero]
    have h := same (i+j+one) (i+one) i
    rwa [show i+j+one-(i+one)=j by abel,show i+j+one-i=j+one by abel] at h
  have annihilated : (fun s t => (χ one s-χ one t)*E s t) = (0 : I → I → K) := by
    apply fourier
    funext i j
    simpa only [Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero] using zero i j
  intro s t ne
  have h := congrFun (congrFun annihilated s) t
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

/-- Connected frequency graphs give a complex CP tangent at the literal
character factors, with the omitted Fourier modes as frame relations. -/
theorem tangent_of_cyclic_graphs {r b n : ℕ} [NeZero r] (d : ZMod r)
    (P Q : Finset (ZMod r)) (Y : Fin b ↪ ZMod r) (Z : Fin n ↪ ZMod r)
    (avoidY : ∀ j, Y j ∉ P) (avoidZ : ∀ k, Z k ∉ Q)
    (connected : ∀ k : ZMod r, ∀ f : ZMod r → ℂ,
      (∀ u ∈ P, f (u+1)=f u ∧ f (u+d)=f u) →
      (∀ v ∈ Q, f (k-v-1)=f (k-v) ∧ f (k-v-d)=f (k-v)) →
      ∀ i j, f i=f j) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let e := (ZMod.finEquiv r).toEquiv
  let χ (i : ZMod r) (s : Fin r) : ℂ := ZMod.stdAddChar (e s*i)
  have law (a b : ZMod r) (t : Fin r) : χ (a+b) t=χ a t*χ b t := by
    simp only [χ,mul_add,AddChar.map_add_eq_mul]
  have injective : Function.Injective (χ 1) := by
    simpa only [χ,mul_one,Function.comp_def] using ZMod.injective_stdAddChar.comp e.injective
  have orth (i j : ZMod r) : ∑ s, χ i s*χ (-j) s = if i=j then (r:ℂ) else 0 := by
    calc
      _ = ∑ s : Fin r, ZMod.stdAddChar (e s*(i-j)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← law,← sub_eq_add_neg]
      _ = ∑ t : ZMod r, ZMod.stdAddChar (t*(i-j)) := e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (t*(i-j)))
      _ = _ := by
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _),ZMod.card]
        by_cases h : i=j <;> simp [h,sub_eq_zero]
  have separates (a b : Fin r → ℂ) (test : ∀ i : ZMod r, ∑ s, χ i s*a s=∑ s, χ i s*b s) : a=b := by
    have eq : (fun j => a (e.symm j))=(fun j => b (e.symm j)) := by
      apply ZMod.dft.injective
      funext i
      rw [ZMod.dft_apply,ZMod.dft_apply]
      simp only [smul_eq_mul]
      rw [← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*a (e.symm t)),
        ← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*b (e.symm t))]
      simpa only [e.symm_apply_apply,χ,mul_neg] using test (-i)
    funext s
    simpa only [e.symm_apply_apply] using congrFun eq (e s)
  have fourier : Function.Injective (fun N : Fin r → Fin r → ℂ => fun i j : ZMod r =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)) := by
    intro A B he
    have each (j : ZMod r) : (fun s => ∑ t, A s t*χ j t)=(fun s => ∑ t, B s t*χ j t) := by
      apply separates
      intro i
      simpa only [Finset.mul_sum] using congrFun (congrFun he i) j
    funext s
    apply separates
    intro j
    simpa only [mul_comm (χ j _)] using congrFun (each j) s
  let frame {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin r) (Fin m) ℂ := fun s j => χ (-(H j)) s
  let dual {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin m) (Fin r) ℂ := fun j s => χ (H j) s / r
  have frameId {m : ℕ} (H : Fin m ↪ ZMod r) : dual H * frame H=1 := by
    ext i j
    change (∑ s, (χ (H i) s/r)*χ (-(H j)) s)=_
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,orth]
    by_cases h : i=j
    · subst j
      simp [NeZero.ne r]
    · simp [h,H.injective.ne h]
  have embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) ℂ => frame Y*N*(frame Z).transpose) := by
    intro A B eq
    have extract (N : Matrix (Fin b) (Fin n) ℂ) :
        (dual Y)*(frame Y*N*(frame Z).transpose)*(dual Z).transpose=N := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,frameId,Matrix.one_mul,Matrix.mul_assoc,
        ← Matrix.transpose_mul,frameId,Matrix.transpose_one,Matrix.mul_one]
    exact (extract A).symm.trans ((congrArg (fun N => (dual Y)*N*(dual Z).transpose) eq).trans (extract B))
  have annihilate {m : ℕ} (A : Finset (ZMod r)) (H : Fin m ↪ ZMod r) (avoid : ∀ j, H j∉A) :
      (Matrix.of (fun (i : A) (t : Fin r) => χ i.val t))*frame H=0 := by
    ext i j
    change (∑ s, χ i.val s*χ (-(H j)) s)=0
    have ne : i.val≠H j := fun h => avoid j (h ▸ i.property)
    rw [orth,if_neg ne]
  refine ⟨fun s => ![1,χ 1 s,χ d s],frame Y,frame Z,?_⟩
  apply tangent_of_commutators (χ 1) (χ d) injective (frame Y) (frame Z) _ _
    (annihilate P Y avoidY) (annihilate Q Z avoidZ) embed
  exact commutators_of_frequency_graphs χ law fourier 1 d injective Subtype.val Subtype.val
    (fun k f left right => connected k f (fun i hi => left ⟨i,hi⟩) (fun i hi => right ⟨i,hi⟩))

/-- The dimensions complementary to the two relation sets determine frames
from the unused frequencies. -/
theorem tangent_of_graph_cards {r b n : ℕ} [NeZero r] (d : ZMod r)
    (P Q : Finset (ZMod r)) (pCard : P.card+b=r) (qCard : Q.card+n=r)
    (connected : ∀ k : ZMod r, ∀ f : ZMod r → ℂ,
      (∀ u ∈ P, f (u+1)=f u ∧ f (u+d)=f u) →
      (∀ v ∈ Q, f (k-v-1)=f (k-v) ∧ f (k-v-d)=f (k-v)) →
      ∀ i j, f i=f j) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  have choose {m : ℕ} (F : Finset (ZMod r)) (count : F.card+m=r) :
      ∃ J : Fin m ↪ ZMod r, ∀ i, J i∉F := by
    have size : Fintype.card (Fin m)=Fintype.card (↥(Fᶜ) : Type) := by
      rw [Fintype.card_fin,Fintype.card_coe,Finset.card_compl,ZMod.card]
      omega
    let e := Fintype.equivOfCardEq size
    exact ⟨e.toEmbedding.trans (Function.Embedding.subtype _),
      fun i => Finset.mem_compl.mp (e i).property⟩
  obtain ⟨Y,hy⟩ := choose P pCard
  obtain ⟨Z,hz⟩ := choose Q qCard
  exact tangent_of_cyclic_graphs d P Q Y Z hy hz connected

/-- ceil((r−W)/d) is the least number of right centers making the
closing gap at most W. All its sampled centers are distinct modulo r. -/
theorem least_chain {r W d : ℕ} (width : W≤r) (hd : 0<d) (step : d≤W) :
    let q := (r-W) ⌈/⌉ d
    q*d<r ∧ r≤q*d+W ∧ ∀ t : ℕ,r≤t*d+W ↔ q≤t := by
  intro q
  have least (t : ℕ) : r≤t*d+W ↔ q≤t := by
    change r≤t*d+W ↔ (r-W) ⌈/⌉ d≤t
    rw [ceilDiv_le_iff_le_mul hd,Nat.mul_comm d t]
    omega
  have upper : q*d≤(r-W+d-1) := by
    change ((r-W) ⌈/⌉ d)*d≤r-W+d-1
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_mul_le_self _ _
  exact ⟨by omega,(least q).mpr le_rfl,least⟩

/-- Within a block of width 2L+1 the L centers have steps +1 and +(L+1).
These edges force the value on every position to equal the block's first value. -/
theorem block_constant {r L : ℕ} {C : Type*} (f : ZMod r → C) (z : ZMod r)
    (edge : ∀ i : Fin L, f (z+(i.val:ZMod r)+1)=f (z+i.val) ∧
      f (z+(i.val:ZMod r)+((L+1:ℕ):ZMod r))=f (z+i.val)) :
    ∀ o : ℕ,o<2*L+1 → f (z+(o:ZMod r))=f z := by
  have first (t : ℕ) (ht : t≤L) : f (z+(t:ZMod r))=f z := by
    induction t with
    | zero => simp
    | succ t ih =>
      simpa only [Nat.cast_succ,← add_assoc] using
        ((edge ⟨t,by omega⟩).1.trans (ih (by omega)))
  intro o ho
  by_cases h : o≤L
  · exact first o h
  · let i : Fin L := ⟨o-(L+1),by omega⟩
    have eq : i.val+(L+1)=o := by dsimp [i]; omega
    have same : z+(i.val:ZMod r)+((L+1:ℕ):ZMod r)=z+(o:ZMod r) := by
      rw [add_assoc,← Nat.cast_add,eq]
    rw [← same]
    exact (edge i).2.trans (first i.val i.isLt.le)

/-- The longer block has centers 0 and 2 through L+1. Its 0 to L+1
edge joins the two unit chains; its long edges cover the remaining positions. -/
theorem long_block_constant {L : ℕ} (hL : 2≤L) {C : Type*} (f : ℕ → C)
    (first : f 1=f 0 ∧ f (L+1)=f 0)
    (edges : ∀ t : ℕ,2≤t → t≤L+1 → f (t+1)=f t ∧ f (t+(L+1))=f t) :
    ∀ o : ℕ,o<2*L+3 → f o=f 0 := by
  have run (t : ℕ) (lo : 2≤t) (hi : t≤L+2) : f t=f 2 := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases eq : t+1=2
      · rw [eq]
      · exact ((edges t (by omega) (by omega)).1).trans (ih (by omega) (by omega))
  have two : f 2=f 0 := (run (L+1) (by omega) (by omega)).symm.trans first.2
  intro o ho
  by_cases small : o<2
  · rcases (by omega : o=0 ∨ o=1) with rfl|rfl
    · rfl
    · exact first.1
  · by_cases mid : o≤L+2
    · exact (run o (by omega) mid).trans two
    · let t := o-(L+1)
      have eq : t+(L+1)=o := by dsimp [t]; omega
      have lo : 2≤t := by dsimp [t]; omega
      have hi : t≤L+1 := by dsimp [t]; omega
      rw [← eq]
      exact ((edges t lo hi).2).trans ((run t lo (by omega)).trans two)

/-- Exactly L+1 distinct left Fourier modes are used in a long block. -/
theorem long_centers (L : ℕ) :
    ∃ centers : Fin (L+1) ↪ Fin (2*L+3),
      ∀ t : ℕ,(∃ i, (centers i).val=t) ↔ t=0 ∨ 2≤t ∧ t≤L+1 := by
  let centers (i : Fin (L+1)) : Fin (2*L+3) :=
    ⟨if i.val=0 then 0 else i.val+1,by split <;> have := i.isLt <;> omega⟩
  have inj : Function.Injective centers := by
    intro i j eq
    apply Fin.ext
    have raw := congrArg Fin.val eq
    change (if i.val=0 then 0 else i.val+1)=(if j.val=0 then 0 else j.val+1) at raw
    split_ifs at raw <;> omega
  refine ⟨⟨centers,inj⟩,?_⟩
  intro t
  constructor
  · rintro ⟨i,rfl⟩
    change (if i.val=0 then 0 else i.val+1)=0 ∨
      2≤(if i.val=0 then 0 else i.val+1) ∧ (if i.val=0 then 0 else i.val+1)≤L+1
    split_ifs <;> have := i.isLt <;> omega
  · rintro (rfl|⟨lo,hi⟩)
    · exact ⟨0,by simp [centers]⟩
    · let t' : Fin (L+1) := ⟨t-1,by omega⟩
      refine ⟨t',?_⟩
      change (if t-1=0 then 0 else t-1+1)=t
      split <;> omega

/-- The gaps between d-spaced samples, including the closing gap, are at
most W. Every residue u is thus t*d plus an offset in [0,W), for t≤q. -/
theorem chain_hits {r W d q u : ℕ} (hd : 0<d) (step : d≤W) (closing : r≤q*d+W)
    (hr : u<r) : ∃ t≤q, ∃ o<W,t*d+o=u := by
  by_cases h : u<q*d
  · refine ⟨u/d,((Nat.div_lt_iff_lt_mul hd).mpr h).le,u%d,(Nat.mod_lt u hd).trans_le step,?_⟩
    rw [Nat.mul_comm,Nat.div_add_mod]
  · exact ⟨q,le_rfl,u-q*d,by omega,by omega⟩

/-- A chain intersects every constant patch that contains at least W
consecutive residues from its start. Patch lengths may vary. -/
theorem patches_of_chain {r W d q : ℕ} [NeZero r] {C : Type*} (f : ZMod r → C) (k : ZMod r)
    (hd : 0<d) (step : d≤W) (closing : r≤q*d+W)
    (patch : ∀ x,∃ B : ZMod r, f x=f B ∧ ∀ o : ℕ,o<W → f (B+(o:ZMod r))=f B)
    (edge : ∀ t : Fin q,f (k-((t.val*d:ℕ):ZMod r)-(d:ZMod r))=f (k-((t.val*d:ℕ):ZMod r))) :
    ∀ i j,f i=f j := by
  have chain (t : ℕ) (ht : t≤q) : f (k-((t*d:ℕ):ZMod r))=f k := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul,Nat.cast_add,← sub_sub]
      exact (edge ⟨t,by omega⟩).trans (ih (by omega))
  have all (x : ZMod r) : f x=f k := by
    obtain ⟨B,hx,flat⟩ := patch x
    obtain ⟨t,ht,o,ho,dist⟩ := chain_hits hd step closing (k-B).val_lt
    have eq : ((t*d:ℕ):ZMod r)+(o:ZMod r)=k-B := by
      rw [← Nat.cast_add,dist,ZMod.natCast_zmod_val]
    have hit : B+(o:ZMod r)=k-((t*d:ℕ):ZMod r) := by linear_combination eq
    exact hx.trans ((flat _ ho).symm.trans ((congrArg f hit).trans (chain _ ht)))
  exact fun i j => (all i).trans (all j).symm

/-- Use s initial blocks of width 2L+3 and h−s final blocks of width 2L+1.
Their Fourier centers and one chain of q right modes connect every frequency
graph whenever the chain and its closing gap fit the shorter block width. -/
theorem mixed_graphs_of_q (h L s q : ℕ) (hh : 0<h) (hL : 2≤L) (hs : s≤h)
    (short : q*(L+1)≤h*(2*L+1)+2*s)
    (cover : h*(2*L+1)+2*s≤q*(L+1)+(2*L+1)) :
    let r := h*(2*L+1)+2*s
    ∃ P Q : Finset (ZMod r), P.card=h*L+s ∧ Q.card=q ∧
      ∀ k : ZMod r,∀ f : ZMod r → ℂ,
        (∀ u∈P,f (u+1)=f u ∧ f (u+((L+1:ℕ):ZMod r))=f u) →
        (∀ v∈Q,f (k-v-1)=f (k-v) ∧ f (k-v-((L+1:ℕ):ZMod r))=f (k-v)) →
        ∀ i j,f i=f j := by
  classical
  intro r
  let W := 2*L+1
  let U := 2*L+3
  let d := L+1
  have hw : 0<W := by dsimp [W]; omega
  have hd : 0<d := by dsimp [d]; omega
  have hr : 0<r := Nat.add_pos_left (Nat.mul_pos hh hw) _
  let : NeZero r := ⟨hr.ne'⟩
  have widths : s*U+(h-s)*W=r := by
    have split := congrArg (·*W) (Nat.sub_add_cancel hs)
    change (h-s+s)*W=h*W at split
    change s*U+(h-s)*W=h*W+2*s
    rw [show U=W+2 by rfl]
    nlinarith only [split]
  let G := (Fin s × Fin U) ⊕ (Fin (h-s) × Fin W)
  let M := (Fin s × Fin (L+1)) ⊕ (Fin (h-s) × Fin L)
  let slot : G ≃ Fin r :=
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr widths)
  let residue : Fin r ↪ ZMod r :=
    { toFun := fun i => (i.val:ZMod r)
      inj' := by
        intro i j eq
        apply Fin.ext
        have raw := congrArg ZMod.val eq
        simpa only [ZMod.val_natCast_of_lt i.isLt,ZMod.val_natCast_of_lt j.isLt] using raw }
  let enc : G ↪ ZMod r := slot.toEmbedding.trans residue
  have onto : Function.Surjective enc := by
    intro x
    obtain ⟨p,hp⟩ := slot.surjective ⟨x.val,x.val_lt⟩
    refine ⟨p,?_⟩
    change ((slot p).val : ZMod r)=x
    rw [hp,ZMod.natCast_zmod_val]
  let lb (j : Fin s) : ZMod r := ((j.val*U:ℕ):ZMod r)
  let sb (j : Fin (h-s)) : ZMod r := ((s*U+j.val*W:ℕ):ZMod r)
  have leval (j : Fin s) (i : Fin U) : enc (.inl (j,i))=lb j+(i.val:ZMod r) := by
    change ((i.val+U*j.val:ℕ):ZMod r)=((j.val*U:ℕ):ZMod r)+i.val
    push_cast
    ring
  have seval (j : Fin (h-s)) (i : Fin W) : enc (.inr (j,i))=sb j+(i.val:ZMod r) := by
    change ((s*U+(i.val+W*j.val):ℕ):ZMod r)=((s*U+j.val*W:ℕ):ZMod r)+i.val
    push_cast
    ring
  obtain ⟨lc,lcRange⟩ := long_centers L
  let sc : Fin L ↪ Fin W := Fin.castLEEmb (by dsimp [W]; omega)
  let pick : M ↪ G := ((Function.Embedding.refl (Fin s)).prodMap lc).sumMap
    ((Function.Embedding.refl (Fin (h-s))).prodMap sc)
  let pe := pick.trans enc
  let P := Finset.univ.map pe
  have lmem (j : Fin s) (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤L+1) : lb j+(i:ZMod r)∈P := by
    obtain ⟨t,ht⟩ := (lcRange i).mpr hi
    have hm : pe (.inl (j,t))∈P := Finset.mem_map.mpr ⟨.inl (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inl (j,lc t))∈P at hm
    simpa only [leval,ht] using hm
  have smem (j : Fin (h-s)) (i : Fin L) : sb j+(i.val:ZMod r)∈P := by
    have hm : pe (.inr (j,i))∈P := Finset.mem_map.mpr ⟨.inr (j,i),Finset.mem_univ _,rfl⟩
    change enc (.inr (j,sc i))∈P at hm
    simpa only [seval,show (sc i).val=i.val from rfl] using hm
  have qlimit (t : Fin q) : t.val*d<r := (Nat.mul_lt_mul_of_pos_right t.isLt hd).trans_le short
  let qe : Fin q ↪ ZMod r :=
    { toFun := fun t => ((t.val*d:ℕ):ZMod r)
      inj' := by
        intro t u eq
        have raw := congrArg ZMod.val eq
        change (((t.val*d:ℕ):ZMod r)).val=(((u.val*d:ℕ):ZMod r)).val at raw
        rw [ZMod.val_natCast_of_lt (qlimit t),ZMod.val_natCast_of_lt (qlimit u)] at raw
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd raw) }
  let Q := Finset.univ.map qe
  have countP : P.card=h*L+s := by
    simp only [P,Finset.card_map,Finset.card_univ,M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    have split := congrArg (·*L) (Nat.sub_add_cancel hs)
    change (h-s+s)*L=h*L at split
    nlinarith only [split]
  refine ⟨P,Q,countP,by simp [Q],?_⟩
  intro k f left right
  have lf (j : Fin s) (o : ℕ) (ho : o<U) : f (lb j+(o:ZMod r))=f (lb j) := by
    let g (t : ℕ) := f (lb j+(t:ZMod r))
    have eq (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤L+1) :
        g (i+1)=g i ∧ g (i+(L+1))=g i := by
      have a := left (lb j+(i:ZMod r)) (lmem j i hi)
      simpa only [g,Nat.cast_add,Nat.cast_one,← add_assoc] using a
    have a := eq 0 (Or.inl rfl)
    have all := long_block_constant hL g (by simpa only [zero_add] using a)
      (fun t hlo hhi => eq t (.inr ⟨hlo,hhi⟩)) o ho
    simpa only [g,Nat.cast_zero,add_zero] using all
  have sf (j : Fin (h-s)) := block_constant f (sb j) (L:=L) (fun i => left _ (smem j i))
  apply patches_of_chain f k hd (by dsimp [d,W]; omega : d≤W) cover
  · intro x
    obtain ⟨⟨j,i⟩|⟨j,i⟩,rfl⟩ := onto x
    · exact ⟨lb j,(congrArg f (leval j i)).trans (lf j _ i.isLt),
        fun o ho => lf j o (by dsimp [W] at ho; dsimp [U]; omega)⟩
    · exact ⟨sb j,(congrArg f (seval j i)).trans (sf j _ i.isLt),sf j⟩
  · intro t
    exact (right (qe t) (Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩)).2

/-- The short-chain test after splitting the middle dimension into long and
short blocks. The remainder s can be any integer between 0 and h. -/
theorem mixed_tangent_of_capacity (h L s N : ℕ) (hh : 0<h) (hL : 2≤L) (hs : s≤h) :
    let W := 2*L+1
    let r := h*W+2*s
    let b := h*(L+1)+s
    N≤r → r≤(r-N)*(L+1)+W →
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  intro W r b enough cap
  have hw : 0<W := by dsimp [W]; omega
  have hr : 0<r := by have := Nat.mul_pos hh hw; dsimp [r]; omega
  have : NeZero r := ⟨hr.ne'⟩
  have wle : W≤r := by
    have le : W≤h*W := by simpa only [one_mul] using Nat.mul_le_mul_right W (show 1≤h from hh)
    dsimp [r]
    omega
  let q := (r-W) ⌈/⌉ (L+1)
  have vals := least_chain wle (by omega : 0<L+1) (by dsimp [W]; omega : L+1≤W)
  have qle : q≤r-N := (vals.2.2 _).mp cap
  obtain ⟨P,Q,cardP,cardQ,connected⟩ :=
    mixed_graphs_of_q h L s q hh hL hs vals.1.le vals.2.1
  have psize : P.card+b=r := by rw [cardP]; dsimp [b,r,W]; ring
  have qsize : Q.card+(r-q)=r := by rw [cardQ]; omega
  exact CriticalHigher.project (show N≤r-q by omega)
    (tangent_of_graph_cards _ P Q psize qsize connected)

/-- The mixed-width integer screen in the registered witness coordinates.
It supplies all generic weighted normal equations after the existing transfer. -/
theorem tangent_of_remainder_capacity (b N r h : ℕ) (hh : 0<h) (width : 3*h≤b)
    (enough : N≤r) (level : r+h=2*b) (cap : r+1≤(r-N+2)*(b/h)) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  let L := b/h-1
  let s := b%h
  have u : 3≤b/h := (Nat.le_div_iff_mul_le hh).mpr width
  have hL : 2≤L := by dsimp [L]; omega
  have hs : s<h := Nat.mod_lt _ hh
  have quotient : L+1=b/h := by dsimp [L]; omega
  have bsize : h*(L+1)+s=b := by rw [quotient]; exact Nat.div_add_mod b h
  have rsize : h*(2*L+1)+2*s=r := by nlinarith only [level,bsize]
  have capacity : r≤(r-N)*(L+1)+(2*L+1) := by
    rw [← quotient] at cap
    nlinarith only [cap]
  have witness := mixed_tangent_of_capacity h L s N hh hL hs.le
    (by rw [rsize]; exact enough) (by rw [rsize]; exact capacity)
  rwa [bsize,rsize] at witness

/-- The exact generic rank in any strict three-slice rectangle passing a
single integer test, with h=2b−r and the Euclidean quotient b/h. -/
theorem rank_of_remainder_capacity (b N r h : ℕ) (hh : 0<h) (hb : 3≤b) (width : 3*h≤b)
    (ordered : b≤N) (enough : N≤r) (level : r+h=2*b)
    (cap : r+1≤(r-N+2)*(b/h)) (count : 3*b*N ⌈/⌉ (b+N+1)=r) :
    Arxiv.«0805.3777».IsGenericRank [3,b,N] r  := by
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb ordered _
    (tangent_of_remainder_capacity b N r h hh width enough level cap)
  rw [show 3+b+N-2=b+N+1 by omega]
  exact count.symm

private theorem count_of_small_slack {p D r s : ℕ} (hd : 0<D)
    (slack : r*D=p+s) (small : s<D) : p ⌈/⌉ D=r := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr (by nlinarith only [slack])) _
  by_contra! below
  have cover := (ceilDiv_le_iff_le_mul (a:=D) (b:=p) hd).mp le_rfl
  have grow := Nat.mul_le_mul_left D (show (p ⌈/⌉ D)+1≤r by omega)
  rw [Nat.mul_add,Nat.mul_one] at grow
  nlinarith only [grow,cover,slack,small]

/-- At the natural endpoint, b≥h² gives the exact expected count. One size
below, the stated linear inequality in b is necessary and sufficient. -/
theorem precise_mixed_counts (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    let r := 2*b-h
    let N := 2*b-3*h+1
    3≤b ∧ 3*h≤b ∧ b≤N ∧ N+1≤r ∧
    (3*b*N ⌈/⌉ (b+N+1)=r ↔ 3*h^2+h≤2*b+1) ∧
    3*b*(N+1) ⌈/⌉ (b+(N+1)+1)=r := by
  intro r N
  have width : 3*h≤b := by
    have prod := Nat.mul_le_mul_right h hh
    nlinarith only [prod,lower]
  have hb : 3≤b := by omega
  have idn : N+3*h=2*b+1 := by dsimp [N]; omega
  have idr : r+h=2*b := Nat.sub_add_cancel (by omega)
  have hp := congrArg (fun t : ℕ => t*h) (Nat.sub_add_cancel (by omega : 1≤h))
  have s₁ : r*(b+N+1)=3*b*N+(3*h*(h-1)+b+h) := by
    have e := congrArg (fun t : ℕ => t*(b+N+1)) idr
    have f := congrArg (fun t : ℕ => t*b) idn
    have g := congrArg (fun t : ℕ => t*h) idn
    nlinarith only [e,f,g,hp]
  have s₂ : r*(b+(N+1)+1)=3*b*(N+1)+3*h*(h-1) := by nlinarith only [s₁,idr]
  have small : 3*h*(h-1)<b+(N+1)+1 := by nlinarith only [lower,idn,hp]
  refine ⟨hb,width,by omega,by omega,⟨?_,?_⟩,count_of_small_slack (by omega) s₂ small⟩
  · intro count
    by_contra! fail
    have pred := Nat.sub_add_cancel (by omega : 1≤r)
    have next := congrArg (fun t : ℕ => t*(b+N+1)) pred
    have smaller : 3*b*N ⌈/⌉ (b+N+1)≤r-1 := (ceilDiv_le_iff_le_mul (by omega)).mpr
      (by nlinarith only [s₁,fail,next,hp,idn])
    omega
  · intro admissible
    apply count_of_small_slack (by omega) s₁
    nlinarith only [admissible,idn,hp]

/-- At the two adjacent sizes, the mixed interval test reduces respectively
to an automatic inequality and a condition on b modulo h. -/
theorem precise_mixed_capacity (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    let r := 2*b-h
    let N := 2*b-3*h+1
    r+1≤(r-N+2)*(b/h) ∧ (r+1≤(r-(N+1)+2)*(b/h) ↔ 2*(b%h)<h) := by
  intro r N
  have width := (precise_mixed_counts h b hh lower).2.1
  have d : h≤b/h := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [sq] using lower)
  have s := Nat.mod_lt b (by omega : 0<h)
  have euclid := Nat.div_add_mod b h
  have idn : N+3*h=2*b+1 := by dsimp [N]; omega
  have idr : r+h=2*b := Nat.sub_add_cancel (by omega)
  have enough : N+1≤r := by omega
  have q₁ : r-N+2=2*h+1 := by have := Nat.sub_add_cancel (by omega : N≤r); omega
  have q₂ : r-(N+1)+2=2*h := by have := Nat.sub_add_cancel enough; omega
  rw [q₁,q₂]
  have lim : b%h+1≤h := by omega
  constructor
  · nlinarith only [euclid,idr,d,lim]
  · constructor <;> intro edge <;> nlinarith only [euclid,idr,edge]

/-- For every h≥3, all middle widths in which the stated rank is the
dimension prediction have complex generic rank 2b−h at this third size. -/
theorem all_widths_generic_rank_sharp (h b : ℕ) (hh : 3≤h)
    (admissible : 3*h^2+h≤2*b+1) :
    Arxiv.«0805.3777».IsGenericRank [3,b,2*b-3*h+1] (2*b-h) := by
  have lower : h^2≤b := by nlinarith only [admissible,hh,Nat.zero_le (h^2)]
  obtain ⟨hb,width,ordered,enough,count,_⟩ := precise_mixed_counts h b hh lower
  have level := Nat.sub_add_cancel (by omega : h≤2*b)
  exact rank_of_remainder_capacity b (2*b-3*h+1) (2*b-h) h (by omega) hb width
    ordered (by omega) level (precise_mixed_capacity h b hh lower).1 (count.mpr admissible)

/-- At the next third size, b≥h² and the lower half of the residue classes
give the same complex generic rank. -/
theorem small_remainder_generic_rank_sharp (h b : ℕ) (hh : 3≤h) (lower : h^2≤b)
    (rem : 2*(b%h)<h) :
    Arxiv.«0805.3777».IsGenericRank [3,b,2*b-3*h+2] (2*b-h) := by
  obtain ⟨hb,width,ordered,enough,_,count⟩ := precise_mixed_counts h b hh lower
  have level := Nat.sub_add_cancel (by omega : h≤2*b)
  exact rank_of_remainder_capacity b (2*b-3*h+2) (2*b-h) h (by omega) hb width
    (by omega) enough level ((precise_mixed_capacity h b hh lower).2.mpr rem) count

end CriticalThreeQuotient

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R1

/-- The remaining rank-interval endpoints with first dimension three.
The three orientations of the pencil test and the cyclic frequency test
already have uniform tangent witnesses. -/
def H1 : Prop :=
  ∀ b r : ℕ, 3 ≤ b → 0<r → r+1<2*(b-1) →
    let A := 3*b
    let d := 3+b-2
    let N := r*d/(A-r)
    b+2 ≤ N → (r-1)*d/(A-(r-1))<N →
    let pencil (u v w : ℕ) := ∃ h m : ℕ, w=2*h ∧ h*m ≤ r ∧ 2 ≤ m ∧
      m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
    ¬(pencil 3 b N ∨ pencil b N 3 ∨ pencil 3 N b) →
    ¬(∃ h : ℕ, 0<h ∧ 3*h ≤ b ∧ N ≤ r ∧ r+h=2*b ∧ r+1 ≤ (r-N+2)*(b/h)) →
    let D := 2*(3*b*N)+1
    ∃ x : Fin r → Fin 3 → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin N → Fin D,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

/-- For every larger first dimension it suffices to check the single
largest admissible third dimension at ranks outside the three pencil families. -/
def H2 : Prop :=
  ∀ a b r : ℕ, 4 ≤ a → a ≤ b → 0<r → r+1<(a-1)*(b-1) →
    let A := a*b
    let d := a+b-2
    let N := r*d/(A-r)
    b+2 ≤ N → (r-1)*d/(A-(r-1))<N →
    let pencil (u v w : ℕ) := ∃ h m : ℕ, w=2*h ∧ h*m ≤ r ∧ 2 ≤ m ∧
      m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
    ¬(pencil a b N ∨ pencil b N a ∨ pencil a N b) →
    let D := 2*(a*b*N)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin N → Fin D,
      ∀ T : Fin a → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2 := by
  intro three larger
  apply CriticalHigher.higher_iff_endpoints.mpr
  intro a b r ha hab hr level A d N start present
  let pencil (u v w : ℕ) := ∃ h m : ℕ, w=2*h ∧ h*m ≤ r ∧ 2 ≤ m ∧
    m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
  by_cases screened : pencil a b N ∨ pencil b N a ∨ pencil a N b
  · exact CriticalHigher.tangent_of_pencil_screen screened
  by_cases first : a=3
  · subst a
    by_cases cycle : ∃ h : ℕ, 0<h ∧ 3*h ≤ b ∧ N ≤ r ∧ r+h=2*b ∧ r+1 ≤ (r-N+2)*(b/h)
    · obtain ⟨h,positive,width,enough,rank,cap⟩ := cycle
      exact CriticalThreeQuotient.tangent_of_remainder_capacity b N r h positive width enough rank cap
    · obtain ⟨x,y,z,span⟩ := three b r hab hr level start present screened cycle
      exact ⟨fun t i => (x t i).val,fun t j => (y t j).val,fun t k => (z t k).val,span⟩
  · obtain ⟨x,y,z,span⟩ := larger a b r (by omega) hab hr level start present screened
    exact ⟨fun t i => (x t i).val,fun t j => (y t j).val,fun t k => (z t k).val,span⟩

theorem three_of_registered
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2) : H1 := by
  intro b r hb hr level A d N start present pencil unscreened outside D
  exact CriticalReduction.bounded_of_witness
    (CriticalHigher.higher_iff_endpoints.mp higher 3 b r (by decide) hb hr level start present)

theorem larger_of_registered
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2) : H2 := by
  intro a b r ha hab hr level A d N start present pencil unscreened D
  exact CriticalReduction.bounded_of_witness
    (CriticalHigher.higher_iff_endpoints.mp higher a b r (by omega) hab hr level start present)

/-- The two finite-grid families are equivalent to the registered higher normal-space statement. -/
theorem remaining_iff_registered : H1 ∧ H2 ↔
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2 :=
  ⟨fun both => main both.1 both.2,fun h => ⟨three_of_registered h,larger_of_registered h⟩⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R1
