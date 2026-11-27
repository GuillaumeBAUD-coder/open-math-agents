import OMAReductions.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1

/-! Exterior spanning for the (n-2,n-2,n) block, as in Lickteig,
Typical tensorial rank (1985), Lemma 4.6. Split the third factor into groups
of slices. For each group the exterior consists of a two-by-two corner and
two arms. Separate determinant polynomials allow each group to be checked
at a different specialization before the tangent coefficients are assembled.

With an even number of added points the construction uses pairs of slices
and, when necessary, a single inactive slice. With an odd number it uses
active four- and three-slice blocks, at most one active pair, and inactive
four- and one-slice blocks. In each four- or three-slice block the exterior
factors of the active points are fixed. Repeating independently supported
arms extends a finite configuration to every required dimension. All finite
matrix ranks are certified by integer right inverses modulo seven and then
lifted to the complex numbers. The final count verifies that the available
inner points suffice for the simultaneous construction.
-/

namespace TensorRankExterior

open MvPolynomial

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
  choose Q hQ hgood using fun k => OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1.surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩


abbrev Param (d e s : ℕ) := Fin s × (Fin d ⊕ (Fin d ⊕ Fin e))
def Fixed {n d e s r : ℕ} (x : Param d e s → ℂ) (a b c : Fin r → Fin n → ℂ) : Prop :=
  ∀ (t : Fin r) (ht : t.val < s) (i : Fin n),
    a t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inl ⟨i.val,h⟩) else 0) ∧
    b t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inr (Sum.inl ⟨i.val,h⟩)) else 0) ∧
    c t i = (if h : i.val < e then x (⟨t.val,ht⟩, Sum.inr (Sum.inr ⟨i.val,h⟩)) else 0)

def Covers {n r : ℕ} (d e : ℕ) (a b c : Fin r → Fin n → ℂ) : Prop :=
  ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
    (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) →
      T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
        a t i * (b t j * w t k))

def Witness (n d e s r : ℕ) : Prop :=
  ∃ x : Param d e s → ℂ, ∃ a b c : Fin r → Fin n → ℂ, Fixed x a b c ∧ Covers d e a b c

end TensorRankExterior

namespace TensorRankExterior

def coreCount (n : ℕ) :=
  if n % 3 = 1 then (n - 1) * (n - 1) / 3 else (n - 2) * n / 3

lemma three_core (n : ℕ) (hn : 2 ≤ n) :
    3 * coreCount n + 2*n = n^2 + (if n % 3 = 1 then 1 else 0) :=
  OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1.three_core n hn

lemma cube_count (n : ℕ) (hn : 2 ≤ n) :
    n^3 ⌈/⌉ (3*n-2) = coreCount n + (8*n/9) + 1 :=
  OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1.cube_count n hn

/-- Write the number of added points as twice a+2, and the third dimension as
two slices for every active or inactive pencil. The dimension bound pays for
all the inner points in this specialization. -/
lemma even_pencil_budget (n p s a b : ℕ) (hn : n=2*(a+b+2)) (hp : p=2*(a+2))
    (hs : 3*s+2*n=n^2) (hr : n^3 ≤ (3*n-2)*(s+p)) :
    (a+2)*(a+2*b+1) + b*(3*a+4*b+4) ≤ s := by
  subst n p
  have hD : 3*(2*(a+b+2))-2=6*a+6*b+10 := by omega
  rw [hD] at hr
  nlinarith [congrArg (fun t : ℕ => (2*(a+b+2))*t) hs]

lemma even_pencil_parameters (n : ℕ) (hn : 5≤n) (hc : n%3≠1) (he : n%2=0)
    (hp : (n-(n-1)/9)%2=0) :
    ∃ a b : ℕ, n=2*(a+b+2) ∧ n-(n-1)/9=2*(a+2) ∧
      (b>0 → a%2=1 → 3≤a) ∧ (a+2)*(a+2*b+1) + b*(3*a+4*b+4) ≤ coreCount n := by
  let p := n-(n-1)/9
  let a := p/2 - 2
  let b := (n-p)/2
  have ha : p=2*(a+2) := by dsimp only [a,p]; omega
  have hb : n=2*(a+b+2) := by dsimp only [b,p] at *; omega
  refine ⟨a,b,hb,ha,?_,?_⟩
  · dsimp only [a,b,p]
    omega
  · apply even_pencil_budget n p _ a b hb ha
    · simpa only [if_neg hc,add_zero] using three_core n (by omega)
    · have hden : 0 < 3*n-2 := by omega
      have h := (ceilDiv_le_iff_le_mul (b := n^3) hden).mp le_rfl
      rw [cube_count n (by omega)] at h
      have hsum : coreCount n+8*n/9+1=coreCount n+p := by dsimp only [p]; omega
      rwa [hsum] at h

end TensorRankExterior


namespace TensorRankExterior

/-- In a two-slice block with two active points, the diagonal positions in
the two outer coordinates have independent coefficients. The other entries
come from an inner point or a third-factor variation in a different slice. -/
lemma active_arm {I E : Type} (T : (I ⊕ E) → Fin 2 → Fin 2 → ℂ) :
    ∃ m : (I ⊕ E) → Fin 2 → ℂ, ∃ v : I → Fin 2 → ℂ, ∃ w : E → Fin 2 → ℂ,
      ∀ i j k, T i j k = (if j=k then m i j else 0) +
        i.elim (fun q => v q j) (fun q => w q k) := by
  let flip (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0
  let v (q : I) (j : Fin 2) := T (Sum.inl q) j (flip j)
  let w (q : E) (k : Fin 2) := T (Sum.inr q) (flip k) k
  let m (q : I ⊕ E) (j : Fin 2) := T q j j - q.elim (fun t => v t j) (fun t => w t j)
  refine ⟨m,v,w,?_⟩
  intro q j k
  cases q <;> fin_cases j <;> fin_cases k <;> simp [m,v,w,flip]

lemma active_corner (T : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    ∃ u v w : Fin 2 → Fin 2 → ℂ, ∀ i j k, T i j k =
      (if j=k then u j i else 0) + (if i=k then v i j else 0) + (if i=j then w i k else 0) := by
  refine ⟨fun j i => T i j j, fun i j => if i=j then 0 else T i j i,
    fun i k => if i=k then 0 else T i i k, ?_⟩
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp

end TensorRankExterior
namespace TensorRankExterior

/-- The arm of a two-slice block that contains no added point. The two
families vary in different outer directions. -/
def Inactive (D U V : Type) [Fintype U] [Fintype V] : Prop :=
  ∃ a : U → D → ℂ, ∃ c : U → Fin 2 → ℂ, ∃ b : V → D → ℂ, ∃ f : V → Fin 2 → ℂ,
    ∀ T : D → Fin 2 → Fin 2 → ℂ, ∃ u : U → Fin 2 → ℂ, ∃ v : V → Fin 2 → ℂ, ∀ i j k,
      T i j k = (∑ q, a q i * (u q j * c q k)) + ∑ q, b q i * (f q j * v q k)

lemma pure_arms (X Y : Type) [Fintype X] [Fintype Y] :
    Inactive (X ⊕ Y) (X × Fin 2) (Y × Fin 2) := by
  classical
  refine ⟨fun q i => if Sum.inl q.1 = i then 1 else 0,
    fun q k => if q.2 = k then 1 else 0, fun q i => if Sum.inr q.1 = i then 1 else 0,
    fun q j => if q.2 = j then 1 else 0, ?_⟩
  intro T
  refine ⟨fun q j => T (Sum.inl q.1) j q.2, fun q k => T (Sum.inr q.1) q.2 k, ?_⟩
  rintro (i|i) j k <;> simp [Fintype.sum_prod_type, ite_mul, mul_ite,
    Finset.sum_ite_eq']

lemma add_arms {D U V E S R : Type} [Fintype U] [Fintype V] [Fintype S] [Fintype R]
    (h : Inactive D U V) (h' : Inactive E S R) : Inactive (D⊕E) (U⊕S) (V⊕R) := by
  obtain ⟨a,c,b,f,hh⟩ := h
  obtain ⟨a',c',b',f',hh'⟩ := h'
  refine ⟨Sum.elim (fun q => Sum.elim (a q) (fun _ => 0)) (fun q => Sum.elim (fun _ => 0) (a' q)),
    Sum.elim c c', Sum.elim (fun q => Sum.elim (b q) (fun _ => 0)) (fun q => Sum.elim (fun _ => 0) (b' q)),
    Sum.elim f f', ?_⟩
  intro T
  obtain ⟨u,v,hu⟩ := hh fun i j k => T (Sum.inl i) j k
  obtain ⟨u',v',hu'⟩ := hh' fun i j k => T (Sum.inr i) j k
  refine ⟨Sum.elim u u', Sum.elim v v', ?_⟩
  rintro (i|i) j k
  · simpa [Fintype.sum_sum_type] using hu i j k
  · simpa [Fintype.sum_sum_type] using hu' i j k

lemma transport_arm {D U V X S R : Type} [Fintype U] [Fintype V] [Fintype S] [Fintype R]
    (e : X ≃ D) (eu : S ≃ U) (ev : R ≃ V) (h : Inactive D U V) : Inactive X S R := by
  obtain ⟨a,c,b,f,hh⟩ := h
  refine ⟨fun q i => a (eu q) (e i), fun q => c (eu q), fun q i => b (ev q) (e i), fun q => f (ev q), ?_⟩
  intro T
  obtain ⟨u,v,hu⟩ := hh fun i j k => T (e.symm i) j k
  refine ⟨fun q => u (eu q), fun q => v (ev q), ?_⟩
  intro i j k
  have h1 := eu.sum_comp fun q => a q (e i) * (u q j * c q k)
  have h2 := ev.sum_comp fun q => b q (e i) * (f q j * v q k)
  simpa only [Equiv.symm_apply_apply,h1,h2] using hu (e i) j k

namespace Mixed

abbrev R := Fin 3 × Fin 2 × Fin 2
abbrev Q := Fin 2 × Fin 3 × Fin 2

def C (t : Fin 3) (k : Fin 2) : ℤ := (![![1,0],![0,1],![1,1]] : Fin 3 → Fin 2 → ℤ) t k
def A (t i : Fin 3) : ℤ := (![![1,0,1],![1,1,0],![1,1,1]] : Fin 3 → Fin 3 → ℤ) t i
def B (t : Fin 3) (j : Fin 2) : ℤ := (![![0,1],![1,0],![1,1]] : Fin 3 → Fin 2 → ℤ) t j

def M : Matrix R Q ℤ := fun ⟨i,j,k⟩ ⟨q,t,h⟩ =>
  if q=0 then (if h=j then (if t=i then C t k else 0) else 0)
  else (if h=k then A t i * B t j else 0)

def entries : Array ℤ := #[
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

def N : Matrix Q R ℤ := fun ⟨q,t,h⟩ ⟨i,j,k⟩ =>
  entries[((q.val*3+t.val)*2+h.val)*12 + (i.val*2+j.val)*2+k.val]?.getD 0

lemma exact_inverse : M * N = 1 := by
  have h : ∀ (i : Fin 3) (j k : Fin 2) (a : Fin 3) (b c : Fin 2),
      (M * N) (i,j,k) (a,b,c) = (1 : Matrix R R ℤ) (i,j,k) (a,b,c) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨a,b,c⟩ => h i j k a b c

lemma covers : Inactive (Fin 3) (Fin 3) (Fin 3) := by
  classical
  have hs : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
    apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    refine ⟨N.map (Int.castRingHom ℂ), ?_⟩
    rw [← Matrix.map_mul, exact_inverse, ← RingHom.mapMatrix_apply, map_one]
  refine ⟨fun t i => if t=i then 1 else 0, fun t k => C t k, fun t i => A t i, fun t j => B t j, ?_⟩
  intro T
  obtain ⟨y,hy⟩ := hs fun z => T z.1 z.2.1 z.2.2
  refine ⟨fun t j => y (0,t,j), fun t k => y (1,t,k), ?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : Q, ((M (i,j,k) z : ℤ) : ℂ) * y z) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Fintype.sum_prod_type, M, apply_ite, ite_mul, Finset.sum_ite_eq', mul_comm, mul_left_comm]

end Mixed

lemma inactive_arm (d u v : ℕ) (h : u+v=2*d)
    (hodd : u%2=1 → 3≤u ∧ 3≤v) : Inactive (Fin d) (Fin u) (Fin v) := by
  by_cases he : u%2=0
  · have raw := pure_arms (Fin (u/2)) (Fin (v/2))
    refine transport_arm ?_ ?_ ?_ raw <;> apply Fintype.equivOfCardEq
    all_goals
      simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod]
      omega
  · obtain ⟨hu,hv⟩ := hodd (by omega)
    have raw := add_arms (pure_arms (Fin ((u-3)/2)) (Fin ((v-3)/2))) Mixed.covers
    refine transport_arm ?_ ?_ ?_ raw <;> apply Fintype.equivOfCardEq
    all_goals
      simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod]
      omega

end TensorRankExterior
namespace TensorRankExterior

def outsideOnly {D : Type} (f : Fin 2 → ℂ) : Fin 2 ⊕ D → ℂ := Sum.elim f (fun _ => 0)
def insideOnly {D : Type} (f : D → ℂ) : Fin 2 ⊕ D → ℂ := Sum.elim (fun _ => 0) f
def edge {D : Type} : (Fin 2 ⊕ D) → (Fin 2 ⊕ D) → Prop
  | Sum.inr _, Sum.inr _ => False
  | _, _ => True
def delta {X : Type} [DecidableEq X] (x y : X) : ℂ := if x=y then 1 else 0

def Holds {D W X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    (a b : X → (Fin 2 ⊕ D) → ℂ) (c : X → W → ℂ)
    (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → (Fin 2 ⊕ D) → ℂ) : Prop :=
  ∀ T : (Fin 2 ⊕ D) → (Fin 2 ⊕ D) → W → ℂ,
    ∃ u v : X → (Fin 2 ⊕ D) → ℂ, ∃ w : X → W → ℂ,
      ∃ ui vi : N → Fin 2 → ℂ, ∃ wq : Q → W → ℂ, ∀ i j k, edge i j →
        T i j k =
          (∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) + a t i * (b t j * w t k))) +
          (∑ t, (outsideOnly (ui t) i * (insideOnly (bi t) j * ci t k) +
            insideOnly (ai t) i * (outsideOnly (vi t) j * ci t k))) +
          ∑ t, aq t i * (bq t j * wq t k)

/-- The exterior part of one group of slices. The points in X have three
free factors. Points in N lie in the inner block, and those in Q contribute
only their third-factor variations to this pencil. -/
def PencilFor (D W X N Q : Type) [Fintype X] [Fintype N] [Fintype Q] : Prop :=
  ∃ a b : X → (Fin 2 ⊕ D) → ℂ, ∃ c : X → W → ℂ,
    ∃ ai bi : N → D → ℂ, ∃ ci : N → W → ℂ,
    ∃ aq bq : Q → (Fin 2 ⊕ D) → ℂ, Holds a b c ai bi ci aq bq

abbrev Pencil (D X N Q : Type) [Fintype X] [Fintype N] [Fintype Q] := PencilFor D (Fin 2) X N Q

lemma idle_pencil {D N V : Type} [Fintype N] [Fintype V] (h : Inactive D N V) :
    Pencil D (Fin 0) N ((Fin 2 × Fin 2) ⊕ (V ⊕ V)) := by
  classical
  obtain ⟨A,C,B,F,hs⟩ := h
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, A, A, C,
    Sum.elim (fun z => outsideOnly (delta z.1)) (Sum.elim (fun t => insideOnly (B t)) (fun t => outsideOnly (F t))),
    Sum.elim (fun z => outsideOnly (delta z.2)) (Sum.elim (fun t => outsideOnly (F t)) (fun t => insideOnly (B t))), ?_⟩
  intro T
  obtain ⟨u,v,hu⟩ := hs fun i j k => T (Sum.inr i) (Sum.inl j) k
  obtain ⟨u',v',hv⟩ := hs fun j i k => T (Sum.inl i) (Sum.inr j) k
  refine ⟨fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,u',u,
    Sum.elim (fun z k => T (Sum.inl z.1) (Sum.inl z.2) k) (Sum.elim v v'), ?_⟩
  rintro (i|i) (j|j) k hh
  · simp [outsideOnly, insideOnly, delta, Fintype.sum_sum_type, Fintype.sum_prod_type,
      ite_mul, mul_ite, Finset.sum_ite_eq']
  · simpa [outsideOnly, insideOnly, Fintype.sum_sum_type, mul_comm, mul_left_comm, mul_assoc] using hv j i k
  · simpa [outsideOnly, insideOnly, Fintype.sum_sum_type] using hu i j k
  · exact False.elim hh

lemma active_pencil (I E : Type) [Fintype I] [Fintype E] :
    Pencil (I ⊕ E) (Fin 2) I (E ⊕ E) := by
  classical
  let diag (t : Fin 2) : Fin 2 ⊕ (I ⊕ E) → ℂ := outsideOnly (delta t)
  let center (t : I) (i : I ⊕ E) : ℂ := delta (Sum.inl t) i
  let side (t : E) (i : I ⊕ E) : ℂ := delta (Sum.inr t) i
  refine ⟨diag,diag,delta,center,center,fun _ _ => 1,
    Sum.elim (fun t => insideOnly (side t)) (fun _ => outsideOnly (fun _ => 1)),
    Sum.elim (fun _ => outsideOnly (fun _ => 1)) (fun t => insideOnly (side t)), ?_⟩
  intro T
  obtain ⟨uc,vc,wc,hc⟩ := active_corner fun i j k => T (Sum.inl i) (Sum.inl j) k
  obtain ⟨m,v,w,hv⟩ := active_arm fun i j k => T (Sum.inr i) (Sum.inl j) k
  obtain ⟨m',v',w',hv'⟩ := active_arm fun j i k => T (Sum.inl i) (Sum.inr j) k
  refine ⟨fun t => Sum.elim (uc t) (fun i => m i t), fun t => Sum.elim (vc t) (fun j => m' j t),
    wc,v',v,Sum.elim w w',?_⟩
  rintro (i|i) (j|j) k hh
  · rw [hc i j k]
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [Fin.sum_univ_two, diag, outsideOnly, insideOnly, delta, Fintype.sum_sum_type]
  · rw [hv' j i k]
    cases j <;> fin_cases i <;> fin_cases k <;>
      simp [diag, center, side, outsideOnly, insideOnly, delta, Fintype.sum_sum_type,
        ite_mul, mul_ite, Finset.sum_ite_eq']
  · rw [hv i j k]
    cases i <;> fin_cases j <;> fin_cases k <;>
      simp [diag, center, side, outsideOnly, insideOnly, delta, Fintype.sum_sum_type,
        ite_mul, mul_ite, Finset.sum_ite_eq']
  · exact False.elim hh

end TensorRankExterior
namespace TensorRankExterior

lemma pencil_transport {D W X N Q E Y S R : Type} [Fintype X] [Fintype N] [Fintype Q]
    [Fintype Y] [Fintype S] [Fintype R] (ed : E ≃ D) (ex : Y ≃ X) (en : S ≃ N) (eq : R ≃ Q)
    (h : PencilFor D W X N Q) : PencilFor E W Y S R := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hs⟩ := h
  let ez := Equiv.sumCongr (Equiv.refl (Fin 2)) ed
  have ho (f : Fin 2 → ℂ) (i : Fin 2 ⊕ E) : outsideOnly f (ez i) = outsideOnly f i := by
    cases i <;> rfl
  have hi (f : D → ℂ) (i : Fin 2 ⊕ E) :
      insideOnly f (ez i) = insideOnly (fun s => f (ed s)) i := by cases i <;> rfl
  refine ⟨fun y i => a (ex y) (ez i),fun y i => b (ex y) (ez i),fun y => c (ex y),
    fun z i => ai (en z) (ed i),fun z i => bi (en z) (ed i),fun z => ci (en z),
    fun z i => aq (eq z) (ez i),fun z i => bq (eq z) (ez i),?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hT⟩ := hs fun i j k => T (ez.symm i) (ez.symm j) k
  refine ⟨fun t i => u (ex t) (ez i),fun t j => v (ex t) (ez j),fun t => w (ex t),
    fun t => ui (en t),fun t => vi (en t),fun t => wq (eq t),?_⟩
  intro i j k he
  have hh : edge (ez i) (ez j) := by cases i <;> cases j <;> exact he
  have hT := hT (ez i) (ez j) k hh
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hT
  rw [hT]
  congr 1
  · congr 1
    · exact (ex.sum_comp (fun z => u z (ez i) * (b z (ez j) * c z k) +
        a z (ez i) * (v z (ez j) * c z k) + a z (ez i) * (b z (ez j) * w z k))).symm
    · have hsum := en.sum_comp (fun z => outsideOnly (ui z) (ez i) * (insideOnly (bi z) (ez j) * ci z k) +
        insideOnly (ai z) (ez i) * (outsideOnly (vi z) (ez j) * ci z k))
      simpa only [ho,hi] using hsum.symm
  · exact (eq.sum_comp (fun z => aq z (ez i) * (bq z (ez j) * wq z k))).symm

lemma even_active (a b : ℕ) :
    Pencil (Fin (2*a+2*b+2)) (Fin 2) (Fin (a+2*b+1)) (Fin (2*(a+1))) := by
  have raw := active_pencil (Fin (a+2*b+1)) (Fin (a+1))
  refine pencil_transport ?_ (Equiv.refl _) (Equiv.refl _) ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

lemma even_idle (a b : ℕ) (hodd : a%2=1 → 3≤a) :
    Pencil (Fin (2*a+2*b+2)) (Fin 0) (Fin (3*a+4*b+4)) (Fin (2*(a+2))) := by
  have raw := idle_pencil (inactive_arm (2*a+2*b+2) (3*a+4*b+4) a (by omega) (by
    intro he; exact ⟨by omega, hodd (by omega)⟩))
  refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ raw
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum]
  omega

end TensorRankExterior
namespace TensorRankExterior.Pencils

abbrev Coord (D : Type) := Fin 2 ⊕ D
abbrev Rows (D W : Type) := {z : Coord D × Coord D × W // edge z.1 z.2.1}
abbrev Cols (D W X N Q : Type) :=
  (X × (Coord D ⊕ (Coord D ⊕ W))) ⊕ ((N × (Fin 2 ⊕ Fin 2)) ⊕ (Q × W))

def matrix {D W X N Q K : Type} [CommRing K] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → K) (c : X → W → K)
    (ai bi : N → D → K) (ci : N → W → K) (aq bq : Q → Coord D → K) :
    Matrix (Rows D W) (Cols D W X N Q) K
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inl h) => if h=i then b t j * c t k else 0
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inr (Sum.inl h)) => if h=j then a t i * c t k else 0
  | ⟨(i,j,k),_⟩, Sum.inl (t,Sum.inr (Sum.inr h)) => if h=k then a t i * b t j else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inl (t,Sum.inl h)) =>
      if Sum.inl h=i then j.elim (fun _ => 0) (bi t) * ci t k else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inl (t,Sum.inr h)) =>
      if Sum.inl h=j then i.elim (fun _ => 0) (ai t) * ci t k else 0
  | ⟨(i,j,k),_⟩, Sum.inr (Sum.inr (t,h)) => if h=k then aq t i * bq t j else 0

lemma action {D W X N Q : Type} [Fintype W] [Fintype D] [Fintype X] [Fintype N] [Fintype Q] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → ℂ) (c : X → W → ℂ) (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → Coord D → ℂ) (y : Cols D W X N Q → ℂ) (i j : Coord D) (k : W) (e : edge i j) :
    (matrix a b c ai bi ci aq bq).mulVec y ⟨(i,j,k),e⟩ =
      (∑ t, (y (Sum.inl (t,Sum.inl i)) * (b t j * c t k) +
        a t i * (y (Sum.inl (t,Sum.inr (Sum.inl j))) * c t k) +
        a t i * (b t j * y (Sum.inl (t,Sum.inr (Sum.inr k)))))) +
      (∑ t, (outsideOnly (fun h => y (Sum.inr (Sum.inl (t,Sum.inl h)))) i * (insideOnly (bi t) j * ci t k) +
        insideOnly (ai t) i * (outsideOnly (fun h => y (Sum.inr (Sum.inl (t,Sum.inr h)))) j * ci t k))) +
      ∑ t, aq t i * (bq t j * y (Sum.inr (Sum.inr (t,k)))) := by
  change (∑ z : Cols D W X N Q, matrix a b c ai bi ci aq bq ⟨(i,j,k),e⟩ z * y z) = _
  cases i <;> cases j <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, matrix, outsideOnly, insideOnly, ite_mul,
      Finset.sum_ite_eq', Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, add_assoc]

lemma holds_iff {D W X N Q : Type} [Fintype W] [Fintype D] [Fintype X] [Fintype N] [Fintype Q] [DecidableEq D] [DecidableEq W]
    (a b : X → Coord D → ℂ) (c : X → W → ℂ) (ai bi : N → D → ℂ) (ci : N → W → ℂ)
    (aq bq : Q → Coord D → ℂ) :
    Holds a b c ai bi ci aq bq ↔ Function.Surjective (matrix a b c ai bi ci aq bq).mulVec := by
  classical
  constructor
  · intro hh T
    let lift (i j : Coord D) (k : W) := if e : edge i j then T ⟨(i,j,k),e⟩ else 0
    obtain ⟨u,v,w,ui,vi,wq,hT⟩ := hh lift
    let y : Cols D W X N Q → ℂ := Sum.elim (fun z => z.2.elim (u z.1) (Sum.elim (v z.1) (w z.1)))
      (Sum.elim (fun z => z.2.elim (ui z.1) (vi z.1)) (fun z => wq z.1 z.2))
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨⟨i,j,k⟩,e⟩ := z
    exact ((action a b c ai bi ci aq bq y i j k e).trans (hT i j k e).symm).trans (dif_pos e)
  · intro hh T
    obtain ⟨y,hy⟩ := hh fun z => T z.1.1 z.1.2.1 z.1.2.2
    refine ⟨fun t i => y (Sum.inl (t,Sum.inl i)),fun t j => y (Sum.inl (t,Sum.inr (Sum.inl j))),
      fun t k => y (Sum.inl (t,Sum.inr (Sum.inr k))),fun t i => y (Sum.inr (Sum.inl (t,Sum.inl i))),
      fun t j => y (Sum.inr (Sum.inl (t,Sum.inr j))),fun t k => y (Sum.inr (Sum.inr (t,k))),?_⟩
    intro i j k e
    exact (congrFun hy ⟨(i,j,k),e⟩).symm.trans (action a b c ai bi ci aq bq y i j k e)

end TensorRankExterior.Pencils
namespace TensorRankExterior.Pencils

open MvPolynomial

abbrev Away {K : Type} (X : K → Type) (k : K) := {z : Sigma X // z.1 ≠ k}
abbrev Variables (D : Type) {K : Type} (W X N : K → Type) :=
  (Sigma X × (Coord D ⊕ (Coord D ⊕ Sigma W))) ⊕ (Sigma N × (D ⊕ (D ⊕ Sigma W)))

def split {K : Type} {X : K → Type} [DecidableEq K] (k : K) : Sigma X ≃ X k ⊕ Away X k where
  toFun z := if e : z.1=k then Sum.inl (e ▸ z.2) else Sum.inr ⟨z,e⟩
  invFun := Sum.elim (fun t => ⟨k,t⟩) Subtype.val
  left_inv := by rintro ⟨l,t⟩; by_cases he : l=k <;> simp [he]
  right_inv := by rintro (t|⟨⟨l,t⟩,he⟩) <;> simp_all

lemma split_here {K : Type} {X : K → Type} [DecidableEq K] (k : K) (t : X k) :
    split k ⟨k,t⟩ = Sum.inl t := by simp [split]

lemma split_away {K : Type} {X : K → Type} [DecidableEq K] (k : K) (t : Away X k) :
    split k t.val = Sum.inr t := by simp [split, t.property]

section Factors
variable {K D F : Type} {W X N : K → Type} (x : Variables D W X N → F)
def xa (z : Sigma X) (i : Coord D) := x (Sum.inl (z,Sum.inl i))
def xb (z : Sigma X) (j : Coord D) := x (Sum.inl (z,Sum.inr (Sum.inl j)))
def xc (z : Sigma X) (k : Sigma W) := x (Sum.inl (z,Sum.inr (Sum.inr k)))
def na (z : Sigma N) (i : D) := x (Sum.inr (z,Sum.inl i))
def nb (z : Sigma N) (j : D) := x (Sum.inr (z,Sum.inr (Sum.inl j)))
def nc (z : Sigma N) (k : Sigma W) := x (Sum.inr (z,Sum.inr (Sum.inr k)))
end Factors

section Family
variable {K D : Type} {W X N : K → Type} [Fintype K] [DecidableEq K]
  [∀k,Fintype (X k)] [∀k,Fintype (N k)]

def At (k : K) (x : Variables D W X N → ℂ) : Prop := Holds
    (fun t => xa x ⟨k,t⟩) (fun t => xb x ⟨k,t⟩) (fun t j => xc x ⟨k,t⟩ ⟨k,j⟩)
    (fun t => na x ⟨k,t⟩) (fun t => nb x ⟨k,t⟩) (fun t j => nc x ⟨k,t⟩ ⟨k,j⟩)
    (fun q : Away X k => xa x q.val) (fun q : Away X k => xb x q.val)

lemma assignment (k : K) (h : PencilFor D (W k) (X k) (N k) (Away X k)) :
    ∃ x : Variables D W X N → ℂ, At k x := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hs⟩ := h
  let atSlice (f : W k → ℂ) (z : Sigma W) := if he : z.1=k then f (he ▸ z.2) else 0
  let x : Variables D W X N → ℂ := Sum.elim
    (fun p => (split k p.1).elim (fun t => p.2.elim (a t) (Sum.elim (b t) (atSlice (c t))))
      (fun q => p.2.elim (aq q) (Sum.elim (bq q) (fun _ => 0))))
    (fun p => (split k p.1).elim (fun t => p.2.elim (ai t) (Sum.elim (bi t) (atSlice (ci t)))) (fun _ => 0))
  refine ⟨x, ?_⟩
  unfold At
  convert hs using 1 <;> funext t i <;>
    simp only [xa,xb,xc,na,nb,nc,x,atSlice,split_here,split_away,Sum.elim_inl,Sum.elim_inr,dif_pos True.intro]

end Family

section Specialize
variable {K D : Type} {W X N : K → Type} [DecidableEq D] [∀k,DecidableEq (W k)]

noncomputable def symbolic (k : K) : Matrix (Rows D (W k)) (Cols D (W k) (X k) (N k) (Away X k))
    (MvPolynomial (Variables D W X N) ℂ) :=
  let v : Variables D W X N → MvPolynomial (Variables D W X N) ℂ := MvPolynomial.X
  matrix (fun t => xa v ⟨k,t⟩) (fun t => xb v ⟨k,t⟩) (fun t j => xc v ⟨k,t⟩ ⟨k,j⟩)
    (fun t => na v ⟨k,t⟩) (fun t => nb v ⟨k,t⟩) (fun t j => nc v ⟨k,t⟩ ⟨k,j⟩)
    (fun q : Away X k => xa v q.val) (fun q : Away X k => xb v q.val)

lemma specialization (k : K) (x : Variables D W X N → ℂ) :
    (symbolic k).map (eval x) = matrix (fun t => xa x ⟨k,t⟩) (fun t => xb x ⟨k,t⟩)
      (fun t j => xc x ⟨k,t⟩ ⟨k,j⟩) (fun t => na x ⟨k,t⟩) (fun t => nb x ⟨k,t⟩) (fun t j => nc x ⟨k,t⟩ ⟨k,j⟩)
      (fun q : Away X k => xa x q.val) (fun q : Away X k => xb x q.val) := by
  ext ⟨⟨i,j,h⟩,hz⟩ z
  rcases z with ⟨t,e|e|e⟩ | ⟨t,e|e⟩ | ⟨t,e⟩ <;>
    cases i <;> cases j <;>
    simp only [symbolic, matrix,xa,xb,xc,na,nb,nc,Matrix.map_apply,Sum.elim_inl,Sum.elim_inr] <;>
    split <;> simp

end Specialize

section Family
variable {K D : Type} {W X N : K → Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D] [∀k,DecidableEq (W k)] [∀k,Fintype (W k)]
  [∀k,Fintype (X k)] [∀k,Fintype (N k)]

lemma at_iff (k : K) (x : Variables D W X N → ℂ) :
    At k x ↔ Function.Surjective ((symbolic k).map (eval x)).mulVec := by
  rw [specialization]
  exact holds_iff _ _ _ _ _ _ _ _

lemma common (h : ∀ k : K, PencilFor D (W k) (X k) (N k) (Away X k)) :
    ∃ x : Variables D W X N → ℂ, ∀ k, At k x := by
  classical
  have hs (k : K) : ∃ x : Variables D W X N → ℂ, Function.Surjective ((symbolic k).map (eval x)).mulVec := by
    obtain ⟨x,hx⟩ := assignment k (h k)
    exact ⟨x,(at_iff k x).mp hx⟩
  obtain ⟨x,_,hx⟩ := simultaneous_surjectivity (fun k : K => @symbolic _ D W X N _ _ k) hs 1 one_ne_zero
  exact ⟨x,fun k => (at_iff k x).mpr (hx k)⟩

end Family
end TensorRankExterior.Pencils
namespace TensorRankExterior.Pencils

lemma sum_split {K : Type} {X : K → Type} [Fintype K] [DecidableEq K] [∀k,Fintype (X k)]
    (k : K) (F : Sigma X → ℂ) : (∑ z, F z) = (∑ t : X k, F ⟨k,t⟩) + ∑ q : Away X k, F q.val := by
  have h := (@split K X _ k).symm.sum_comp F
  rw [Fintype.sum_sum_type] at h
  exact h.symm

def slice {K : Type} {W : K → Type} [DecidableEq K] (k : K) (f : Sigma W → ℂ) (p : Sigma W) : ℂ :=
  if k=p.1 then f p else 0

def Combined {K D : Type} [Fintype K] [DecidableEq K] {W X N : K → Type}
    [∀k,Fintype (X k)] [∀k,Fintype (N k)] (x : Variables D W X N → ℂ) : Prop :=
  ∀ T : Coord D → Coord D → (Sigma W) → ℂ,
    ∃ u v : Sigma X → Coord D → ℂ, ∃ w : Sigma X → (Sigma W) → ℂ,
    ∃ ui vi : Sigma N → Fin 2 → ℂ, ∀ i j z, edge i j →
      T i j z =
        (∑ t, (u t i * (xb x t j * slice t.1 (xc x t) z) +
          xa x t i * (v t j * slice t.1 (xc x t) z) + xa x t i * (xb x t j * w t z))) +
        ∑ t, (outsideOnly (ui t) i * (insideOnly (nb x t) j * slice t.1 (nc x t) z) +
          insideOnly (na x t) i * (outsideOnly (vi t) j * slice t.1 (nc x t) z))

lemma assemble {K D : Type} [Fintype K] [DecidableEq K] {W X N : K → Type}
    [∀k,Fintype (X k)] [∀k,Fintype (N k)]
    (x : Variables D W X N → ℂ) (h : ∀ k, At k x) : Combined x := by
  classical
  intro T
  choose u v w ui vi wq good using fun k : K => h k (fun i j s => T i j ⟨k,s⟩)
  let join (t : Sigma X) (z : Sigma W) : ℂ := (split z.1 t).elim
    (fun q => w z.1 q z.2) (fun q => wq z.1 q z.2)
  refine ⟨fun t => u t.1 t.2,fun t => v t.1 t.2,join,fun t => ui t.1 t.2,fun t => vi t.1 t.2,?_⟩
  rintro i j ⟨k,z⟩ he
  rw [good k i j z he]
  rw [sum_split (X:=X) k, sum_split (X:=N) k]
  have hx (q : Away X k) : q.val.1 ≠ k := q.property
  have hn (q : Away N k) : q.val.1 ≠ k := q.property
  simp [slice,join,split_here,split_away,hx,hn,add_comm,add_left_comm,add_assoc]

lemma exists_combined {K D : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
    {W X N : K → Type} [∀k,Fintype (X k)] [∀k,Fintype (N k)]
    [∀k,Fintype (W k)] [∀k,DecidableEq (W k)]
    (h : ∀ k : K, PencilFor D (W k) (X k) (N k) (Away X k)) :
    ∃ x : Variables D W X N → ℂ, Combined x := by
  obtain ⟨x,hx⟩ := common h
  exact ⟨x,assemble x hx⟩

end TensorRankExterior.Pencils
namespace TensorRankExterior.Pencils

def splitAt (r s p : ℕ) (h : r=s+p) : Fin r ≃ Fin s ⊕ Fin p where
  toFun t := if ht : t.val<s then Sum.inl ⟨t.val,ht⟩ else Sum.inr ⟨t.val-s,by omega⟩
  invFun := Sum.elim (fun t => ⟨t.val,by omega⟩) (fun t => ⟨s+t.val,by omega⟩)
  left_inv := by
    intro t
    by_cases ht : t.val<s
    · simp [ht]
    · simp [ht,Fin.ext_iff]
      omega
  right_inv := by
    rintro (t|t)
    · simp [t.isLt]
    · simp [show ¬s+t.val<s by omega]

lemma splitAt_small {r s p : ℕ} (h : r=s+p) (t : Fin r) (ht : t.val<s) :
    splitAt r s p h t=Sum.inl ⟨t.val,ht⟩ := by simp [splitAt,ht]

def coordIso {n d : ℕ} (h : n=d+2) : Fin n ≃ Coord (Fin d) :=
  (splitAt n d 2 h).trans (Equiv.sumComm _ _)

lemma coord_small {n d : ℕ} (h : n=d+2) (i : Fin n) (hi : i.val<d) :
    coordIso h i=Sum.inr ⟨i.val,hi⟩ := by simp [coordIso,splitAt,hi]

lemma inner_pad {n d : ℕ} (h : n=d+2) (i : Fin n) (a : Fin d → ℂ) :
    insideOnly a (coordIso h i) = (if hi : i.val<d then a ⟨i.val,hi⟩ else 0) := by
  by_cases hi : i.val<d <;> simp [insideOnly,coordIso,splitAt,hi]

lemma edge_of_index {n d : ℕ} (h : n=d+2) (i j k : Fin n) (he : d ≤ i.val ∨ d ≤ j.val ∨ n ≤ k.val) :
    edge (coordIso h i) (coordIso h j) := by
  by_cases hi : i.val<d <;> by_cases hj : j.val<d <;>
    simp [edge,coordIso,splitAt,hi,hj]
  omega

lemma sum_elim {R U V : Type} [Fintype R] [Fintype U] [Fintype V] (e : R ≃ U⊕V)
    (a : U → ℂ) (b : V → ℂ) : (∑t, (e t).elim a b) = (∑t, a t)+(∑t, b t) := by
  have h := e.sum_comp (Sum.elim a b)
  simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using h

lemma witness_of_combined {K Z : Type} [Fintype K] [DecidableEq K] [Fintype Z]
    {W₀ X N : K → Type} [∀k,Fintype (X k)] [∀k,Fintype (N k)] {n d s r : ℕ} (hn : n=d+2)
    (ew : Fin n ≃ Sigma W₀) (ep : Fin r ≃ Fin s ⊕ Sigma X)
    (hp : ∀ t : Fin r, ∀ ht : t.val<s, ep t=Sum.inl ⟨t.val,ht⟩) (en : Fin s ≃ Sigma N ⊕ Z)
    (x : Variables (Fin d) W₀ X N → ℂ) (combined : Combined x) : Witness n d n s r := by
  classical
  let ei := coordIso hn
  let an (t : Fin s) (i : Fin d) := (en t).elim (fun q => na x q i) (fun _ => 0)
  let bn (t : Fin s) (i : Fin d) := (en t).elim (fun q => nb x q i) (fun _ => 0)
  let cn (t : Fin s) (k : Fin n) := (en t).elim (fun q => slice q.1 (nc x q) (ew k)) (fun _ => 0)
  let par : Param d n s → ℂ := fun p => p.2.elim (an p.1) (Sum.elim (bn p.1) (cn p.1))
  let A (t : Fin r) (i : Fin n) := (ep t).elim (fun z => insideOnly (an z) (ei i)) (fun z => xa x z (ei i))
  let B (t : Fin r) (j : Fin n) := (ep t).elim (fun z => insideOnly (bn z) (ei j)) (fun z => xb x z (ei j))
  let C (t : Fin r) (k : Fin n) := (ep t).elim (fun z => cn z k) (fun z => slice z.1 (xc x z) (ew k))
  refine ⟨par,A,B,C,?_,?_⟩
  · intro t ht i
    simp [A,B,C,hp t ht,ei,inner_pad,par,i.isLt]
  · intro T
    obtain ⟨u,v,w,ui,vi,ht⟩ := combined fun i j k => T (ei.symm i) (ei.symm j) (ew.symm k)
    let U (t : Fin r) (i : Fin n) := (ep t).elim
      (fun z => (en z).elim (fun q => outsideOnly (ui q) (ei i)) (fun _ => 0)) (fun z => u z (ei i))
    let V (t : Fin r) (j : Fin n) := (ep t).elim
      (fun z => (en z).elim (fun q => outsideOnly (vi q) (ei j)) (fun _ => 0)) (fun z => v z (ei j))
    let W (t : Fin r) (k : Fin n) := (ep t).elim (fun _ => 0) (fun z => w z (ew k))
    refine ⟨U,V,W,?_⟩
    intro i j k he
    let F (z : Sigma N) := outsideOnly (ui z) (ei i) * (insideOnly (nb x z) (ei j) * slice z.1 (nc x z) (ew k)) +
      insideOnly (na x z) (ei i) * (outsideOnly (vi z) (ei j) * slice z.1 (nc x z) (ew k))
    let G (z : Sigma X) := u z (ei i) * (xb x z (ei j) * slice z.1 (xc x z) (ew k)) +
      xa x z (ei i) * (v z (ei j) * slice z.1 (xc x z) (ew k)) +
      xa x z (ei i) * (xb x z (ei j) * w z (ew k))
    have hs : T i j k = (∑ z, G z) + ∑ z, F z := by
      simpa only [Equiv.symm_apply_apply] using ht (ei i) (ei j) (ew k) (edge_of_index hn i j k he)
    rw [hs]
    calc
      _ = ∑ t, (ep t).elim (fun z => (en z).elim F (fun _ => 0)) G := by
        rw [sum_elim, sum_elim, Finset.sum_const_zero, add_zero, add_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        cases eqt : ep t with
        | inl z =>
          cases eqz : en z with
          | inl q =>
            simp only [U,V,W,A,B,C,an,bn,cn,F,eqt,eqz,Sum.elim_inl,mul_zero,add_zero]
          | inr q => simp [U,V,W,A,B,C,an,bn,cn,F,eqt,eqz]
        | inr z => simp [U,V,W,A,B,C,G,eqt]

end TensorRankExterior.Pencils
namespace TensorRankExterior.Pencils

def blockSize {a b : ℕ} (u v : ℕ) : Fin a ⊕ Fin b → ℕ := Sum.elim (fun _ => u) (fun _ => v)
abbrev Groups (a b : ℕ) := Fin (a+2) ⊕ Fin b
abbrev ExtraSlots (a b : ℕ) (k : Groups a b) := Fin (blockSize 2 0 k)
abbrev InnerSlots (a b : ℕ) (k : Groups a b) := Fin (blockSize (a+2*b+1) (3*a+4*b+4) k)

lemma card_slots (a b u v : ℕ) :
    Fintype.card (Σ h : Fin a ⊕ Fin b, Fin (blockSize u v h)) = a*u+b*v := by
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  change (∑ _ : Fin a, Fintype.card (Fin u)) + (∑ _ : Fin b, Fintype.card (Fin v)) = _
  simp

lemma all_even_pencils (a b : ℕ) (ho : b>0 → a%2=1 → 3≤a) :
    ∃ x : Variables (Fin (2*a+2*b+2)) (fun _ : Groups a b => Fin 2) (ExtraSlots a b) (InnerSlots a b) → ℂ, Combined x := by
  apply exists_combined
  intro k
  have hoff := (Fintype.card_congr (@split _ (ExtraSlots a b) _ k)).symm
  rw [Fintype.card_sum] at hoff
  have hX : Fintype.card (Sigma (ExtraSlots a b)) = (a+2)*2+b*0 := card_slots _ _ _ _
  rw [hX] at hoff
  cases k with
  | inl k =>
    change 2 + _ = _ at hoff
    refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (even_active a b)
    apply Fintype.equivOfCardEq
    rw [Fintype.card_fin]
    omega
  | inr k =>
    change 0 + _ = _ at hoff
    have hb : 0 < b := (Nat.zero_le k.val).trans_lt k.isLt
    refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (even_idle a b (ho hb))
    apply Fintype.equivOfCardEq
    rw [Fintype.card_fin]
    omega

lemma even_config (a b s : ℕ) (ho : b>0 → a%2=1 → 3≤a)
    (hs : (a+2)*(a+2*b+1)+b*(3*a+4*b+4) ≤ s) :
    Witness (2*(a+b+2)) (2*a+2*b+2) (2*(a+b+2)) s (s+2*(a+2)) := by
  classical
  let K := Groups a b
  let X := ExtraSlots a b
  let N := InnerSlots a b
  obtain ⟨x,hx⟩ := all_even_pencils a b ho
  let ew : Fin (2*(a+b+2)) ≃ Sigma (fun _ : K => Fin 2) := Fintype.equivOfCardEq (by
    simp [K,Groups,Fintype.card_sigma]; omega)
  have hc : Fintype.card (Sigma X)=(a+2)*2+b*0 := card_slots _ _ _ _
  let ex : Fin (2*(a+2)) ≃ Sigma X := Fintype.equivOfCardEq (by rw [Fintype.card_fin,hc]; omega)
  let ep := (splitAt (s+2*(a+2)) s (2*(a+2)) rfl).trans (Equiv.sumCongr (Equiv.refl (Fin s)) ex)
  have hp (t : Fin (s+2*(a+2))) (ht : t.val<s) : ep t=Sum.inl ⟨t.val,ht⟩ := by
    simp [ep,splitAt_small rfl t ht]
  have hn : Fintype.card (Sigma N)=(a+2)*(a+2*b+1)+b*(3*a+4*b+4) := card_slots _ _ _ _
  let en : Fin s ≃ Sigma N ⊕ Fin (s-Fintype.card (Sigma N)) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum,Fintype.card_fin,hn]; omega)
  exact witness_of_combined (by omega) ew ep hp en x hx

lemma even_supported (n : ℕ) (hn : 5≤n) (hc : n%3≠1) (he : n%2=0) (hp : (n-(n-1)/9)%2=0) :
    Witness n (n-2) n (coreCount n) (n^3 ⌈/⌉ (3*n-2)) := by
  obtain ⟨a,b,ha,hb,ho,hs⟩ := even_pencil_parameters n hn hc he hp
  have hd : n-2=2*a+2*b+2 := by omega
  have hr : n^3 ⌈/⌉ (3*n-2)=coreCount n+2*(a+2) := by rw [cube_count n (by omega)]; omega
  rw [hr,hd]
  convert even_config a b (coreCount n) ho hs using 1

end TensorRankExterior.Pencils
namespace TensorRankExterior

/-- A single inactive slice. Four outer basis tensors cover its corner, and
two additional points per remaining inner coordinate cover each arm. -/
lemma singleton_idle (I E : Type) [Fintype I] [Fintype E] :
    PencilFor (I ⊕ E) (Fin 1) (Fin 0) I ((Fin 2 × Fin 2) ⊕ ((E × Fin 2) ⊕ (E × Fin 2))) := by
  classical
  let a (t : I) (i : I ⊕ E) := delta (Sum.inl t) i
  let b (t : E) (i : I ⊕ E) := delta (Sum.inr t) i
  refine ⟨fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,a,a,fun _ _ => 1,
    Sum.elim (fun z => outsideOnly (delta z.1)) (Sum.elim (fun z => insideOnly (b z.1)) (fun z => outsideOnly (delta z.2))),
    Sum.elim (fun z => outsideOnly (delta z.2)) (Sum.elim (fun z => outsideOnly (delta z.2)) (fun z => insideOnly (b z.1))), ?_⟩
  intro T
  refine ⟨fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,
    fun t i => T (Sum.inl i) (Sum.inr (Sum.inl t)) 0,fun t j => T (Sum.inr (Sum.inl t)) (Sum.inl j) 0,
    Sum.elim (fun z k => T (Sum.inl z.1) (Sum.inl z.2) k)
      (Sum.elim (fun z k => T (Sum.inr (Sum.inr z.1)) (Sum.inl z.2) k)
        (fun z k => T (Sum.inl z.2) (Sum.inr (Sum.inr z.1)) k)), ?_⟩
  rintro (i|i) (j|j) k he
  · simp [insideOnly,outsideOnly,Fintype.sum_sum_type,Fintype.sum_prod_type,delta,ite_mul,mul_ite,Finset.sum_ite_eq']
  · cases j <;> fin_cases k <;>
      simp [a,b,insideOnly,outsideOnly,Fintype.sum_sum_type,Fintype.sum_prod_type,delta,ite_mul,mul_ite,Finset.sum_ite_eq']
  · cases i <;> fin_cases k <;>
      simp [a,b,insideOnly,outsideOnly,Fintype.sum_sum_type,Fintype.sum_prod_type,delta,ite_mul,mul_ite,Finset.sum_ite_eq']
  · exact False.elim he

end TensorRankExterior
namespace TensorRankExterior.Pencils

lemma unused_incoming {D W X N Q Z : Type} [Fintype X] [Fintype N] [Fintype Q] [Fintype Z]
    (h : PencilFor D W X N Q) : PencilFor D W X N (Q ⊕ Z) := by
  obtain ⟨a,b,c,ai,bi,ci,aq,bq,hs⟩ := h
  refine ⟨a,b,c,ai,bi,ci,Sum.elim aq (fun _ _ => 0),Sum.elim bq (fun _ _ => 0),?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,ht⟩ := hs T
  refine ⟨u,v,w,ui,vi,Sum.elim wq (fun _ _ => 0),?_⟩
  intro i j k he
  simpa [Fintype.sum_sum_type] using ht i j k he

lemma odd_active (a b : ℕ) :
    Pencil (Fin (2*a+2*b+3)) (Fin 2) (Fin (a+2*b+2)) (Fin (2*(a+1))) := by
  refine pencil_transport ?_ (Equiv.refl _) (Equiv.refl _) ?_ (active_pencil (Fin (a+2*b+2)) (Fin (a+1)))
  all_goals
    apply Fintype.equivOfCardEq
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

lemma odd_idle (a b : ℕ) (ho : a%2=1 → 3≤a) :
    Pencil (Fin (2*a+2*b+3)) (Fin 0) (Fin (3*a+4*b+6)) (Fin (2*(a+2))) := by
  have raw := idle_pencil (inactive_arm (2*a+2*b+3) (3*a+4*b+6) a (by omega) (by
    intro he; exact ⟨by omega,ho (by omega)⟩))
  refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ raw
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum]
  omega

lemma odd_single (a b : ℕ) :
    let d := 2*a+2*b+3
    PencilFor (Fin d) (Fin 1) (Fin 0) (Fin (d-a/2)) (Fin (2*(a+2))) := by
  dsimp only
  have raw := unused_incoming (Z:=Fin (2*(a%2))) (singleton_idle (Fin (2*a+2*b+3-a/2)) (Fin (a/2)))
  refine pencil_transport ?_ (Equiv.refl _) (Equiv.refl _) ?_ raw
  all_goals
    apply Fintype.equivOfCardEq
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega

abbrev OddGroups (a b : ℕ) := Option (Groups a b)
abbrev OddW (a b : ℕ) (k : OddGroups a b) := Fin (k.elim 1 (fun _ => 2))
abbrev OddX (a b : ℕ) (k : OddGroups a b) := Fin (k.elim 0 (blockSize 2 0))
abbrev OddN (a b : ℕ) (k : OddGroups a b) :=
  Fin (k.elim (2*a+2*b+3-a/2) (blockSize (a+2*b+2) (3*a+4*b+6)))

lemma card_three (a b h u v : ℕ) :
    Fintype.card (Σ k : Option (Fin a ⊕ Fin b), Fin (k.elim h (blockSize u v))) = h+(a*u+b*v) := by
  rw [Fintype.card_sigma,Fintype.sum_option,Fintype.sum_sum_type]
  change Fintype.card (Fin h) + ((∑ _ : Fin a, Fintype.card (Fin u)) + ∑ _ : Fin b, Fintype.card (Fin v)) = _
  simp

lemma all_odd_pencils (a b : ℕ) (ho : b>0 → a%2=1 → 3≤a) :
    ∃ x : Variables (Fin (2*a+2*b+3)) (OddW a b) (OddX a b) (OddN a b) → ℂ, Combined x := by
  apply exists_combined
  intro k
  have hoff := (Fintype.card_congr (@split _ (OddX a b) _ k)).symm
  rw [Fintype.card_sum] at hoff
  have hX : Fintype.card (Sigma (OddX a b)) = 0+((a+2)*2+b*0) := card_three _ _ _ _ _
  rw [hX] at hoff
  rcases k with _ | (k|k)
  · change 0+_=_ at hoff
    refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (odd_single a b)
    apply Fintype.equivOfCardEq
    rw [Fintype.card_fin]
    omega
  · change 2+_=_ at hoff
    refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (odd_active a b)
    apply Fintype.equivOfCardEq
    rw [Fintype.card_fin]
    omega
  · change 0+_=_ at hoff
    have hb : 0<b := (Nat.zero_le k.val).trans_lt k.isLt
    refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (odd_idle a b (ho hb))
    apply Fintype.equivOfCardEq
    rw [Fintype.card_fin]
    omega

lemma odd_budget (n p s a b : ℕ) (hn : n=2*(a+b+2)+1) (hp : p=2*(a+2))
    (hs : 3*s+2*n=n^2) (hr : n^3 ≤ (3*n-2)*(s+p)) :
    (2*a+2*b+3-a/2) + ((a+2)*(a+2*b+2)+b*(3*a+4*b+6)) ≤ s := by
  subst n p
  have hD : 3*(2*(a+b+2)+1)-2=6*a+6*b+13 := by omega
  rw [hD] at hr
  have ha : (2*a+2*b+3-a/2)+a/2=2*a+2*b+3 := by omega
  have half : a ≤ 2*(a/2)+1 := by omega
  have h4 : 4*((2*a+2*b+3-a/2) + ((a+2)*(a+2*b+2)+b*(3*a+4*b+6))) ≤ 4*s+2 := by
    nlinarith [congrArg (fun t : ℕ => (2*(a+b+2)+1)*t) hs]
  omega

lemma odd_config (a b s : ℕ) (ho : b>0 → a%2=1 → 3≤a)
    (hs : (2*a+2*b+3-a/2) + ((a+2)*(a+2*b+2)+b*(3*a+4*b+6)) ≤ s) :
    Witness (2*(a+b+2)+1) (2*a+2*b+3) (2*(a+b+2)+1) s (s+2*(a+2)) := by
  classical
  let W := OddW a b
  let X := OddX a b
  let N := OddN a b
  obtain ⟨x,hx⟩ := all_odd_pencils a b ho
  have hW : Fintype.card (Sigma W) = 1+((a+2)*2+b*2) := by
    change Fintype.card (Σ k : OddGroups a b, Fin (k.elim 1 (fun _ => 2))) = _
    rw [Fintype.card_sigma,Fintype.sum_option,Fintype.sum_sum_type]
    change Fintype.card (Fin 1) + ((∑ _ : Fin (a+2), Fintype.card (Fin 2)) + ∑ _ : Fin b, Fintype.card (Fin 2)) = _
    simp
  let ew : Fin (2*(a+b+2)+1) ≃ Sigma W := Fintype.equivOfCardEq (by rw [Fintype.card_fin,hW]; omega)
  have hc : Fintype.card (Sigma X)=0+((a+2)*2+b*0) := card_three _ _ _ _ _
  let ex : Fin (2*(a+2)) ≃ Sigma X := Fintype.equivOfCardEq (by rw [Fintype.card_fin,hc]; omega)
  let ep := (splitAt (s+2*(a+2)) s (2*(a+2)) rfl).trans (Equiv.sumCongr (Equiv.refl (Fin s)) ex)
  have hp (t : Fin (s+2*(a+2))) (ht : t.val<s) : ep t=Sum.inl ⟨t.val,ht⟩ := by
    simp [ep,splitAt_small rfl t ht]
  have hn : Fintype.card (Sigma N)=(2*a+2*b+3-a/2) + ((a+2)*(a+2*b+2)+b*(3*a+4*b+6)) :=
    card_three _ _ _ _ _
  let en : Fin s ≃ Sigma N ⊕ Fin (s-Fintype.card (Sigma N)) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum,Fintype.card_fin,hn]; omega)
  exact witness_of_combined (by omega) ew ep hp en x hx

lemma even_extra_supported (n : ℕ) (hn : 5≤n) (hc : n%3≠1) (hp : (n-(n-1)/9)%2=0) :
    Witness n (n-2) n (coreCount n) (n^3 ⌈/⌉ (3*n-2)) := by
  by_cases he : n%2=0
  · exact even_supported n hn hc he hp
  let p := n-(n-1)/9
  let a := p/2-2
  let b := (n-p-1)/2
  have ha : p=2*(a+2) := by dsimp only [p,a]; omega
  have hb : n=2*(a+b+2)+1 := by dsimp only [p,b] at *; omega
  have ho : b>0 → a%2=1 → 3≤a := by dsimp only [p,a,b]; omega
  have hden : 0<3*n-2 := by omega
  have hh := (ceilDiv_le_iff_le_mul (b:=n^3) hden).mp le_rfl
  have hr : n^3 ⌈/⌉ (3*n-2) = coreCount n+p := by rw [cube_count n (by omega)]; dsimp only [p]; omega
  rw [hr] at hh
  have hs := odd_budget n p (coreCount n) a b hb ha (by simpa only [if_neg hc,add_zero] using three_core n (by omega)) hh
  rw [hr,ha,show n-2=2*a+2*b+3 by omega]
  convert odd_config a b (coreCount n) ho hs using 1

end TensorRankExterior.Pencils
namespace TensorRankExterior.Tiles

/-- The exterior parts of the active points are prescribed so that the same
points can serve an arbitrarily large number of independent interior rows. -/
def Anchored {D Wh X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    (A B : X → Fin 2 → ℂ) (C : X → Wh → ℂ) : Prop :=
  ∃ ax bx : X → D → ℂ, ∃ ai bi : N → D → ℂ, ∃ ci : N → Wh → ℂ,
    ∃ aq bq : Q → (Fin 2 ⊕ D) → ℂ,
      Holds (fun t => Sum.elim (A t) (ax t)) (fun t => Sum.elim (B t) (bx t)) C ai bi ci aq bq

def Limb {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V] (O : X → Fin 2 → ℂ)
    (C : X → Wh → ℂ) (a : N → D → ℂ) (ci : N → Wh → ℂ) (b : V → D → ℂ) (f : V → Fin 2 → ℂ) : Prop :=
  ∀ T : D → Fin 2 → Wh → ℂ, ∃ u₀ : X → D → ℂ, ∃ u : N → Fin 2 → ℂ, ∃ v : V → Wh → ℂ,
    ∀ i j k, T i j k =
      (∑ t, u₀ t i * (O t j * C t k)) + (∑ t, a t i * (u t j * ci t k)) +
      ∑ t, b t i * (f t j * v t k)

def Paired {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V] (A B : X → Fin 2 → ℂ)
    (C : X → Wh → ℂ) : Prop :=
  ∃ ai bi : N → D → ℂ, ∃ ci : N → Wh → ℂ, ∃ aq bq : V → D → ℂ, ∃ f g : V → Fin 2 → ℂ,
    Limb B C ai ci aq f ∧ Limb A C bi ci bq g

lemma to_pencil {D Wh X N Q : Type} [Fintype X] [Fintype N] [Fintype Q]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ} (h : Anchored (D:=D) (N:=N) (Q:=Q) A B C) :
    PencilFor D Wh X N Q := by
  obtain ⟨ax,bx,ai,bi,ci,aq,bq,hs⟩ := h
  exact ⟨_,_,C,ai,bi,ci,aq,bq,hs⟩

lemma repeat_limb {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V]
    {O : X → Fin 2 → ℂ} {C : X → Wh → ℂ} {a : N → D → ℂ} {ci : N → Wh → ℂ}
    {b : V → D → ℂ} {f : V → Fin 2 → ℂ} (L : Type) [Fintype L] [DecidableEq L] (h : Limb O C a ci b f) :
    Limb O C (fun (z : L×N) (i : L×D) => if z.1=i.1 then a z.2 i.2 else 0) (fun z => ci z.2)
      (fun (z : L×V) (i : L×D) => if z.1=i.1 then b z.2 i.2 else 0) (fun z => f z.2) := by
  classical
  intro T
  choose u₀ u v hv using fun l : L => h fun i j k => T (l,i) j k
  refine ⟨fun t i => u₀ i.1 t i.2,fun t => u t.1 t.2,fun t => v t.1 t.2,?_⟩
  rintro ⟨l,i⟩ j k
  simpa [Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using hv l i j k

lemma repeat_paired {D Wh X N V : Type} [Fintype X] [Fintype N] [Fintype V]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ} (L : Type) [Fintype L] [DecidableEq L]
    (h : Paired (D:=D) (N:=N) (V:=V) A B C) : Paired (D:=L×D) (N:=L×N) (V:=L×V) A B C := by
  obtain ⟨ai,bi,ci,aq,bq,f,g,ha,hb⟩ := h
  exact ⟨_,_,_,_,_,_,_,repeat_limb L ha,repeat_limb L hb⟩

lemma append {D E Wh X N Q M V : Type} [Fintype X] [Fintype N] [Fintype Q] [Fintype M] [Fintype V]
    {A B : X → Fin 2 → ℂ} {C : X → Wh → ℂ}
    (base : Anchored (D:=D) (N:=N) (Q:=Q) A B C) (arms : Paired (D:=E) (N:=M) (V:=V) A B C) :
    Anchored (D:=D⊕E) (N:=N⊕M) (Q:=Q⊕(V⊕V)) A B C := by
  obtain ⟨ax,bx,ai,bi,ci,aq,bq,hs⟩ := base
  obtain ⟨al,bl,cl,rl,sl,f,g,hl,hr⟩ := arms
  let lower (z : Fin 2 ⊕ D) : Fin 2 ⊕ (D⊕E) := z.elim Sum.inl (fun i => Sum.inr (Sum.inl i))
  let extend (t : (Fin 2⊕D) → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ :=
    Sum.elim (fun j => t (Sum.inl j)) (Sum.elim (fun j => t (Sum.inr j)) (fun _ => 0))
  let eg (v : E → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ := insideOnly (Sum.elim (fun _ => 0) v)
  refine ⟨fun t => Sum.elim (ax t) (fun _ => 0),fun t => Sum.elim (bx t) (fun _ => 0),
    Sum.elim (fun t => Sum.elim (ai t) (fun _ => 0)) (fun t => Sum.elim (fun _ => 0) (al t)),
    Sum.elim (fun t => Sum.elim (bi t) (fun _ => 0)) (fun t => Sum.elim (fun _ => 0) (bl t)),Sum.elim ci cl,
    Sum.elim (fun t => extend (aq t)) (Sum.elim (fun t => eg (rl t)) (fun t => outsideOnly (g t))),
    Sum.elim (fun t => extend (bq t)) (Sum.elim (fun t => outsideOnly (f t)) (fun t => eg (sl t))),?_⟩
  intro T
  obtain ⟨u,v,w,ui,vi,wq,hb⟩ := hs fun i j k => T (lower i) (lower j) k
  obtain ⟨y,l,t,hy⟩ := hl fun i j k => T (Sum.inr (Sum.inr i)) (Sum.inl j) k
  obtain ⟨z,r,s,hz⟩ := hr fun j i k => T (Sum.inl i) (Sum.inr (Sum.inr j)) k
  let join (v : (Fin 2⊕D) → ℂ) (r : E → ℂ) : Fin 2 ⊕ (D⊕E) → ℂ :=
    Sum.elim (fun i => v (Sum.inl i)) (Sum.elim (fun i => v (Sum.inr i)) r)
  refine ⟨fun t => join (u t) (y t),fun t => join (v t) (z t),w,Sum.elim ui r,Sum.elim vi l,
    Sum.elim wq (Sum.elim t s),?_⟩
  rintro (i|i) (j|j) k he
  · simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inl i) (Sum.inl j) k (by trivial))
  · cases j with
    | inl j => simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inl i) (Sum.inr j) k (by trivial))
    | inr j => simpa [extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type,mul_comm,mul_assoc,mul_left_comm] using hz j i k
  · cases i with
    | inl i => simpa [lower,extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using (hb (Sum.inr i) (Sum.inl j) k (by trivial))
    | inr i => simpa [extend,eg,join,insideOnly,outsideOnly,Fintype.sum_sum_type] using hy i j k
  · exact False.elim he

end TensorRankExterior.Tiles
namespace TensorRankExterior.Seven

/-- A digit of a row of a nonnegative integer matrix in the given binary width. -/
def digit (a : Array ℕ) (bits i j : ℕ) : ℕ := (a[i]?.getD 0 >>> (bits*j)) % 2^bits

def dot (a b : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => dot a b i j k + a i k * b k j

def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => allBelow p n && p n

lemma allBelow_iff (p : ℕ → Bool) (n : ℕ) :
    allBelow p n = true ↔ ∀ i<n, p i=true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨h,k⟩ i hi
      by_cases he : i=n
      · simpa [he] using k
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

lemma dot_fin (a b : ℕ → ℕ → ℕ) (i j n : ℕ) :
    dot a b i j n = ∑ t : Fin n, a i t.val * b t.val j := by
  induction n with
  | zero => simp [dot]
  | succ n ih => rw [dot,Fin.sum_univ_castSucc,ih]; rfl

def valid (a b : ℕ → ℕ → ℕ) (m : ℕ) :=
  allBelow (fun i => allBelow (fun j => dot a b i j m % 7 == (if i=j then 1 else 0)) m) m

lemma valid_entry {a b : ℕ → ℕ → ℕ} {m : ℕ} (hv : valid a b m = true) (i j : Fin m) :
    dot a b i.val j.val m % 7 = (if i=j then 1 else 0) := by
  obtain h := (allBelow_iff _ _).mp ((allBelow_iff _ _).mp hv i.val i.isLt) j.val j.isLt
  simpa [Fin.ext_iff] using (beq_iff_eq.mp h)

lemma lift_rank {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
    (A : Matrix I K ℤ) (B : Matrix K I ℤ)
    (hab : A.map (Int.castRingHom (ZMod 7)) * B.map (Int.castRingHom (ZMod 7)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let D := A*B
  have h7 : ((D.det : ℤ) : ZMod 7) = 1 := by
    change (Int.castRingHom (ZMod 7)) D.det = 1
    rw [RingHom.map_det,RingHom.mapMatrix_apply,show D=A*B from rfl,Matrix.map_mul,hab,Matrix.det_one]
  have hn : D.det≠0 := by
    intro he
    rw [he, Int.cast_zero] at h7
    exact (by decide : (0 : ZMod 7) ≠ 1) h7
  have hu : IsUnit (D.map (Int.castRingHom ℂ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    change (D.det : ℂ) ≠ 0
    exact_mod_cast hn
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  intro y
  obtain ⟨z,hz⟩ := hs y
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul]
  exact hz

lemma certified {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] {m : ℕ}
    (M : Matrix I K ℤ) (rows : I ≃ Fin m) (sel : Fin m → K) (a b : ℕ → ℕ → ℕ)
    (ha : ∀ i j : Fin m, M (rows.symm i) (sel j) = (a i.val j.val : ℤ))
    (hv : valid a b m = true) : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  let A : Matrix I (Fin m) ℤ := fun i j => M i (sel j)
  let B : Matrix (Fin m) I ℤ := fun t i => b t.val (rows i).val
  have hA (i : I) (t : Fin m) : A i t = (a (rows i).val t.val : ℤ) := by
    simpa only [A,Equiv.symm_apply_apply] using ha (rows i) t
  have mod7 : A.map (Int.castRingHom (ZMod 7)) * B.map (Int.castRingHom (ZMod 7)) = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ t : Fin m, ((A i t : ℤ) : ZMod 7) * (((b t.val (rows j).val : ℕ) : ℤ) : ZMod 7)) = _
    simp only [hA,Int.cast_natCast]
    have H := congrArg (fun t : ℕ => (t : ZMod 7)) (valid_entry hv (rows i) (rows j))
    simpa only [ZMod.natCast_mod,dot_fin,Nat.cast_sum,Nat.cast_mul,Equiv.apply_eq_iff_eq,
      apply_ite,Nat.cast_one,Nat.cast_zero] using H
  have hsmall := lift_rank A B mod7
  let E : Matrix K (Fin m) ℂ := fun k i => if k=sel i then 1 else 0
  have hcols : M.map (Int.castRingHom ℂ) * E = A.map (Int.castRingHom ℂ) := by
    ext i t
    rw [Matrix.mul_apply]
    change (∑ k : K, ((M i k : ℤ) : ℂ) * (if k=sel t then 1 else 0)) = ((M i (sel t) : ℤ) : ℂ)
    simp [mul_ite,Finset.sum_ite_eq']
  intro y
  obtain ⟨z,hz⟩ := hsmall y
  refine ⟨E.mulVec z,?_⟩
  rw [Matrix.mulVec_mulVec,hcols]
  exact hz

def prodFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A×B ≃ Fin (a*b) :=
  (ea.prodCongr eb).trans finProdFinEquiv
def sumFin {A B : Type} {a b : ℕ} (ea : A ≃ Fin a) (eb : B ≃ Fin b) : A⊕B ≃ Fin (a+b) :=
  (Equiv.sumCongr ea eb).trans finSumFinEquiv

/-- Row order is the two outer rows followed by the two outer columns in
each interior row. The third index varies fastest. -/
def rowEquiv (d w : ℕ) : Pencils.Rows (Fin d) (Fin w) ≃ Fin (2*((2+d)*w)+d*(2*w)) :=
  let e : Pencils.Rows (Fin d) (Fin w) ≃ (Fin 2 × Pencils.Coord (Fin d) × Fin w) ⊕ (Fin d × Fin 2 × Fin w) :=
    { toFun := fun z => match z with
        | ⟨(Sum.inl i,j,k),_⟩ => Sum.inl (i,j,k)
        | ⟨(Sum.inr i,Sum.inl j,k),_⟩ => Sum.inr (i,j,k)
        | ⟨(Sum.inr _,Sum.inr _,_),h⟩ => False.elim h
      invFun := Sum.elim (fun z => ⟨(Sum.inl z.1,z.2.1,z.2.2),by cases z.2.1 <;> trivial⟩)
        (fun z => ⟨(Sum.inr z.1,Sum.inl z.2.1,z.2.2),by trivial⟩)
      left_inv := by rintro ⟨⟨i,j,k⟩,h⟩; cases i <;> cases j <;> first | rfl | exact False.elim h
      right_inv := by rintro (⟨i,j,k⟩|⟨i,j,k⟩) <;> rfl }
  e.trans (sumFin (prodFin (Equiv.refl _) (prodFin finSumFinEquiv (Equiv.refl _)))
    (prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))))

def colEquiv (d w x n q : ℕ) : Pencils.Cols (Fin d) (Fin w) (Fin x) (Fin n) (Fin q) ≃
    Fin (x*((2+d)+((2+d)+w))+(n*(2+2)+q*w)) :=
  sumFin (prodFin (Equiv.refl _) (sumFin finSumFinEquiv (sumFin finSumFinEquiv (Equiv.refl _))))
    (sumFin (prodFin (Equiv.refl _) finSumFinEquiv) (prodFin (Equiv.refl _) (Equiv.refl _)))

end TensorRankExterior.Seven
namespace TensorRankExterior.Seven

open TensorRankExterior.Pencils TensorRankExterior.Tiles

def table {m n : ℕ} (v : Array ℕ) (i : Fin m) (j : Fin n) : ℤ := (v[i.val*n+j.val]?.getD 0 : ℕ)
def outA {x : ℕ} (t : Fin x) (i : Fin 2) : ℤ := if i=0 then 1 else (t.val+1 : ℕ)
def outB {x : ℕ} (t : Fin x) (i : Fin 2) : ℤ := if i=0 then 1 else (#[1,2,4,3][t.val]?.getD 0 : ℕ)
def basisC {x w : ℕ} (t : Fin x) (k : Fin w) : ℤ := if t.val=k.val then 1 else 0

def Room (d w x n q : ℕ) : Prop :=
  Anchored (D:=Fin d) (N:=Fin n) (Q:=Fin q) (fun (t : Fin x) i => (outA t i : ℂ))
    (fun t j => (outB t j : ℂ)) (fun t (k : Fin w) => (basisC t k : ℂ))

def Wing (d w x n v : ℕ) : Prop :=
  Paired (D:=Fin d) (N:=Fin n) (V:=Fin v) (fun (t : Fin x) i => (outA t i : ℂ))
    (fun t j => (outB t j : ℂ)) (fun t (k : Fin w) => (basisC t k : ℂ))

lemma pencil_cast {D Wh X N Q : Type} [DecidableEq D] [DecidableEq Wh]
    (a b : X → Coord D → ℤ) (c : X → Wh → ℤ) (ai bi : N → D → ℤ) (ci : N → Wh → ℤ)
    (aq bq : Q → Coord D → ℤ) :
    (Pencils.matrix a b c ai bi ci aq bq).map (Int.castRingHom ℂ) =
      Pencils.matrix (fun t i => (a t i : ℂ)) (fun t i => (b t i : ℂ)) (fun t i => (c t i : ℂ))
        (fun t i => (ai t i : ℂ)) (fun t i => (bi t i : ℂ)) (fun t i => (ci t i : ℂ))
        (fun t i => (aq t i : ℂ)) (fun t i => (bq t i : ℂ)) := by
  ext ⟨⟨i,j,h⟩,hz⟩ z
  rcases z with ⟨t,e|e|e⟩ | ⟨t,e|e⟩ | ⟨t,e⟩ <;> cases i <;> cases j <;>
    simp only [Pencils.matrix, Matrix.map_apply, Sum.elim_inl,Sum.elim_inr] <;> split <;> simp

lemma certified_room {d w x n q : ℕ} (ax bx : Fin x → Fin d → ℤ)
    (ai bi : Fin n → Fin d → ℤ) (ci : Fin n → Fin w → ℤ) (aq bq : Fin q → Coord (Fin d) → ℤ)
    (h : Function.Surjective ((Pencils.matrix (fun t => Sum.elim (outA t) (ax t))
      (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq).map (Int.castRingHom ℂ)).mulVec) :
    Room d w x n q := by
  classical
  refine ⟨fun t i => ax t i,fun t i => bx t i,fun t i => ai t i,fun t i => bi t i,
    fun t k => ci t k,fun t i => aq t i,fun t i => bq t i,?_⟩
  apply (holds_iff _ _ _ _ _ _ _ _).mpr
  rw [pencil_cast] at h
  have he (a : Fin 2 → ℤ) (b : Fin d → ℤ) :
      (fun i => ((Sum.elim a b i : ℤ) : ℂ)) = Sum.elim (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) := by
    funext i
    cases i <;> rfl
  have hOut (op : Fin x → Fin 2 → ℤ) (ip : Fin x → Fin d → ℤ) :
      (fun t i => ((Sum.elim (op t) (ip t) i : ℤ) : ℂ)) =
        (fun t => Sum.elim (fun i => (op t i : ℂ)) (fun i => (ip t i : ℂ))) := by
    funext t
    exact he (op t) (ip t)
  rw [hOut outA ax,hOut outB bx] at h
  exact h

abbrev ArmCols (D Wh X N V : Type) := (X × D) ⊕ ((N × Fin 2) ⊕ (V × Wh))
def armMatrix {D Wh X N V : Type} [DecidableEq D] [DecidableEq Wh] (O : X → Fin 2 → ℤ) (C : X → Wh → ℤ)
    (a : N → D → ℤ) (ci : N → Wh → ℤ) (b : V → D → ℤ) (f : V → Fin 2 → ℤ) :
    Matrix (D × Fin 2 × Wh) (ArmCols D Wh X N V) ℤ
  | (i,j,k),Sum.inl (t,h) => if h=i then O t j*C t k else 0
  | (i,j,k),Sum.inr (Sum.inl (t,h)) => if h=j then a t i*ci t k else 0
  | (i,j,k),Sum.inr (Sum.inr (t,h)) => if h=k then b t i*f t j else 0

lemma certified_limb {D Wh X N V : Type} [Fintype D] [Fintype Wh] [Fintype X] [Fintype N] [Fintype V]
    [DecidableEq D] [DecidableEq Wh] (O : X → Fin 2 → ℤ) (C : X → Wh → ℤ)
    (a : N → D → ℤ) (ci : N → Wh → ℤ) (b : V → D → ℤ) (f : V → Fin 2 → ℤ)
    (h : Function.Surjective ((armMatrix O C a ci b f).map (Int.castRingHom ℂ)).mulVec) :
    Limb (fun t i => (O t i : ℂ)) (fun t k => (C t k : ℂ)) (fun t i => (a t i : ℂ))
      (fun t k => (ci t k : ℂ)) (fun t i => (b t i : ℂ)) (fun t j => (f t j : ℂ)) := by
  intro T
  obtain ⟨y,hy⟩ := h fun z => T z.1 z.2.1 z.2.2
  refine ⟨fun t i => y (Sum.inl (t,i)),fun t j => y (Sum.inr (Sum.inl (t,j))),
    fun t k => y (Sum.inr (Sum.inr (t,k))),?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : ArmCols D Wh X N V, ((armMatrix O C a ci b f (i,j,k) z : ℤ) : ℂ) * y z) = _
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,armMatrix,apply_ite,Finset.sum_ite_eq',
    mul_comm,mul_assoc,add_assoc]

def armRows (d w : ℕ) : Fin d × Fin 2 × Fin w ≃ Fin (d*(2*w)) :=
  prodFin (Equiv.refl _) (prodFin (Equiv.refl _) (Equiv.refl _))
def armCols (d w x n v : ℕ) : ArmCols (Fin d) (Fin w) (Fin x) (Fin n) (Fin v) ≃ Fin (x*d+(n*2+v*w)) :=
  sumFin (prodFin (Equiv.refl _) (Equiv.refl _)) (sumFin (prodFin (Equiv.refl _) (Equiv.refl _))
    (prodFin (Equiv.refl _) (Equiv.refl _)))

end TensorRankExterior.Seven
namespace TensorRankExterior.Seven

open TensorRankExterior.Pencils TensorRankExterior.Tiles

namespace ActiveFour

def ax : Fin 4 → Fin 2 → ℤ := table #[4, 2, 4, 3, 4, 5, 5, 4]
def bx : Fin 4 → Fin 2 → ℤ := table #[2, 0, 1, 4, 0, 4, 3, 0]
def ai : Fin 1 → Fin 2 → ℤ := table #[4, 4]
def bi : Fin 1 → Fin 2 → ℤ := table #[3, 2]
def ci : Fin 1 → Fin 4 → ℤ := table #[2, 2, 3, 5]
def aq (t : Fin 1) (j : Coord (Fin 2)) : ℤ := table #[5, 1, 0, 4] t (finSumFinEquiv j)
def bq (t : Fin 1) (j : Coord (Fin 2)) : ℤ := table #[3, 2, 4, 5] t (finSumFinEquiv j)

def M : Matrix (Rows (Fin 2) (Fin 4)) (Cols (Fin 2) (Fin 4) (Fin 4) (Fin 1) (Fin 1)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (ax t)) (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq

def original : Array ℕ := #[
  0xf0000000000000100000000000000000001000000000000000000010000000000000000000000000100000001,
  0xf000000000000010000000000000000000100000000000000000000000000010000000100000100000000000000,
  0xf00000000000001000000000000000000000000000001000000010001000000000000000000010000000000000000,
  0xf0000000000000000000000000100000001010000000000000000000100000000000000000001000000000000000000,
  0xa0000000000000300000000000000000004000000000000000000020000000000000000000000010000000001,
  0xa000000000000030000000000000000000400000000000000000000000001000000000200000100000000000000,
  0xa00000000000003000000000000000000000000000100000000040002000000000000000000010000000000000000,
  0xa0000000000000000000000010000000003040000000000000000000200000000000000000001000000000000000000,
  0x140000000600000300000000000000000000000000000000000000010000000000000000000000000000000002,
  0x14000000000600030000000000000000000000000000000000000000000100000000000100000200000000000000,
  0x1400000000000903000000000000000000000000010000000000000001000000000000000000020000000000000000,
  0x140000000000000f00000000000000000003000000000000000000000100000000000000000002000000000000000000,
  0x190000000400000000000000000000000004000000000000000000040000000000000000000001000000000000,
  0x19000000000400000000000000000000000400000000000000000000000000000000000400000000000000000000,
  0x1900000000000600000000000000000000000000000000000000040004000000000000000000000000000000000000,
  0x190000000000000a00000001000000000000040000000000000000000400000000000000000000000000000000000000,
  0x30000000000000400000000000000000003000000000000000000020000000000000000000000000100000100,
  0x3000000000000040000000000000000000300000000000000000000000000020000010000000100000000000000,
  0x300000000000004000000000000000000000000000003000001000002000000000000000000010000000000000000,
  0x30000000000000000000000000400000100030000000000000000000200000000000000000001000000000000000000,
  0x20000000000000c0000000000000000000c000000000000000000040000000000000000000000010000000100,
  0x20000000000000c0000000000000000000c00000000000000000000000002000000020000000100000000000000,
  0x20000000000000c000000000000000000000000000300000004000004000000000000000000010000000000000000,
  0x200000000000000000000000400000003000c0000000000000000000400000000000000000001000000000000000000,
  0x40000060000000c00000000000000000000000000000000000000020000000000000000000000000000000200,
  0x40000000600000c0000000000000000000000000000000000000000000200000000010000000200000000000000,
  0x40000000009000c000000000000000000000000030000000000000002000000000000000000020000000000000000,
  0x400000000000f0000000000000000000300000000000000000000000200000000000000000002000000000000000000,
  0x5000004000000000000000000000000000c000000000000000000080000000000000000000001000000000000,
  0x5000000040000000000000000000000000c00000000000000000000000000000000040000000000000000000000,
  0x500000000060000000000000000000000000000000000000004000008000000000000000000000000000000000000,
  0x500000000000a00000000040000000000000c0000000000000000000800000000000000000000000000000000000000,
  0x8000000000500000000000000000004000000000000000000040000000000000000000000000400010000,
  0x8000000050000000000000000000400000000000000000000000000040001000000000400000000000000,
  0xc000005000000000000000000000000000004000100000004000000000000000000040000000000000000,
  0x14000000000000000500010000040000000000000000000400000000000000000004000000000000000000,
  0x800000000000f00000000000000000010000000000000000000080000000000000000000000040000010000,
  0x8000000000f0000000000000000001000000000000000000000000004000002000000000400000000000000,
  0xc0000000f000000000000000000000000000400000400000008000000000000000000040000000000000000,
  0x1400000000000000050000030000100000000000000000000800000000000000000004000000000000000000,
  0xc0008000000000400000000000000000005000000000000000000030000000000000000000000000201000000,
  0xc000008000000040000000000000000000500000000000000000000000000030100000000000200000000000000,
  0xc0000000c000004000000000000000000000000000005010000000003000000000000000000020000000000000000,
  0xc0000000014000000000000000401000000050000000000000000000300000000000000000002000000000000000000,
  0x80800000000000c00000000000000000014000000000000000000060000000000000000000000020001000000,
  0x80008000000000c0000000000000000001400000000000000000000000003000200000000000200000000000000,
  0x800000c0000000c000000000000000000000000000500040000000006000000000000000000020000000000000000,
  0x80000001400000000000000040003000000140000000000000000000600000000000000000002000000000000000000]
def rightInverse : Array ℕ := #[
  0x50401036005300266026501230646064305460341014501,
  0x32202355052604555005334461415231600151012051362,
  0x36202251015405315001323563635623600353632053344,
  0x51001512065102226052556334566146302664261036530,
  0x54201656030301066066564232246444301462641014551,
  0x11003504066202144064155624454105201544553015133,
  0x11103564065202244014156624454155200544153025133,
  0x4000604043206440464016603350565061505150165046,
  0x60004003001500636023102160121022305240521022502,
  0x354051603032501516041564632206443303362351044554,
  0x12003303030501034203140121024002250246023102110,
  0x26006205021603651125252443111021425114516321232,
  0x56001201066403116151565533636553362362231153505,
  0x46005302022103522642414310262346113625365246414,
  0x63004104060202043204650650053105510534054205620,
  0x54001604064202346614551634456515356564651615561,
  0x53001103055504236333523136526232364264421132553,
  0x43305142040106022062412315462366101625565046420,
  0x10003004006200144054405640653055202520254055405,
  0x200010005000600000000000400020000000000000000000,
  0x41005501565412211031053524532133604304433033033,
  0x13003101145436213031613505533333404335435033623,
  0x40005003004510335013201150422012006210620012001,
  0x61005506465352264036253254546134504414442034033,
  0x6000200010005000000120043005600500043002000040,
  0x23006102243166421062216355364366301615163066426,
  0x16003205214665351015421433415611406133616011241,
  0x300040004000300010004000400020006000300020006,
  0x1000505022603550345024403210141013103310441064,
  0x123046100045006261036213145501334404415466035223,
  0x551061501062402506043554634216140303064301041534,
  0x156041205012605506040524233226640303663351042544,
  0x641035500060102042001450614002105100024015004430,
  0x436032205011605655021322463165621605253562024342,
  0x165044402021103623024642456143526505036554026612,
  0x356051203012505526041524633206646303263361044544,
  0x140045001003400432062406510302063101620165066406,
  0x52301346056304166036532231146224304461541044560,
  0x4000602005100220132003306560536054600460436003,
  0x30002005004600352015001410412011106100613011501,
  0x64004603031501633023662152123422505232524022652,
  0x55001406022303566046544236246544303466341044514,
  0x65004400025003203030643056503530504036404030613,
  0x56001203010505036003520133026602300263021002540,
  0x25606411026403111031241546431513404316636023210,
  0x3064502330213021101420212036203620212021,
  0x1205460211031103540531033404340431033103,
  0x231012503064502355010351064405111606054652016331]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 55]
def pick (t : Fin 48) := (colEquiv 2 4 4 1 1).symm (⟨(pivots[t.val]?.getD 0) % 56, Nat.mod_lt _ (by decide)⟩ : Fin 56)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 48), M ((rowEquiv 2 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 48 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (rowEquiv 2 4) pick _ _ matrix_entries inverse_entries

lemma spans : Room 2 4 4 1 1 := certified_room ax bx ai bi ci aq bq rank

end ActiveFour

namespace ActiveThreeZero

def ax : Fin 3 → Fin 0 → ℤ := table #[]
def bx : Fin 3 → Fin 0 → ℤ := table #[]
def ai : Fin 0 → Fin 0 → ℤ := table #[]
def bi : Fin 0 → Fin 0 → ℤ := table #[]
def ci : Fin 0 → Fin 3 → ℤ := table #[]
def aq (t : Fin 0) (j : Coord (Fin 0)) : ℤ := table #[] t (finSumFinEquiv j)
def bq (t : Fin 0) (j : Coord (Fin 0)) : ℤ := table #[] t (finSumFinEquiv j)

def M : Matrix (Rows (Fin 0) (Fin 3)) (Cols (Fin 0) (Fin 3) (Fin 3) (Fin 0) (Fin 0)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (ax t)) (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq

def original : Array ℕ := #[
  0x10000000000010001,
  0x100010001000000,
  0x101000000000100000000,
  0x20000000000000001,
  0x20001000000,
  0x402000000000100000000,
  0x20000000000010100,
  0x201000001000000,
  0x10002000000000100000000,
  0x40000000000000100,
  0x2000001000000,
  0x40004000000000100000000]
def rightInverse : Array ℕ := #[
  0x5002003005,
  0x4004004003,
  0x1006005002,
  0x10050050040,
  0x500100400500,
  0x30010050050,
  0x10010050,
  0x30010040060,
  0x1006006001,
  0x300200400500,
  0x600400600500,
  0x300300200600]
def pivots : Array ℕ := #[0, 1, 2, 5, 6, 7, 8, 9, 11, 13, 14, 15]
def pick (t : Fin 12) := (colEquiv 0 3 3 0 0).symm (⟨(pivots[t.val]?.getD 0) % 21, Nat.mod_lt _ (by decide)⟩ : Fin 21)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 12), M ((rowEquiv 0 3).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 12 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (rowEquiv 0 3) pick _ _ matrix_entries inverse_entries

lemma spans : Room 0 3 3 0 0 := certified_room ax bx ai bi ci aq bq rank

end ActiveThreeZero

namespace ActiveThreeMixed

def ax : Fin 3 → Fin 2 → ℤ := table #[5, 5, 6, 0, 5, 3]
def bx : Fin 3 → Fin 2 → ℤ := table #[6, 5, 6, 1, 0, 2]
def ai : Fin 1 → Fin 2 → ℤ := table #[2, 5]
def bi : Fin 1 → Fin 2 → ℤ := table #[3, 3]
def ci : Fin 1 → Fin 3 → ℤ := table #[3, 1, 4]
def aq (t : Fin 2) (j : Coord (Fin 2)) : ℤ := table #[2, 0, 4, 2, 0, 1, 1, 0] t (finSumFinEquiv j)
def bq (t : Fin 2) (j : Coord (Fin 2)) : ℤ := table #[4, 1, 4, 1, 6, 4, 3, 1] t (finSumFinEquiv j)

def M : Matrix (Rows (Fin 2) (Fin 3)) (Cols (Fin 2) (Fin 3) (Fin 3) (Fin 1) (Fin 2)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (ax t)) (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq

def original : Array ℕ := #[
  0x800000000000100000000000000000100000000000000000000000100000001,
  0x80000000000010000000000000000000000000100000001000100000000000000,
  0x8000000000000000000000100000001010000000000000000010000000000000000,
  0x200000000000400000000000000000200000000000000000000010000000001,
  0x20000000000040000000000000000000000010000000002000100000000000000,
  0x2000000000000000000010000000004020000000000000000010000000000000000,
  0x800000009000000000000000000000600000000000000000001000000000006,
  0x80000000003000000000000000000000001000000000006000600000000000000,
  0x800000000000c000001000000000000060000000000000000060000000000000000,
  0x200000009000200000000000000000100000000000000000000000000000005,
  0x20000000003020000000000000000000000000000000001000500000000000000,
  0x200000000000c000000000000000002010000000000000000050000000000000000,
  0x600000000000000000300000000000000000200000000000000000000000100000100,
  0x30000000000000000000000000200000100000100000000000000,
  0x60000000000000000000000000300000100020000000000000000010000000000000000,
  0x400000000000000000c00000000000000000400000000000000000000010000000100,
  0xc0000000000000000000000020000000200000100000000000000,
  0x40000000000000000000000030000000400040000000000000000010000000000000000,
  0x300000000000900000000000000000000000c00000000000000000001000000000600,
  0x300000000000000000000000002000000000600000600000000000000,
  0x30000000000000c000000030000000000000c0000000000000000060000000000000000,
  0x100000000000900000600000000000000000200000000000000000000000000000500,
  0x300060000000000000000000000000000000100000500000000000000,
  0x10000000000000c00000000000000000200020000000000000000050000000000000000,
  0x600001000060000000500000000000000000600000000000000000000000500010000,
  0x100000020000050000000000000000000000000600010000000500000000000000,
  0x60010000000080000000000000500010000060000000000000000050000000000000000,
  0x400000406000000001400000000000000000c00000000000000000000050000010000,
  0x40002000000140000000000000000000000060000020000000500000000000000,
  0x400040000080000000000000500000400000c0000000000000000050000000000000000,
  0x8000f0000000300000000000000000000000000000000000000000501000000,
  0x80000050000030000000000000000000000000001000000000500000000000000,
  0x8000000140000000000000301000000000000000000000000050000000000000000,
  0x20f000000000c00000000000000000000000000000000000000050001000000,
  0x200050000000c0000000000000000000000000002000000000500000000000000,
  0x2000014000000000000030004000000000000000000000000050000000000000000]
def rightInverse : Array ℕ := #[
  0x506101333214510036313603653011311410,
  0x260620433514201001464120102006452341,
  0x561126354244534024321624614033312402,
  0x156342245662143052226442465045202556,
  0x356241640460345052623542566045602151,
  0x663424545162651013541324343054532221,
  0x202605445562260041463105123060464362,
  0x10050010050000000050040000000050040,
  0x541166541166530425304661610232040212,
  0x46061046061010002013046060005020055,
  0x35012035012030064016025030023010043,
  0x145362205612160064216455410023250553,
  0x623444563124650031555323340016530256,
  0x41066041066020045004021020062040032,
  0x32015032015040013021002040054000014,
  0x15052015052060034036055030023020023,
  0x232615405502234021461111113036426356,
  0x553144553144520161505543630426150536,
  0x223634223634450611305133640356320546,
  0x421536421536250515404231640652520342,
  0x601406351346140055244401360042340342,
  0x163424413554340151535223360446420616,
  0x542165542165530223201362210134340514,
  0x416551416551060342103356520565110025,
  0x622435622435150413001532440354120244,
  0x624433506101621060544335336020562213,
  0x30010030010000000050040000000000000,
  0x35012035012040054006015060043030063,
  0x33014033014040051005013060046030066,
  0x325232645462310034636535550013650103,
  0x633414543164620061555313330026510246,
  0x543164300200544055313663663042353425,
  0x20030020030040030030000060010030030,
  0x465522465522210134106625150413060553,
  0x621436503104623065540334334022561212,
  0x600400600400400300200500200500200200]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42]
def pick (t : Fin 36) := (colEquiv 2 3 3 1 2).symm (⟨(pivots[t.val]?.getD 0) % 43, Nat.mod_lt _ (by decide)⟩ : Fin 43)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 36), M ((rowEquiv 2 3).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 36 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (rowEquiv 2 3) pick _ _ matrix_entries inverse_entries

lemma spans : Room 2 3 3 1 2 := certified_room ax bx ai bi ci aq bq rank

end ActiveThreeMixed

namespace IdleFourOne

def ax : Fin 0 → Fin 2 → ℤ := table #[]
def bx : Fin 0 → Fin 2 → ℤ := table #[]
def ai : Fin 7 → Fin 2 → ℤ := table #[1, 3, 5, 1, 3, 5, 4, 1, 3, 0, 4, 3, 1, 6]
def bi : Fin 7 → Fin 2 → ℤ := table #[6, 2, 6, 5, 0, 5, 6, 2, 1, 0, 0, 2, 1, 2]
def ci : Fin 7 → Fin 4 → ℤ := table #[0, 2, 0, 6, 0, 0, 2, 5, 1, 6, 5, 6, 1, 2, 4, 6, 5, 0, 4, 3, 5, 4, 5, 5, 5, 0, 5, 0]
def aq (t : Fin 5) (j : Coord (Fin 2)) : ℤ := table #[0, 6, 5, 2, 3, 2, 0, 0, 6, 0, 3, 5, 5, 4, 1, 1, 3, 0, 4, 3] t (finSumFinEquiv j)
def bq (t : Fin 5) (j : Coord (Fin 2)) : ℤ := table #[0, 2, 5, 2, 1, 6, 1, 1, 6, 1, 0, 1, 3, 5, 0, 2, 6, 2, 5, 2] t (finSumFinEquiv j)

def M : Matrix (Rows (Fin 2) (Fin 4)) (Cols (Fin 2) (Fin 4) (Fin 0) (Fin 7) (Fin 5)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (ax t)) (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq

def original : Array ℕ := #[
  0x120000000f00000024000000030000000000000000000000000000000000000000000000000000000000000000,
  0x120000000f0000002400000003000000000000000000000000000000000000000000000000000000000000000000,
  0x120000000f000000240000000300000000000000000000000000000000000000000000000000000000000000000000,
  0x120000000f00000024000000030000000000000000000000000000000000000000000000000000000000000000000000,
  0x60000001900000006000000120000000000000000000000000000000000000000000000000000000000000000,
  0x6000000190000000600000012000000000000000000000000000000000000000000000000000000000000000000,
  0x600000019000000060000001200000000000000000000000000000000000000000000000000000000000000000000,
  0x60000001900000006000000120000000000000000000000000000000000000000000000000000000000000000000000,
  0xf0000000000000000000000030000000000000005000000000000000500000006000000000000000000000000,
  0xf00000000000000000000000300000000000000000000000000000000000000000c00000000000000000000000c,
  0xf00000000000000000000000300000000000000000005000000000000000400000018000000000000000c00000000,
  0xf0000000000000000000000030000000000000000000000000000000000000300000024000000000000001e00000024,
  0x60000000a0000000600000003000000000000000a0000000a0000000000000002000000050000000000000000,
  0x60000000a00000006000000030000000000000000000000000800000000000000040000001e0000000000000004,
  0x60000000a00000006000000030000000000000000000a0000000a0000000000000008000000190000000a00000000,
  0x60000000a000000060000000300000000000000000000000000000a000000000000000c0000001e000000190000000c,
  0xc00000000000000020000000000000000000000000000000000000000000000000000000000000000,
  0xc0000000000000002000000000000000000000000000000000000000000000000000000000000000000,
  0xc000000000000000200000000000000000000000000000000000000000000000000000000000000000000,
  0xc00000000000000020000000000000000000000000000000000000000000000000000000000000000000000,
  0x14000000000000000c0000000c00000000000000000000000000000000000000000000000000000000,
  0x14000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000,
  0x14000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000,
  0x14000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000,
  0x20000001e00000500000000000000050000000600000000000000000000000000,
  0x20000001e0000000000000000000000000000000c00000000000000000000000c00,
  0x20000001e0000000005000000000000000400000018000000000000000c0000000000,
  0x20000001e000000000000000000000000000300000024000000000000001e0000002400,
  0x800000000000000020000000c00000a0000000a000000000000000200000005000000000000000000,
  0x800000000000000020000000c000000000000000800000000000000040000001e000000000000000400,
  0x800000000000000020000000c000000000a0000000a0000000000000008000000190000000a0000000000,
  0x800000000000000020000000c0000000000000000000a000000000000000c0000001e000000190000000c00,
  0x18000000030000001200000000000000000005000000140000000f000000040000000300000000000000000000,
  0x18000000030000001200000000000000000000000000001000000000000000080000001200000000000000020000,
  0x180000000300000012000000000000000000000005000000140000000c000000100000000f0000000a000000000000,
  0x180000000300000012000000000000000000000000000000001400000009000000180000001200000019000000060000,
  0x80000000500000003000000000000000a05000000140000000f00000004000000030000000000000000000000,
  0x80000000500000003000000000000000a0000000000100000000000000008000000120000000000000002000000,
  0x80000000500000003000000000000000a000005000000140000000c000000100000000f0000000a00000000000000,
  0x80000000500000003000000000000000a00000000000000140000000900000018000000120000001900000006000000,
  0x12000000030000001e0000000000000000001e0000000f00000000000000010000000500000000000000000000,
  0x12000000030000001e00000000000000000000000000000c00000000000000020000001e00000000000000060000,
  0x12000000030000001e00000000000000000000001e0000000f00000000000000040000001900000002000000000000,
  0x12000000030000001e000000000000000000000000000000000f00000000000000060000001e00000005000000120000,
  0x6000000050000000500000000000000041e0000000f0000000000000001000000050000000000000000000000,
  0x60000000500000005000000000000000400000000000c00000000000000020000001e0000000000000006000000,
  0x60000000500000005000000000000000400001e0000000f0000000000000004000000190000000200000000000000,
  0x600000005000000050000000000000004000000000000000f00000000000000060000001e0000000500000012000000]
def rightInverse : Array ℕ := #[
  0x2040000345250313666563523400456431501042661,
  0x60503062516164344645530432146621023244435661035,
  0x60550002516453210232444460605620000000015554343,
  0x540100003666000030626555011026012046411133646061,
  0x20405033452432500000000134431533255643303066331,
  0x50302044325345232556433261114460000000023126535,
  0x40160326134355400000000261124140000000012421140,
  0x663005035363432500000000261163310000000035545064,
  0x6050000251610232444142162502261110044365251,
  0x40106056134251652530655431301114015122230222145,
  0x20425123452643350313666620263645031366614264540,
  0x241001021242526100000000241362330000000021154025,
  0x1344516626113255,
  0x10206055261251613445166134454650000000062364121,
  0x10263315261506400000000452216430000000062361643,
  0x603204014121613400000000452253630000000014465363,
  0x3060000164340151222421431602104246042632144,
  0x50305034325432521042460602666454015122222516266,
  0x60533552516000130626555604141133062655542562050,
  0x325302042510345210232444353053101023244402153645,
  0x2312315346246236,
  0x60504012516613423123153402621150000000030511643,
  0x20010000435520464111214265361023244420204252,
  0x220505030030432520464111655532626054533350226344,
  0x30605031643432500000000516612425166010223122516,
  0x10200005261000051660102653562360000000025161140,
  0x30654361643404660545333444516463062655540546151,
  0x533400006555000060545333461423404015122266512446,
  0x20403063452164350313666620552255031366603526052,
  0x6050000251610232444145162403062655560611314,
  0x10205035261432540151222133612514015122213152546,
  0x10200005261000060545333610152155031366633330625,
  0x10205035261432560545333310161156054533305613061,
  0x3060000164340151222421431105031366630344542,
  0x40106056134251620464111405340642046411145461623,
  0x40100006134000030626555540451466054533355550316,
  0x50304014325613420464111150525502046411104261020,
  0x1020000526160545333635615104015122210266413,
  0x60502042516345230626555604163263062655565625431,
  0x60500002516000010232444460605622046411154442152,
  0x10205035261432560545333310161116054533305613061,
  0x3060000164340151222421431405031366630344542,
  0x40106056134251620464111405343642046411145461623,
  0x40100006134000030626555540411466054533355550316,
  0x30601021643526140151222230343334015122201412041,
  0x2040000345250313666563523501023244420055136,
  0x50304014325613460545333501252456054533356543262,
  0x50300004325000020464111150533544015122261115234]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
def pick (t : Fin 48) := (colEquiv 2 4 0 7 5).symm (⟨(pivots[t.val]?.getD 0) % 48, Nat.mod_lt _ (by decide)⟩ : Fin 48)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 48), M ((rowEquiv 2 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 48 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (rowEquiv 2 4) pick _ _ matrix_entries inverse_entries

lemma spans : Room 2 4 0 7 5 := certified_room ax bx ai bi ci aq bq rank

end IdleFourOne

namespace IdleFourThree

def ax : Fin 0 → Fin 2 → ℤ := table #[]
def bx : Fin 0 → Fin 2 → ℤ := table #[]
def ai : Fin 5 → Fin 2 → ℤ := table #[3, 5, 5, 5, 1, 0, 6, 0, 2, 2]
def bi : Fin 5 → Fin 2 → ℤ := table #[5, 3, 3, 6, 6, 5, 2, 2, 6, 1]
def ci : Fin 5 → Fin 4 → ℤ := table #[5, 2, 0, 2, 6, 4, 0, 3, 1, 0, 5, 2, 0, 2, 5, 3, 3, 3, 1, 4]
def aq (t : Fin 7) (j : Coord (Fin 2)) : ℤ := table #[2, 0, 4, 2, 0, 1, 1, 0, 4, 1, 4, 1, 6, 4, 3, 1, 3, 4, 4, 0, 2, 3, 4, 0, 3, 0, 6, 4] t (finSumFinEquiv j)
def bq (t : Fin 7) (j : Coord (Fin 2)) : ℤ := table #[5, 3, 2, 2, 3, 6, 0, 5, 0, 4, 5, 0, 0, 4, 6, 3, 0, 3, 2, 4, 2, 6, 4, 4, 6, 4, 6, 6] t (finSumFinEquiv j)

def M : Matrix (Rows (Fin 2) (Fin 4)) (Cols (Fin 2) (Fin 4) (Fin 0) (Fin 5) (Fin 7)) ℤ :=
  Pencils.matrix (fun t => Sum.elim (outA t) (ax t)) (fun t => Sum.elim (outB t) (bx t)) basisC ai bi ci aq bq

def original : Array ℕ := #[
  0x1200000004000000000000000000000000000000000000000a0000000000000000000000000000000000000000,
  0x1200000004000000000000000000000000000000000000000a000000000000000000000000000000000000000000,
  0x1200000004000000000000000000000000000000000000000a00000000000000000000000000000000000000000000,
  0x1200000004000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000,
  0xc0000000c00000009000000180000001000000000000000060000000000000000000000000000000000000000,
  0xc0000000c0000000900000018000000100000000000000006000000000000000000000000000000000000000000,
  0xc0000000c000000090000001800000010000000000000000600000000000000000000000000000000000000000000,
  0xc0000000c00000009000000180000001000000000000000060000000000000000000000000000000000000000000000,
  0x120000000800000006000000240000001400000000000000040000001200000000000000060000001200000019,
  0x12000000080000000600000024000000140000000000000004000000001200000004000000000000000c0000000a,
  0x120000000800000006000000240000001400000000000000040000000000060000000a0000001e0000000000000000,
  0x1200000008000000060000002400000014000000000000000400000000000018000000060000000c000000090000000a,
  0x12000000080000000c00000012000000000000000000000004000000030000000000000005000000240000000f,
  0x12000000080000000c00000012000000000000000000000004000000000300000004000000000000001800000006,
  0x12000000080000000c000000120000000000000000000000040000000000010000000a000000190000000000000000,
  0x12000000080000000c0000001200000000000000000000000400000000000004000000060000000a0000001200000006,
  0x600000000000000000000000000000003000000000000000000000000000000000000000000000000,
  0x60000000000000000000000000000000300000000000000000000000000000000000000000000000000,
  0x6000000000000000000000000000000030000000000000000000000000000000000000000000000000000,
  0x600000000000000000000000000000003000000000000000000000000000000000000000000000000000000,
  0x120000000c000000100000000400000006000000000000000000000000000000000000000000000000,
  0x120000000c00000010000000040000000600000000000000000000000000000000000000000000000000,
  0x120000000c0000001000000004000000060000000000000000000000000000000000000000000000000000,
  0x120000000c000000100000000400000006000000000000000000000000000000000000000000000000000000,
  0xc00000008000000180000000500000000000000000000120000000000000006000000120000001900,
  0xc00000008000000180000000500000000000000000000001200000004000000000000000c0000000a00,
  0xc000000080000001800000005000000000000000000000000060000000a0000001e000000000000000000,
  0xc0000000800000018000000050000000000000000000000000018000000060000000c000000090000000a00,
  0xc000000100000000c0000000000000005000000000000030000000000000005000000240000000f00,
  0xc000000100000000c000000000000000500000000000000030000000400000000000000180000000600,
  0xc000000100000000c00000000000000050000000000000000010000000a00000019000000000000000000,
  0xc000000100000000c000000000000000500000000000000000004000000060000000a000000120000000600,
  0x24000000080000000000000000000000000000000300000014000600000000000000010000001e0000000f0000,
  0x240000000800000000000000000000000000000003000000140000060000000c0000000000000014000000060000,
  0x24000000080000000000000000000000000000000300000014000000020000001e0000000500000000000000000000,
  0x24000000080000000000000000000000000000000300000014000000000800000012000000020000000f000000060000,
  0x18000000180000000c0000000c00000010000000060000000c0600000000000000010000001e0000000f000000,
  0x18000000180000000c0000000c00000010000000060000000c00060000000c000000000000001400000006000000,
  0x18000000180000000c0000000c00000010000000060000000c0000020000001e000000050000000000000000000000,
  0x18000000180000000c0000000c00000010000000060000000c0000000800000012000000020000000f00000006000000,
  0x1800000000000000000000000000000000000000000000000a000600000000000000000000001e000000190000,
  0x1800000000000000000000000000000000000000000000000a0000060000000000000000000000140000000a0000,
  0x1800000000000000000000000000000000000000000000000a00000002000000000000000000000000000000000000,
  0x1800000000000000000000000000000000000000000000000a000000000800000000000000000000000f0000000a0000,
  0x100000000000000000000000040000000400000000000000060600000000000000000000001e00000019000000,
  0x1000000000000000000000000400000004000000000000000600060000000000000000000000140000000a000000,
  0x1000000000000000000000000400000004000000000000000600000200000000000000000000000000000000000000,
  0x100000000000000000000000040000000400000000000000060000000800000000000000000000000f0000000a000000]
def rightInverse : Array ℕ := #[
  0x566440140000434513602146105446415363204353523001,
  0x422636530000226060336665264350231130551003515014,
  0x44500000332022603320445022605510445044505510,
  0x321612410000332035421463631416155510445063145510,
  0x603304401130412136146243206661466052124202604263,
  0x201153655510113035514663142033636640226011213225,
  0x536513521130332004440666456114634450664056210000,
  0x540612411130332002220333412416154450664052540000,
  0x566423020000540514012624441540523325354036406106,
  0x422600000000000014456332355142260000000063321445,
  0x1110000066604440666011104440333011101110333,
  0x135236533216226002220333551034315621423510260555,
  0x633261430000230263065153262451316565145606116565,
  0x355142260000000014455664211363320000000021130000,
  0x422632620000036615122402530506442546443003112546,
  0x126605261531135453423125153630226012004053412135,
  0x656024121466664065215416555605102631321512511456,
  0x656040141466434503223114015113111130551035530655,
  0x602563152155161315122402003250032260332001045520,
  0x145260565622616451203562151341105510445034545231,
  0x235651450441642333516132414322463542146355521310,
  0x245136222631525144261645346044416226330013023616,
  0x250631342155161304440666254551030054600106043114,
  0x110005425146631121024541660160556456063660530046,
  0x156302200224241424662654322250201026503204650643,
  0x404510361354066540213054650256205024001031300234,
  0x512212331466434513602146611361052205032305020455,
  0x514523566423044160120040525115644514042426616344,
  0x400625225363011226112210231365232156354246252353,
  0x343356410553204344653643202662010214333055536351,
  0x610444316311343216232250541360660015400340246254,
  0x156302510224642364560636326660426004304414000630,
  0x421120421025252624431655611145450666022211041646,
  0x66022156535226006513226340115351344114022363402,
  0x414064033544525154533603366452464465364354633062,
  0x155541551242252660351046610123633454261413113346,
  0x56560564345616433432136240051526162252320235314,
  0x6200151025605220061066500320504036005040551025,
  0x551522543544525121024541453212201114451160311556,
  0x634014456052000021101544421106512006106602631040,
  0x314206600665653565446415266610663064102605410452,
  0x505130243215044150632015410614501065003023200625,
  0x136636223544525132406354433242016601026201060511,
  0x135162144562055340360050161321455135056564434255,
  0x621452550553066545140424225412500555044450111630,
  0x440006056423551064336630636130615231334060523011,
  0x121002126311343242041312521316021153651605053503,
  0x52613351354653551434561506546101321014103105561]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
def pick (t : Fin 48) := (colEquiv 2 4 0 5 7).symm (⟨(pivots[t.val]?.getD 0) % 48, Nat.mod_lt _ (by decide)⟩ : Fin 48)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 48), M ((rowEquiv 2 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 48 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (rowEquiv 2 4) pick _ _ matrix_entries inverse_entries

lemma spans : Room 2 4 0 5 7 := certified_room ax bx ai bi ci aq bq rank

end IdleFourThree

namespace FourInner

def ai : Fin 2 → Fin 1 → ℤ := table #[5, 5]
def bi : Fin 2 → Fin 1 → ℤ := table #[6, 3]
def ci : Fin 2 → Fin 4 → ℤ := table #[6, 6, 0, 6, 3, 5, 1, 2]
def aq : Fin 0 → Fin 1 → ℤ := table #[]
def bq : Fin 0 → Fin 1 → ℤ := table #[]
def f : Fin 0 → Fin 2 → ℤ := table #[]
def g : Fin 0 → Fin 2 → ℤ := table #[]

namespace Left
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 4) (Fin 2) (Fin 0)) ℤ :=
  armMatrix outB basisC ai ci aq f

def original : Array ℕ := #[
  0xf001e00000001,
  0x19001e00000100,
  0x5000000010000,
  0xa001e01000000,
  0xf001e0000000001,
  0x19001e0000000200,
  0x500000000040000,
  0xa001e0003000000]
def rightInverse : Array ℕ := #[
  0x21411360,
  0x36225445,
  0x46642523,
  0x52540643,
  0x55026105,
  0x26631424,
  0x23321215,
  0x11514346]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 4 2 0).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Left


namespace Right
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 4) (Fin 2) (Fin 0)) ℤ :=
  armMatrix outA basisC bi ci bq g

def original : Array ℕ := #[
  0x9002400000001,
  0xf002400000100,
  0x3000000010000,
  0x6002401000000,
  0x900240000000001,
  0xf00240000000200,
  0x300000000030000,
  0x600240004000000]
def rightInverse : Array ℕ := #[
  0x65444664,
  0x55021615,
  0x30562141,
  0x35653622,
  0x32402160,
  0x6620325,
  0x60354012,
  0x45215636]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 4 2 0).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Right

lemma spans : Wing 1 4 4 2 0 := by
  exact ⟨_,_,_,_,_,_,_,certified_limb outB basisC ai ci aq f Left.rank,
    certified_limb outA basisC bi ci bq g Right.rank⟩

end FourInner

namespace FourIncoming

def ai : Fin 0 → Fin 1 → ℤ := table #[]
def bi : Fin 0 → Fin 1 → ℤ := table #[]
def ci : Fin 0 → Fin 4 → ℤ := table #[]
def aq : Fin 1 → Fin 1 → ℤ := table #[1]
def bq : Fin 1 → Fin 1 → ℤ := table #[2]
def f : Fin 1 → Fin 2 → ℤ := table #[6, 0]
def g : Fin 1 → Fin 2 → ℤ := table #[0, 4]

namespace Left
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 4) (Fin 0) (Fin 1)) ℤ :=
  armMatrix outB basisC ai ci aq f

def original : Array ℕ := #[
  0x600000001,
  0x60000000100,
  0x6000000010000,
  0x600000001000000,
  0x1,
  0x200,
  0x40000,
  0x3000000]
def rightInverse : Array ℕ := #[
  0x10000,
  0x400000,
  0x2000000,
  0x50000000,
  0x10006,
  0x400060,
  0x2000600,
  0x50006000]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 4 0 1).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Left


namespace Right
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 4) (Fin 0) (Fin 1)) ℤ :=
  armMatrix outA basisC bi ci bq g

def original : Array ℕ := #[
  0x1,
  0x100,
  0x10000,
  0x1000000,
  0x800000001,
  0x80000000200,
  0x8000000030000,
  0x800000004000000]
def rightInverse : Array ℕ := #[
  0x1,
  0x10,
  0x100,
  0x1000,
  0x10006,
  0x100050,
  0x1000400,
  0x10003000]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 4 0 1).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Right

lemma spans : Wing 1 4 4 0 1 := by
  exact ⟨_,_,_,_,_,_,_,certified_limb outB basisC ai ci aq f Left.rank,
    certified_limb outA basisC bi ci bq g Right.rank⟩

end FourIncoming

namespace ThreeInner

def ai : Fin 3 → Fin 2 → ℤ := table #[1, 2, 6, 0, 0, 4]
def bi : Fin 3 → Fin 2 → ℤ := table #[5, 5, 0, 4, 5, 1]
def ci : Fin 3 → Fin 3 → ℤ := table #[5, 4, 6, 5, 1, 2, 2, 0, 4]
def aq : Fin 0 → Fin 2 → ℤ := table #[]
def bq : Fin 0 → Fin 2 → ℤ := table #[]
def f : Fin 0 → Fin 2 → ℤ := table #[]
def g : Fin 0 → Fin 2 → ℤ := table #[]

namespace Left
def M : Matrix (Fin 2 × Fin 2 × Fin 3) (ArmCols (Fin 2) (Fin 3) (Fin 3) (Fin 3) (Fin 0)) ℤ :=
  armMatrix outB basisC ai ci aq f

def original : Array ℕ := #[
  0x1e0005000000000001,
  0x60004000000010000,
  0xc0006000100000000,
  0x1e000500000000000001,
  0x6000400000000020000,
  0xc000600000400000000,
  0x80000000a000000000100,
  0x8000001000000,
  0x100000000c010000000000,
  0x80000000a00000000000100,
  0x800000002000000,
  0x100000000c00040000000000]
def rightInverse : Array ℕ := #[
  0x60020056042,
  0x662426554143,
  0x40060345202,
  0x10115352,
  0x10050460620,
  0x554243223634,
  0x662425,
  0x10050554143,
  0x40060606401,
  0x50040565122,
  0x115352554143,
  0x156341115352]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def pick (t : Fin 12) := (armCols 2 3 3 3 0).symm (⟨(pivots[t.val]?.getD 0) % 12, Nat.mod_lt _ (by decide)⟩ : Fin 12)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 12), M ((armRows 2 3).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 12 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 2 3) pick _ _ matrix_entries inverse_entries

end Left


namespace Right
def M : Matrix (Fin 2 × Fin 2 × Fin 3) (ArmCols (Fin 2) (Fin 3) (Fin 3) (Fin 3) (Fin 0)) ℤ :=
  armMatrix outA basisC bi ci bq g

def original : Array ℕ := #[
  0xa00000019000000000001,
  0x14000000010000,
  0x140000001e000100000000,
  0xa0000001900000000000001,
  0x1400000000020000,
  0x140000001e00000300000000,
  0x200140019000000000100,
  0x40014000001000000,
  0x40008001e010000000000,
  0x20014001900000000000100,
  0x4001400000002000000,
  0x40008001e00030000000000]
def rightInverse : Array ℕ := #[
  0x641366510651,
  0x432216163424,
  0x324533532625,
  0x143404435212,
  0x265122565022,
  0x21136521636,
  0x324533532615,
  0x641366354543,
  0x432215201106,
  0x114453452245,
  0x136411152445,
  0x453244602305]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def pick (t : Fin 12) := (armCols 2 3 3 3 0).symm (⟨(pivots[t.val]?.getD 0) % 12, Nat.mod_lt _ (by decide)⟩ : Fin 12)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 12), M ((armRows 2 3).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 12 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 2 3) pick _ _ matrix_entries inverse_entries

end Right

lemma spans : Wing 2 3 3 3 0 := by
  exact ⟨_,_,_,_,_,_,_,certified_limb outB basisC ai ci aq f Left.rank,
    certified_limb outA basisC bi ci bq g Right.rank⟩

end ThreeInner

namespace ThreeIncoming

def ai : Fin 0 → Fin 1 → ℤ := table #[]
def bi : Fin 0 → Fin 1 → ℤ := table #[]
def ci : Fin 0 → Fin 3 → ℤ := table #[]
def aq : Fin 1 → Fin 1 → ℤ := table #[1]
def bq : Fin 1 → Fin 1 → ℤ := table #[2]
def f : Fin 1 → Fin 2 → ℤ := table #[6, 0]
def g : Fin 1 → Fin 2 → ℤ := table #[0, 4]

namespace Left
def M : Matrix (Fin 1 × Fin 2 × Fin 3) (ArmCols (Fin 1) (Fin 3) (Fin 3) (Fin 0) (Fin 1)) ℤ :=
  armMatrix outB basisC ai ci aq f

def original : Array ℕ := #[
  0x6000001,
  0x600000100,
  0x60000010000,
  0x1,
  0x200,
  0x40000]
def rightInverse : Array ℕ := #[
  0x1000,
  0x40000,
  0x200000,
  0x1006,
  0x40060,
  0x200600]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5]
def pick (t : Fin 6) := (armCols 1 3 3 0 1).symm (⟨(pivots[t.val]?.getD 0) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 6), M ((armRows 1 3).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 6 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 3) pick _ _ matrix_entries inverse_entries

end Left


namespace Right
def M : Matrix (Fin 1 × Fin 2 × Fin 3) (ArmCols (Fin 1) (Fin 3) (Fin 3) (Fin 0) (Fin 1)) ℤ :=
  armMatrix outA basisC bi ci bq g

def original : Array ℕ := #[
  0x1,
  0x100,
  0x10000,
  0x8000001,
  0x800000200,
  0x80000030000]
def rightInverse : Array ℕ := #[
  0x1,
  0x10,
  0x100,
  0x1006,
  0x10050,
  0x100400]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5]
def pick (t : Fin 6) := (armCols 1 3 3 0 1).symm (⟨(pivots[t.val]?.getD 0) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 6), M ((armRows 1 3).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 6 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 3) pick _ _ matrix_entries inverse_entries

end Right

lemma spans : Wing 1 3 3 0 1 := by
  exact ⟨_,_,_,_,_,_,_,certified_limb outB basisC ai ci aq f Left.rank,
    certified_limb outA basisC bi ci bq g Right.rank⟩

end ThreeIncoming

namespace IdleInner

def ai : Fin 4 → Fin 1 → ℤ := table #[1, 4, 4, 3]
def bi : Fin 4 → Fin 1 → ℤ := table #[4, 5, 5, 2]
def ci : Fin 4 → Fin 4 → ℤ := table #[6, 4, 5, 3, 0, 5, 5, 5, 3, 2, 4, 2, 3, 6, 3, 1]
def aq : Fin 0 → Fin 1 → ℤ := table #[]
def bq : Fin 0 → Fin 1 → ℤ := table #[]
def f : Fin 0 → Fin 2 → ℤ := table #[]
def g : Fin 0 → Fin 2 → ℤ := table #[]

namespace Left
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 0) (Fin 4) (Fin 0)) ℤ :=
  armMatrix outB basisC ai ci aq f

def original : Array ℕ := #[
  0x9000c00000006,
  0x12000800140004,
  0x9001000140005,
  0x3000800140003,
  0x9000c0000000600,
  0x1200080014000400,
  0x900100014000500,
  0x300080014000300]
def rightInverse : Array ℕ := #[
  0x4305,
  0x43050000,
  0x3646,
  0x36460000,
  0x616,
  0x6160000,
  0x2412,
  0x24120000]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 0 4 0).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Left


namespace Right
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 0) (Fin 4) (Fin 0)) ℤ :=
  armMatrix outA basisC bi ci bq g

def original : Array ℕ := #[
  0x6000f00000018,
  0xc000a00190010,
  0x6001400190014,
  0x2000a0019000c,
  0x6000f0000001800,
  0xc000a0019001000,
  0x600140019001400,
  0x2000a0019000c00]
def rightInverse : Array ℕ := #[
  0x1603,
  0x16030000,
  0x1262,
  0x12620000,
  0x252,
  0x2520000,
  0x3653,
  0x36530000]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 0 4 0).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Right

lemma spans : Wing 1 4 0 4 0 := by
  exact ⟨_,_,_,_,_,_,_,certified_limb outB basisC ai ci aq f Left.rank,
    certified_limb outA basisC bi ci bq g Right.rank⟩

end IdleInner

namespace IdleIncoming

def ai : Fin 0 → Fin 1 → ℤ := table #[]
def bi : Fin 0 → Fin 1 → ℤ := table #[]
def ci : Fin 0 → Fin 4 → ℤ := table #[]
def aq : Fin 2 → Fin 1 → ℤ := table #[5, 5]
def bq : Fin 2 → Fin 1 → ℤ := table #[6, 3]
def f : Fin 2 → Fin 2 → ℤ := table #[6, 6, 0, 6]
def g : Fin 2 → Fin 2 → ℤ := table #[3, 5, 1, 2]

namespace Left
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 0) (Fin 0) (Fin 2)) ℤ :=
  armMatrix outB basisC ai ci aq f

def original : Array ℕ := #[
  0x1e,
  0x1e00,
  0x1e0000,
  0x1e000000,
  0x1e0000001e,
  0x1e0000001e00,
  0x1e0000001e0000,
  0x1e0000001e000000]
def rightInverse : Array ℕ := #[
  0x4,
  0x40,
  0x400,
  0x4000,
  0x40003,
  0x400030,
  0x4000300,
  0x40003000]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 0 0 2).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Left


namespace Right
def M : Matrix (Fin 1 × Fin 2 × Fin 4) (ArmCols (Fin 1) (Fin 4) (Fin 0) (Fin 0) (Fin 2)) ℤ :=
  armMatrix outA basisC bi ci bq g

def original : Array ℕ := #[
  0x300000012,
  0x30000001200,
  0x3000000120000,
  0x300000012000000,
  0x60000001e,
  0x60000001e00,
  0x60000001e0000,
  0x60000001e000000]
def rightInverse : Array ℕ := #[
  0x10005,
  0x100050,
  0x1000500,
  0x10005000,
  0x10003,
  0x100030,
  0x1000300,
  0x10003000]
def pivots : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7]
def pick (t : Fin 8) := (armCols 1 4 0 0 2).symm (⟨(pivots[t.val]?.getD 0) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma matrix_entries : ∀ (i j : Fin 8), M ((armRows 1 4).symm i) (pick j) = (digit original 8 i.val j.val : ℤ) := by
  decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
lemma inverse_entries : valid (digit original 8) (digit rightInverse 4) 8 = true := by decide +kernel
lemma rank : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
  classical
  exact certified M (armRows 1 4) pick _ _ matrix_entries inverse_entries

end Right

lemma spans : Wing 1 4 0 0 2 := by
  exact ⟨_,_,_,_,_,_,_,certified_limb outB basisC ai ci aq f Left.rank,
    certified_limb outA basisC bi ci bq g Right.rank⟩

end IdleIncoming

end TensorRankExterior.Seven
namespace TensorRankExterior.Seven
open TensorRankExterior.Tiles

/-- A finite base, repeated inner-only arms, and repeated incoming-only arms
assemble a pencil in any dimension with the resulting point counts. -/
lemma grow {d w x n q di ni vo : ℕ} (base : Room d w x n q)
    (inner : Wing di w x ni 0) (incoming : Wing 1 w x 0 vo) (i e : ℕ) :
    PencilFor (Fin (d+i*di+e)) (Fin w) (Fin x) (Fin (n+i*ni)) (Fin (q+e*(2*vo))) := by
  have h := to_pencil (append (append base (repeat_paired (Fin i) inner)) (repeat_paired (Fin e) incoming))
  refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ h <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    ring

lemma odd_four_active (d p : ℕ) (hp : 5≤p) (hd : p≤d+2) (ho : p%2=1) :
    PencilFor (Fin d) (Fin 4) (Fin 4) (Fin (2*d+2-p)) (Fin (p-4)) := by
  let e := (p-5)/2
  let i := d-2-e
  have raw := grow ActiveFour.spans FourInner.spans FourIncoming.spans i e
  refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_fin,i,e]
    omega

lemma odd_three_active (d p : ℕ) (hp : 5≤p) (hd : p≤d+2) (ho : p%2=1) :
    PencilFor (Fin d) (Fin 3) (Fin 3) (Fin ((3*(2*d+2-p)+3)/4)) (Fin (p-3)) := by
  let e := (p-3)/2
  by_cases h : (d-e)%2=0
  · have raw := grow ActiveThreeZero.spans ThreeInner.spans ThreeIncoming.spans ((d-e)/2) e
    refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ raw <;> apply Fintype.equivOfCardEq
    all_goals
      simp only [Fintype.card_fin,e] at *
      omega
  · have raw := grow ActiveThreeMixed.spans ThreeInner.spans ThreeIncoming.spans ((d-e-1)/2) (e-1)
    refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ raw <;> apply Fintype.equivOfCardEq
    all_goals
      simp only [Fintype.card_fin,e] at *
      omega

lemma odd_four_idle (d p : ℕ) (hp : 5≤p) (hd : p≤d+2) (ho : p%2=1) :
    PencilFor (Fin d) (Fin 4) (Fin 0) (Fin (4*d+4-p)) (Fin p) := by
  by_cases h : p%4=1
  · let e := (p-5)/4
    have raw := grow IdleFourOne.spans IdleInner.spans IdleIncoming.spans (d-2-e) e
    refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ raw <;> apply Fintype.equivOfCardEq
    all_goals
      simp only [Fintype.card_fin,e]
      omega
  · let e := (p-7)/4
    have raw := grow IdleFourThree.spans IdleInner.spans IdleIncoming.spans (d-2-e) e
    refine pencil_transport ?_ (Equiv.refl _) ?_ ?_ raw <;> apply Fintype.equivOfCardEq
    all_goals
      simp only [Fintype.card_fin,e]
      omega

lemma two_active (d p : ℕ) (hp : 5≤p) (hd : p≤d+2) :
    PencilFor (Fin d) (Fin 2) (Fin 2) (Fin (d+1-p/2)) (Fin (p-2)) := by
  have raw := Pencils.unused_incoming (Z:=Fin (p%2))
    (active_pencil (Fin (d+1-p/2)) (Fin ((p-2)/2)))
  refine pencil_transport ?_ (Equiv.refl _) (Equiv.refl _) ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega

lemma one_idle (d p : ℕ) (hp : 5≤p) (hd : p≤d+2) :
    PencilFor (Fin d) (Fin 1) (Fin 0) (Fin (d+1-p/4)) (Fin p) := by
  have raw := Pencils.unused_incoming (Z:=Fin (p%4))
    (singleton_idle (Fin (d+1-p/4)) (Fin ((p-4)/4)))
  refine pencil_transport ?_ (Equiv.refl _) (Equiv.refl _) ?_ raw <;> apply Fintype.equivOfCardEq
  all_goals
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega

end TensorRankExterior.Seven
namespace TensorRankExterior.Seven

def angularBudget (n : ℕ) : ℕ :=
  let p := n-(n-1)/9
  let d := n-2
  let a := (p-3)/4
  let t := (p-3)%4/2
  let b := (n-p)/4
  let v := (n-p)%4
  a*(2*d+2-p) + (3*(2*d+2-p)+3)/4 + t*(d+1-p/2) + b*(4*d+4-p) + v*(d+1-p/4)

set_option maxHeartbeats 900000 in
/-- The few blocks whose widths are below four cost at most fourteen
scalar directions in total. The cubic ceiling pays for this rounding. -/
lemma angular_budget (n : ℕ) (hn : 5≤n) (hc : n%3≠1) (ho : (n-(n-1)/9)%2=1) :
    angularBudget n ≤ coreCount n := by
  by_cases small : n≤26
  · interval_cases n <;> norm_num [angularBudget,coreCount] at *
  let p := n-(n-1)/9
  let d := n-2
  let a := (p-3)/4
  let t := (p-3)%4/2
  let b := (n-p)/4
  let v := (n-p)%4
  let X := 2*d+2-p
  let F := 4*d+4-p
  have hd : d+2=n := by dsimp only [d]; omega
  have hp : 5≤p ∧ p≤n := by dsimp only [p]; omega
  have hodd : p%2=1 := ho
  have ha : 4*a+3+2*t=p := by dsimp only [a,t]; omega
  have hb : 4*b+v=n-p := by dsimp only [b,v]; omega
  have ht : t≤1 := by dsimp only [t]; omega
  have hv : v≤3 := by dsimp only [v]; omega
  have hx : X+p=2*d+2 := by dsimp only [X]; omega
  have hf : F+p=4*d+4 := by dsimp only [F]; omega
  have hhalf : 4*(d+1-p/2) ≤ 2*X+2 := by omega
  have hsingle : 4*(d+1-p/4) ≤ F+3 := by omega
  have hthree : 4*((3*X+3)/4) ≤ 3*X+3 := by omega
  have tally : 4*angularBudget n ≤ p*X+(n-p)*F+14 := by
    change 4*(a*X+(3*X+3)/4+t*(d+1-p/2)+b*F+v*(d+1-p/4)) ≤ _
    nlinarith only [ht,hv,hthree,Nat.mul_le_mul_left t hhalf,Nat.mul_le_mul_left v hsingle,
      congrArg (fun z : ℕ => z*X) ha, congrArg (fun z : ℕ => z*F) hb]
  have hden : 3*n-2+2=3*n := by omega
  have hrem : n-p+p=n := by omega
  have balance : p*X+(n-p)*F+(3*n-2)*p+4*n=4*n^2 := by
    nlinarith only [congrArg (fun z : ℕ => z*F) hrem,congrArg (fun z : ℕ => z*n) hf,
      congrArg (fun z : ℕ => z*p) hx,congrArg (fun z : ℕ => z*p) hf,
      congrArg (fun z : ℕ => z*p) hd,congrArg (fun z : ℕ => z*n) hd,congrArg (fun z : ℕ => z*p) hden]
  have hs : 3*coreCount n+2*n=n^2 := by simpa only [if_neg hc,add_zero] using three_core n (by omega)
  have hp9 : 8*n+3≤9*p := by dsimp only [p]; omega
  have room : 4*n^2+14 ≤ 4*coreCount n+(3*n-2)*p+4*n := by
    have hl : 27≤n := by omega
    nlinarith only [hl,hs,hden,Nat.mul_le_mul_left (3*n-2) hp9,congrArg (fun z : ℕ => z*n) hden]
  omega

end TensorRankExterior.Seven
namespace TensorRankExterior.Seven
open TensorRankExterior.Pencils

abbrev Blocks (a t b v : ℕ) := Fin a ⊕ (Fin 1 ⊕ (Fin t ⊕ (Fin b ⊕ Fin v)))
def five {a t b v : ℕ} (na n₃ n₂ nb nv : ℕ) : Blocks a t b v → ℕ :=
  Sum.elim (fun _ => na) (Sum.elim (fun _ => n₃) (Sum.elim (fun _ => n₂) (Sum.elim (fun _ => nb) (fun _ => nv))))

lemma card_five (a t b v na n₃ n₂ nb nv : ℕ) :
    Fintype.card (Σ k : Blocks a t b v, Fin (five na n₃ n₂ nb nv k)) =
      a*na+n₃+t*n₂+b*nb+v*nv := by
  rw [Fintype.card_sigma]
  simp only [Blocks,Fintype.sum_sum_type]
  change (∑ _ : Fin a, Fintype.card (Fin na)) + ((∑ _ : Fin 1, Fintype.card (Fin n₃)) +
    ((∑ _ : Fin t, Fintype.card (Fin n₂)) + ((∑ _ : Fin b, Fintype.card (Fin nb)) +
      ∑ _ : Fin v, Fintype.card (Fin nv)))) = _
  simp [add_assoc]

lemma odd_extra_config (d p a t b v s : ℕ) (hp : 5≤p) (hd : p≤d+2) (ho : p%2=1)
    (ha : 4*a+3+2*t=p) (hb : 4*b+v=d+2-p)
    (hs : a*(2*d+2-p)+(3*(2*d+2-p)+3)/4+t*(d+1-p/2)+b*(4*d+4-p)+v*(d+1-p/4) ≤ s) :
    Witness (d+2) d (d+2) s (s+p) := by
  classical
  let K := Blocks a t b v
  let W (k : K) := Fin (five 4 3 2 4 1 k)
  let X (k : K) := Fin (five 4 3 2 0 0 k)
  let N (k : K) := Fin (five (2*d+2-p) ((3*(2*d+2-p)+3)/4) (d+1-p/2) (4*d+4-p) (d+1-p/4) k)
  have hX : Fintype.card (Sigma X) = p := by
    change Fintype.card (Σ k : Blocks a t b v, Fin (five 4 3 2 0 0 k))=_
    rw [card_five]
    omega
  have hW : Fintype.card (Sigma W) = d+2 := by
    change Fintype.card (Σ k : Blocks a t b v, Fin (five 4 3 2 4 1 k))=_
    rw [card_five]
    omega
  have hN : Fintype.card (Sigma N) ≤ s := by
    exact (card_five a t b v _ _ _ _ _).le.trans hs
  have locals (k : K) : PencilFor (Fin d) (W k) (X k) (N k) (Away X k) := by
    have hoff := (Fintype.card_congr (@split _ X _ k)).symm
    rw [Fintype.card_sum,hX] at hoff
    rcases k with k|k|k|k|k
    · change 4+_=p at hoff
      refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (odd_four_active d p hp hd ho)
      apply Fintype.equivOfCardEq
      rw [Fintype.card_fin]
      omega
    · change 3+_=p at hoff
      refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (odd_three_active d p hp hd ho)
      apply Fintype.equivOfCardEq
      rw [Fintype.card_fin]
      omega
    · change 2+_=p at hoff
      refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (two_active d p hp hd)
      apply Fintype.equivOfCardEq
      rw [Fintype.card_fin]
      omega
    · change 0+_=p at hoff
      refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (odd_four_idle d p hp hd ho)
      apply Fintype.equivOfCardEq
      rw [Fintype.card_fin]
      omega
    · change 0+_=p at hoff
      refine pencil_transport (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) ?_ (one_idle d p hp hd)
      apply Fintype.equivOfCardEq
      rw [Fintype.card_fin]
      omega
  obtain ⟨x,hx⟩ := exists_combined locals
  let ew : Fin (d+2) ≃ Sigma W := Fintype.equivOfCardEq (by rw [Fintype.card_fin,hW])
  let ex : Fin p ≃ Sigma X := Fintype.equivOfCardEq (by rw [Fintype.card_fin,hX])
  let ep := (splitAt (s+p) s p rfl).trans (Equiv.sumCongr (Equiv.refl (Fin s)) ex)
  have hpin (j : Fin (s+p)) (hj : j.val<s) : ep j=Sum.inl ⟨j.val,hj⟩ := by simp [ep,splitAt_small rfl j hj]
  let en : Fin s ≃ Sigma N ⊕ Fin (s-Fintype.card (Sigma N)) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum,Fintype.card_fin]; omega)
  exact witness_of_combined rfl ew ep hpin en x hx

lemma first_format (n : ℕ) (hn : 5≤n) (hc : n%3≠1) :
    Witness n (n-2) n (coreCount n) (coreCount n + (n-(n-1)/9)) := by
  let d := n-2
  let p := n-(n-1)/9
  by_cases he : p%2=0
  · have hw := Pencils.even_extra_supported n hn hc he
    have hr : n^3 ⌈/⌉ (3*n-2)=coreCount n+p := by
      rw [cube_count n (by omega)]
      dsimp only [p]
      omega
    rwa [hr] at hw
  · let a := (p-3)/4
    let t := (p-3)%4/2
    let b := (n-p)/4
    let v := (n-p)%4
    have hodd : p%2=1 := by omega
    have hdim : d+2=n := by dsimp only [d]; omega
    have hs := angular_budget n hn hc hodd
    have hp : 5≤p ∧ p≤d+2 := by dsimp only [p,d]; omega
    have hA : 4*a+3+2*t=p := by dsimp only [a,t]; omega
    have hB : 4*b+v=d+2-p := by dsimp only [b,v]; omega
    have hw := odd_extra_config d p a t b v (coreCount n) hp.1 hp.2 hodd hA hB hs
    rwa [hdim] at hw

end TensorRankExterior.Seven

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1.H1 := by
  intro n hn hc
  have hw := TensorRankExterior.Seven.first_format n hn hc
  have hs : TensorRankExterior.coreCount n = (n-2)*n/3 := by
    simp only [TensorRankExterior.coreCount,if_neg hc]
  rw [hs] at hw
  obtain ⟨x,a,b,c,hfix,hcov⟩ := hw
  refine ⟨a,b,c,?_,?_⟩
  · intro t ht i hi
    have h := hfix t ht i
    exact ⟨by simpa only [dif_neg (Nat.not_lt_of_ge hi)] using h.1,
      by simpa only [dif_neg (Nat.not_lt_of_ge hi)] using h.2.1⟩
  · intro T
    obtain ⟨u,v,w,h⟩ := hcov T
    exact ⟨u,v,w,fun i j k hij => h i j k (hij.imp_right Or.inl)⟩
