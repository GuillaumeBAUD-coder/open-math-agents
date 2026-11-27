import OMAReductions.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1

/-! Projecting a tensor tangent map onto the complement of a rectangular block
gives a matrix polynomial in the inner factors. At one supported configuration
of full row rank, fix both the extra points and a right inverse. The resulting
determinant is a nonzero polynomial in the inner coordinates, and its
nonvanishing preserves the projected spanning property. Thus each format needs
only one supported configuration per dimension. The extra-point budget in both
formats is exactly n minus the integer quotient of n - 1 by 9.

The two geometrically different complements are those in Thomas Lickteig,
Typical tensorial rank (1985), Lemmas 4.6 and 4.7.
[Article](https://doi.org/10.1016/0024-3795(85)90070-9). -/

namespace OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1

open MvPolynomial

section TwoOuterCoordinates
/-- One spanning configuration outside the (n-2,n-2,n) block. Its inner
points have both of their first two factors supported inside the block. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 ≤ n → n % 3 ≠ 1 →
    let d := n-2
    let s := d*n/3
    let r := s + (n - (n-1)/9)
    ∃ a b c : Fin r → Fin n → ℂ,
      (∀ (t : Fin r), t.val < s → ∀ i : Fin n, d ≤ i.val → a t i = 0 ∧ b t i = 0) ∧
      ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
        (d ≤ i.val ∨ d ≤ j.val) →
          T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
            a t i * (b t j * w t k))
end TwoOuterCoordinates

section ThreeOuterFactors
/-- One spanning configuration outside the (n-1,n-1,n-2) block, with the
three inner factors supported in their corresponding coordinate ranges. -/
def H2 : Prop :=
  ∀ n : ℕ, 10 ≤ n → n % 3 = 1 →
    let d := n-1
    let e := n-2
    let s := d*d/3
    let r := s + (n - (n-1)/9)
    ∃ a b c : Fin r → Fin n → ℂ,
      (∀ (t : Fin r), t.val < s → ∀ i : Fin n,
        (d ≤ i.val → a t i = 0 ∧ b t i = 0) ∧ (e ≤ i.val → c t i = 0)) ∧
      ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
        (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) →
          T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
            a t i * (b t j * w t k))
end ThreeOuterFactors


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

lemma projected_tangent_iff {n d e r : ℕ} (a b c : Fin r → Fin n → ℂ)
    (M : Matrix {z : Fin n × Fin n × Fin n // d ≤ z.1.val ∨ d ≤ z.2.1.val ∨ e ≤ z.2.2.val}
      (Fin r × (Fin n ⊕ (Fin n ⊕ Fin n))) ℂ)
    (entries : ∀ (i j k : Fin n) (h : d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val)
      (t : Fin r) (q : Fin n ⊕ (Fin n ⊕ Fin n)), M ⟨(i,j,k),h⟩ (t,q) = match q with
        | Sum.inl v => if v=i then b t j*c t k else 0
        | Sum.inr (Sum.inl v) => if v=j then a t i*c t k else 0
        | Sum.inr (Sum.inr v) => if v=k then a t i*b t j else 0) :
    (∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
      (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) → T i j k = ∑ t, (u t i * (b t j*c t k) +
        a t i*(v t j*c t k) + a t i*(b t j*w t k))) ↔ Function.Surjective M.mulVec := by
  classical
  let J := Fin r × (Fin n ⊕ (Fin n ⊕ Fin n))
  have action (y : J → ℂ) (i j k : Fin n) (h : d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) :
      M.mulVec y ⟨(i,j,k),h⟩ = ∑ t, (y (t,Sum.inl i) * (b t j*c t k) +
        a t i*(y (t,Sum.inr (Sum.inl j))*c t k) + a t i*(b t j*y (t,Sum.inr (Sum.inr k)))) := by
    change (∑ z : J, M ⟨(i,j,k),h⟩ z*y z) = _
    simp [J,Fintype.sum_prod_type,Fintype.sum_sum_type,entries,ite_mul,Finset.sum_ite_eq',
      mul_comm,mul_assoc,add_assoc]
  constructor
  · intro hh T
    let lift (i j k : Fin n) := if h : d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val then T ⟨(i,j,k),h⟩ else 0
    obtain ⟨u,v,w,ht⟩ := hh lift
    let y : J → ℂ := fun z => Sum.elim (u z.1) (Sum.elim (v z.1) (w z.1)) z.2
    refine ⟨y, ?_⟩
    funext z
    obtain ⟨⟨i,j,k⟩,h⟩ := z
    exact ((action y i j k h).trans (ht i j k h).symm).trans (dif_pos h)
  · intro hh T
    obtain ⟨y,hy⟩ := hh fun z => T z.1.1 z.1.2.1 z.1.2.2
    refine ⟨fun t i => y (t,Sum.inl i), fun t j => y (t,Sum.inr (Sum.inl j)),
      fun t k => y (t,Sum.inr (Sum.inr k)), ?_⟩
    intro i j k h
    exact (congrFun hy ⟨(i,j,k),h⟩).symm.trans (action y i j k h)

/-- An isolated full-rank witness gives an entire principal open of compatible
inner configurations, with the extra vectors fixed at their witness values. -/
lemma generic_from_supported {n d e s r : ℕ} (hd : d≤n) (he : e≤n) (hs : s≤r)
    (witness : ∃ a b c : Fin r → Fin n → ℂ,
      (∀ (t : Fin r), t.val < s → ∀ i : Fin n,
        (d ≤ i.val → a t i = 0 ∧ b t i = 0) ∧ (e ≤ i.val → c t i = 0)) ∧
      ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
        (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) → T i j k = ∑ t, (u t i*(b t j*c t k) +
          a t i*(v t j*c t k) + a t i*(b t j*w t k))) :
    ∃ P : MvPolynomial (Fin s × (Fin d ⊕ (Fin d ⊕ Fin e))) ℂ, P ≠ 0 ∧
      ∀ x : Fin s × (Fin d ⊕ (Fin d ⊕ Fin e)) → ℂ, eval x P ≠ 0 →
        ∃ a b c : Fin r → Fin n → ℂ,
          (∀ (t : Fin r) (ht : t.val < s) (i : Fin n),
            a t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inl ⟨i.val,h⟩) else 0) ∧
            b t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inr (Sum.inl ⟨i.val,h⟩)) else 0) ∧
            c t i = (if h : i.val < e then x (⟨t.val,ht⟩, Sum.inr (Sum.inr ⟨i.val,h⟩)) else 0)) ∧
          ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
            (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) → T i j k = ∑ t, (u t i*(b t j*c t k) +
              a t i*(v t j*c t k) + a t i*(b t j*w t k)) := by
  classical
  obtain ⟨a,b,c,supp,hspan⟩ := witness
  let V := Fin s × (Fin d ⊕ (Fin d ⊕ Fin e))
  let J := Fin r × (Fin n ⊕ (Fin n ⊕ Fin n))
  let I := {z : Fin n × Fin n × Fin n // d ≤ z.1.val ∨ d ≤ z.2.1.val ∨ e ≤ z.2.2.val}
  let nameA (t : Fin s) (i : Fin d) : V := (t,Sum.inl i)
  let nameB (t : Fin s) (j : Fin d) : V := (t,Sum.inr (Sum.inl j))
  let nameC (t : Fin s) (k : Fin e) : V := (t,Sum.inr (Sum.inr k))
  let x₀ (z : V) := z.2.elim (fun i => a (Fin.castLE hs z.1) (Fin.castLE hd i))
    (Sum.elim (fun j => b (Fin.castLE hs z.1) (Fin.castLE hd j))
      (fun k => c (Fin.castLE hs z.1) (Fin.castLE he k)))
  let factor {m : ℕ} (name : Fin s → Fin m → V) (base : Fin r → Fin n → ℂ)
      (t : Fin r) (i : Fin n) : MvPolynomial V ℂ :=
    if ht : t.val < s then (if hi : i.val < m then X (name ⟨t.val,ht⟩ ⟨i.val,hi⟩) else 0) else C (base t i)
  let A := factor nameA a
  let B := factor nameB b
  let D := factor nameC c
  have recover (m : ℕ) (hm : m≤n) (name : Fin s → Fin m → V) (base : Fin r → Fin n → ℂ)
      (hz : ∀ (t : Fin r), t.val < s → ∀ i : Fin n, m ≤ i.val → base t i=0)
      (hg : ∀ t i, x₀ (name t i) = base (Fin.castLE hs t) (Fin.castLE hm i)) :
      (fun t i => eval x₀ (factor name base t i)) = base := by
    funext t i
    by_cases ht : t.val < s
    · by_cases hi : i.val < m
      · simpa only [factor,dif_pos ht,dif_pos hi,eval_X,
          show Fin.castLE hs ⟨t.val,ht⟩ = t from Fin.ext rfl,
          show Fin.castLE hm ⟨i.val,hi⟩ = i from Fin.ext rfl] using hg ⟨t.val,ht⟩ ⟨i.val,hi⟩
      · simp [factor,ht,hi,hz t ht i (Nat.le_of_not_gt hi)]
    · simp [factor,ht]
  have ha : (fun t i => eval x₀ (A t i)) = a :=
    recover d hd _ _ (fun t ht i hi => ((supp t ht i).1 hi).1) (fun _ _ => rfl)
  have hb : (fun t i => eval x₀ (B t i)) = b :=
    recover d hd _ _ (fun t ht i hi => ((supp t ht i).1 hi).2) (fun _ _ => rfl)
  have hc : (fun t i => eval x₀ (D t i)) = c :=
    recover e he _ _ (fun t ht i hi => (supp t ht i).2 hi) (fun _ _ => rfl)
  let M : Matrix I J (MvPolynomial V ℂ) := fun z h => match h.2 with
    | Sum.inl v => if v=z.val.1 then B h.1 z.val.2.1 * D h.1 z.val.2.2 else 0
    | Sum.inr (Sum.inl v) => if v=z.val.2.1 then A h.1 z.val.1 * D h.1 z.val.2.2 else 0
    | Sum.inr (Sum.inr v) => if v=z.val.2.2 then A h.1 z.val.1 * B h.1 z.val.2.1 else 0
  have equiv (x : V → ℂ) := projected_tangent_iff (d:=d) (e:=e)
    (fun t i => eval x (A t i)) (fun t i => eval x (B t i)) (fun t i => eval x (D t i)) (M.map (eval x))
    (by
      intro i j k h t q
      change eval x (M ⟨(i,j,k),h⟩ (t,q)) = _
      rcases q with v | v | v
      · by_cases hv : v=i <;> simp [M,hv]
      · by_cases hv : v=j <;> simp [M,hv]
      · by_cases hv : v=k <;> simp [M,hv])
  have hbase : Function.Surjective (M.map (eval x₀)).mulVec := by
    apply (equiv x₀).mp
    have fa (t i) : eval x₀ (A t i) = a t i := congrFun (congrFun ha t) i
    have fb (t i) : eval x₀ (B t i) = b t i := congrFun (congrFun hb t) i
    have fc (t i) : eval x₀ (D t i) = c t i := congrFun (congrFun hc t) i
    simpa only [fa,fb,fc] using hspan
  obtain ⟨P,hP,hgood⟩ := surjectivity_polynomial M x₀ hbase
  refine ⟨P,hP,?_⟩
  intro x hx
  refine ⟨fun t i => eval x (A t i),fun t i => eval x (B t i),fun t i => eval x (D t i),?_,(equiv x).mpr (hgood x hx)⟩
  intro t ht i
  by_cases h₁ : i.val < d <;> by_cases h₂ : i.val < e <;> simp [A,B,D,factor,ht,h₁,h₂,nameA,nameB,nameC]


lemma three_core (n : ℕ) (hn : 2 ≤ n) :
    3 * (if n%3=1 then (n-1)*(n-1)/3 else (n-2)*n/3) + 2*n = n^2 + (if n % 3 = 1 then 1 else 0) := by
  by_cases h : n % 3 = 1
  · simp only [if_pos h]
    have hr : (n-1)%3 = 0 := by omega
    have hm : ((n-1)*(n-1))%3 = 0 := by rw [Nat.mul_mod]; simp [hr]
    have h3 : 3 * (((n-1)*(n-1))/3) = (n-1)*(n-1) := by omega
    rw [h3]
    have hsub : n-1+1=n := by omega
    nlinarith [congrArg (fun q : ℕ => q*q) hsub]
  · simp only [if_neg h, add_zero]
    have hr : (n-2)%3 = 0 ∨ n%3 = 0 := by omega
    have hm : ((n-2)*n)%3 = 0 := by rw [Nat.mul_mod]; rcases hr with h | h <;> simp [h]
    have h3 : 3 * (((n-2)*n)/3) = (n-2)*n := by omega
    rw [h3]
    have hsub : n-2+2=n := by omega
    nlinarith [congrArg (fun q : ℕ => q*n) hsub]

/-- The same number of extra points works for both rectangular formats. -/
lemma cube_count (n : ℕ) (hn : 2 ≤ n) :
    n^3 ⌈/⌉ (3*n-2) = (if n%3=1 then (n-1)*(n-1)/3 else (n-2)*n/3) + (8*n/9) + 1 := by
  let s := (if n%3=1 then (n-1)*(n-1)/3 else (n-2)*n/3)
  let D := 3*n-2
  let q := 8*n/9
  let j := 8*n%9
  let b := if n%3=1 then 1 else 0
  have hs : 3*s+2*n=n^2+b := three_core n hn
  have hD : D+2=3*n := by dsimp only [D]; omega
  have hp : 0<D := by omega
  have hq : 9*q+j=8*n := by dsimp only [q,j]; omega
  have hlo : 3*b ≤ j+1 := by dsimp only [b,j]; split <;> omega
  have hhi : j ≤ 7+3*b := by dsimp only [b,j]; split <;> omega
  have hz : 9*(s+q)+j=3*n^2+2*n+3*b := by omega
  have key : 9*(D*(s+q))+D*j+4*n=9*n^3+D*(3*b) := calc
    _ = D*(9*(s+q)+j)+4*n := by ring
    _ = D*(3*n^2+2*n+3*b)+4*n := by rw [hz]
    _ = _ := by nlinarith [congrArg (fun z : ℕ => z*(3*n^2+2*n)) hD]
  have lo : D*(s+q)<n^3 := by
    have h := Nat.mul_le_mul_left D hlo
    rw [Nat.mul_add, Nat.mul_one] at h
    omega
  have hi : n^3 ≤ D*(s+q+1) := by
    have h := Nat.mul_le_mul_left D hhi
    rw [Nat.mul_add] at h
    rw [Nat.mul_succ]
    omega
  change n^3 ⌈/⌉ D = s+q+1
  refine le_antisymm ((ceilDiv_le_iff_le_mul hp).mpr hi) ?_
  by_contra! h
  have hh : n^3 ⌈/⌉ D ≤ s+q := by omega
  exact (not_le_of_gt lo) ((ceilDiv_le_iff_le_mul hp).mp hh)

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1.H3 := by
  intro h₁ h₂ n hn h7
  let d := if n%3=1 then n-1 else n-2
  let e := if n%3=1 then n-2 else n
  let s := d*(if n%3=1 then d else n)/3
  let r := n^3 ⌈/⌉ (3*n-2)
  have hd : d≤n := by dsimp only [d]; split <;> omega
  have he : e≤n := by dsimp only [e]; split <;> omega
  have hs : s≤r := OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1.inner_count_le
    n d _ (by omega) hd (by split <;> omega)
  apply generic_from_supported (n:=n) (d:=d) (e:=e) (s:=s) (r:=r) hd he hs
  let One (d e s r : ℕ) : Prop := ∃ a b c : Fin r → Fin n → ℂ,
    (∀ (t : Fin r), t.val<s → ∀ i : Fin n, (d ≤ i.val → a t i=0 ∧ b t i=0) ∧ (e ≤ i.val → c t i=0)) ∧
    ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
      (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) → T i j k=∑ t, (u t i*(b t j*c t k) +
        a t i*(v t j*c t k) + a t i*(b t j*w t k))
  change One d e s r
  have hcount := cube_count n (by omega)
  have hextra : 8*n/9+1=n-(n-1)/9 := by omega
  rw [Nat.add_assoc,hextra] at hcount
  by_cases hm : n%3=1
  · simp only [r,hcount,d,e,s,if_pos hm]
    exact h₂ n (by omega) hm
  · simp only [r,hcount,d,e,s,if_neg hm]
    obtain ⟨a,b,c,support,cover⟩ := h₁ n hn hm
    refine ⟨a,b,c,fun t ht i => ⟨support t ht i,fun hi => False.elim ((Nat.not_le_of_gt i.isLt) hi)⟩,?_⟩
    intro T
    obtain ⟨u,v,w,h⟩ := cover T
    refine ⟨u,v,w,?_⟩
    intro i j k hijk
    exact h i j k (by rcases hijk with hi|hj|hk <;> omega)

end OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1_H3_R1
