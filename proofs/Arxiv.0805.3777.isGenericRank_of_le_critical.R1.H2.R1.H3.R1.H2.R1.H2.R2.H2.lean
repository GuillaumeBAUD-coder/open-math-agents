import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

-- Credit: @mattdorman

/-! # Generic complex tensor rank at the even sharp boundary

For even h≥10, take b=h(h−2)−1, r=2b−h and n=r−(2h−5).
In the conic construction the coefficient matrix has L² rows and L²−1
columns, where L=h−1. Sparse coefficients split the column test into
residue classes. In a stretch of ordinary coordinates, each normal
satisfies a four-periodic difference equation. Inserting four coordinates
preserves its kernel. Following the three ordered anchor gaps reduces
every width to 966 finite residue tests.

Exact elimination reduces those integer tests to 198 cores of order at
most 16. Their ranks modulo 131 give full column rank over the complex
numbers. Polynomial specialization makes the residue tests simultaneous
and the parent’s tangent-to-rank argument gives the stated generic rank.

The underlying problem is Friedland’s Conjecture 5.1, arXiv:0805.3777.
The immediate target is the even sharp-boundary hypothesis of the
higher-dimensional normal-space reduction descending from project PR 12200.
-/

namespace CriticalConicEvenSparse

/-- The two omitted classes, represented inside the actual column interval 0,…,L. -/
def allowed (m a v : ℤ) : Prop := v≠a-2 ∧ v≠a+m-4

/-- The private pair coordinate in the full representative range −1,…,m−2. -/
def position (m a v : ℤ) : ℤ := ((v-a)*((m+1)/2)+1)%m-1

/-- Outside the physical interval this is zero. Inside, later special
sites take precedence over earlier sites when two of them coincide. -/
def weight (m a z : ℤ) : ℤ :=
  if z<0 ∨ m-2≤z then 0 else if z=a+1 then 17 else if z=a then 13
  else if z=a-1 then 11 else if z=m-3 then 7 else if z=m-4 then 5
  else if z=1 then 3 else if z=0 then 2 else 1

/-- The unblocked sign-scaled coefficient for one physical residue. -/
def entry (m a s v : ℤ) : ℤ :=
  let p := position m a v-(if s<a then 1 else 0)
  (if v≤ s then weight m a (s+1)*weight m a p else 0) -
    (if s≤v+1 then weight m a s*weight m a (p+1) else 0) +
    (if s=1 ∧ v=m-2 then weight m a 0*weight m a (p+2) else 0)

/-- Full column rank on the columns actually present in residue a. -/
def Good (L a : ℕ) : Prop :=
  ∀ x : Fin (L+1)→ℂ,
    (∀ v : Fin (L+1), ¬allowed ((L:ℤ)+2) a v.val → x v=0) →
    (∀ s : Fin L, (∑ v : Fin (L+1), (entry ((L:ℤ)+2) a s.val v.val : ℂ)*x v)=0) → x=0

end CriticalConicEvenSparse

namespace CriticalConicEvenSparse

/-- Unbounded index functions allow row and column positions to be transported
across a gap. Only the finite row and column ranges are read by good. -/
structure Profile where
  upper : ℕ→ℂ
  lower : ℕ→ℂ
  before : ℕ→Bool
  channel : ℕ→ℤ→ℂ
  allow : ℕ→Prop
  corner : ℂ

def Profile.coeff (P : Profile) (L s v : ℕ) : ℂ :=
  let off : ℤ := if P.before s then -1 else 0
  (if v≤ s then P.upper s*P.channel v off else 0) -
    (if s≤v+1 then P.lower s*P.channel v (off+1) else 0) +
    (if s=1 ∧ v=L then P.corner*P.channel v (off+2) else 0)

def Profile.good (P : Profile) (L : ℕ) : Prop :=
  ∀ x : Fin (L+1)→ℂ, (∀ v : Fin (L+1), ¬P.allow v.val → x v=0) →
    (∀ s : Fin L,(∑ v : Fin (L+1),P.coeff L s.val v.val*x v)=0) → x=0

def up (t i : ℕ) := if i<t then i else i+4

/-- The inputs of a clean, ordered four-position insertion. -/
structure Splice (L t : ℕ) (P Q : Profile) : Prop where
  left : 3≤t
  right : t+4≤L
  row : ∀ s, s<L → Q.upper (up t s)=P.upper s ∧ Q.lower (up t s)=P.lower s ∧
    Q.before (up t s)=P.before s
  col : ∀ v, v≤L → (Q.allow (up t v) ↔ P.allow v) ∧
    ∀ r : ℤ, -1≤r → r≤2 → Q.channel (up t v) r=P.channel v r
  newAllow : ∀ j : Fin 4,Q.allow (t+j.val)
  rowClean : ∀ s, t-1≤ s → s≤t+4 → Q.upper s=1 ∧ Q.lower s=1 ∧
    Q.before s=Q.before (t-1)
  colClean : ∀ v, t-2≤v → v≤t+3 → ∀ r : ℤ, -1≤r → r≤2 → Q.channel v r=1
  corner : Q.corner=P.corner

end CriticalConicEvenSparse

namespace CriticalConicEvenResearch

/-- For two ordinary consecutive rows, the sign-normalized prefix/suffix
formula changes only in columns s−1 and s+1. -/
theorem consecutive_prefix {s v : ℕ} (a b : ℂ) :
    ((if v≤ s+1 then a else 0)-(if s+1≤v+1 then b else 0))-
      ((if v≤ s then a else 0)-(if s≤v+1 then b else 0)) =
      (if v=s+1 then a else 0)+(if v+1=s then b else 0) := by
  split_ifs <;> first | (exfalso; omega) | ring

/-- Inserting four row and column indices at cut t preserves the original
prefix/suffix entries, except for row t and column t−1. -/
theorem old_prefix_after_gap (t s v : ℕ) (a b : ℂ) :
    let up (i : ℕ) := if i<t then i else i+4
    ((if up v≤up s then a else 0) - (if up s≤up v+1 then b else 0)) =
      ((if v≤ s then a else 0) - (if s≤v+1 then b else 0)) +
      (if s=t ∧ v+1=t then b else 0) := by
  intro up
  have order : up v≤up s ↔ v≤ s := by dsimp [up]; split <;> split <;> omega
  rw [if_congr order rfl rfl]
  by_cases edge : s=t ∧ v+1=t
  · have short : s≤v+1 := by omega
    have long : ¬ up s≤up v+1 := by dsimp [up]; split <;> split <;> omega
    simp only [if_pos edge,if_pos short,if_neg long]
    ring
  · have same : up s≤up v+1 ↔ s≤v+1 := by dsimp [up]; split <;> split <;> omega
    simp only [same,if_neg edge,add_zero]

/-- At an original row, each new ordinary column contributes the same
multiple, except the last inserted column at row t. -/
theorem fresh_prefix_after_gap (t s : ℕ) (j : Fin 4) (a b : ℂ) :
    let up (i : ℕ) := if i<t then i else i+4
    ((if t+j.val≤up s then a else 0) - (if up s≤t+j.val+1 then b else 0)) =
      (if s<t then -b else a) - (if s=t ∧ j.val=3 then b else 0) := by
  intro up
  have hj := j.isLt
  by_cases before : s<t
  · have strict : ¬ t+j.val≤up s := by dsimp [up]; rw [if_pos before]; omega
    have covers : up s≤t+j.val+1 := by dsimp [up]; rw [if_pos before]; omega
    have edge : ¬(s=t ∧ j.val=3) := by omega
    simp [strict,covers,before,edge]
  · have hPrefix : t+j.val≤up s := by dsimp [up]; rw [if_neg before]; omega
    have suffix : up s≤t+j.val+1 ↔ s=t ∧ j.val=3 := by dsimp [up]; rw [if_neg before]; omega
    simp only [hPrefix,ite_true,suffix,if_neg before]

/-- The isolated corner (1,L) is unchanged by an interior four-step gap. -/
theorem old_corner_after_gap {t s v L : ℕ} (interior : 2≤t) (right : t≤L) :
    let up (i : ℕ) := if i<t then i else i+4
    (up s=1 ∧ up v=L+4) ↔ (s=1 ∧ v=L) := by
  intro up
  dsimp [up]
  split <;> split <;> omega

/-- In the large kernel the four fresh unknowns are forced to be
(−x_a,−x_b,x_a,x_b). Restricting to old columns and adjoining these
four coordinates are mutually inverse linear splittings. -/
theorem four_gap_kernel {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℂ) (B : Matrix (I ⊕ Fin 4) (J ⊕ Fin 4) ℂ)
    (anchor : I) (a b : J) (charge edge : I→ℂ)
    (old : ∀ (x : J→ℂ) (y : Fin 4→ℂ) i,
      B.mulVec (Sum.elim x y) (.inl i)= A.mulVec x i+charge i*(∑ j,y j)+edge i*(x b-y 3))
    (fresh : ∀ (x : J→ℂ) (y : Fin 4→ℂ),
      let v := B.mulVec (Sum.elim x y)
      v (.inr 0)-v (.inl anchor)=x a+y 0 ∧ v (.inr 1)-v (.inr 0)=x b+y 1 ∧
      v (.inr 2)-v (.inr 1)=y 0+y 2 ∧ v (.inr 3)-v (.inr 2)=y 1+y 3)
    (x : J→ℂ) (y : Fin 4→ℂ) :
    B.mulVec (Sum.elim x y)=0 ↔ A.mulVec x=0 ∧ y= ![-x a,-x b,x a,x b] := by
  have step := fresh x y
  dsimp only at step
  constructor
  · intro all
    rw [all] at step
    simp only [Pi.zero_apply,sub_zero] at step
    obtain ⟨q₀,q₁,q₂,q₃⟩ := step
    have val : y= ![-x a,-x b,x a,x b] := by
      funext j
      fin_cases j <;> simp <;> first | linear_combination -q₀ | linear_combination -q₁ | linear_combination q₀-q₂ | linear_combination q₁-q₃
    refine ⟨?_,val⟩
    funext i
    have h := old x y i
    rw [all,val] at h
    simpa [Fin.sum_univ_succ] using h.symm
  · rintro ⟨small,rfl⟩
    have before (i) : B.mulVec (Sum.elim x ![-x a,-x b,x a,x b]) (.inl i)=0 := by
      rw [old,small]
      simp [Fin.sum_univ_succ]
    obtain ⟨e,f,g,h⟩ := step
    rw [before] at e
    simp at e f g h
    have f₁ := sub_eq_zero.mp f
    have g₂ := sub_eq_zero.mp g
    have h₃ := sub_eq_zero.mp h
    rw [e] at f₁
    rw [f₁] at g₂
    rw [g₂] at h₃
    funext i
    rcases i with i|j
    · exact before i
    · fin_cases j <;> first | exact e | exact f₁ | exact g₂ | exact h₃

end CriticalConicEvenResearch

namespace CriticalConicEvenResearch

/-- The physical column determined by k,v can be recognized solely from
its residue modulo L+2, using its prescribed full set of representatives. -/
theorem physical_column_index {L a k v n : ℤ} (pos : 5 ≤ L) (acol : 0 ≤ a ∧ a < L)
    (kcol : 0 ≤ k ∧ k < L-1) (vcol : 0 ≤ v ∧ v ≤ L)
    (join : 2*k+a-v=n*L) :
    -1 ≤ k+n ∧ k+n ≤ L ∧ 2*(k+n)=v-a+n*(L+2) := by
  have lower : -1 ≤ n := by
    by_contra! bad
    nlinarith only [join,kcol.1,acol.1,vcol.2,pos,
      mul_le_mul_of_nonneg_right (show n ≤ -2 by omega) (by omega : 0 ≤ L)]
  have upper : n ≤ 2 := by
    by_contra! bad
    nlinarith only [join,kcol.2,acol.2,vcol.1,
      mul_le_mul_of_nonneg_right (show 3 ≤ n by omega) (by omega : 0 ≤ L)]
  exact ⟨by omega,by omega,by nlinarith only [join]⟩

/-- For odd m, symmetry of the doubled column coordinate leaves precisely
one integer in the inclusive range [−1,m−2]. -/
theorem column_probe {m a v p n z : ℤ} (pos : 0 < m) (oddM : Odd m)
    (rep : -1 ≤ p ∧ p ≤ m-2) (phase : 2*p=v-a+n*m) :
    p=z ↔ (-1 ≤ z ∧ z ≤ m-2) ∧ ∃ j : ℤ,v=a+2*z+j*m := by
  constructor
  · rintro rfl
    exact ⟨rep,-n,by nlinarith only [phase]⟩
  · rintro ⟨bound,j,eq⟩
    have scale : 2*(p-z)=(n+j)*m := by nlinarith only [phase,eq]
    have lo : -2 < n+j := by
      by_contra! bad
      nlinarith only [scale,rep.1,bound.2,mul_le_mul_of_nonneg_right bad pos.le]
    have hi : n+j < 2 := by
      by_contra! bad
      nlinarith only [scale,rep.2,bound.1,mul_le_mul_of_nonneg_right bad pos.le]
    obtain ⟨b,hb⟩ := oddM
    have choices : n+j= -1 ∨ n+j=0 ∨ n+j=1 := by omega
    rcases choices with e|e|e <;> rw [e] at scale <;> omega

/-- The exact event congruences for ordinary and end probes and for probes
anchored at the exceptional hub. -/
theorem shift_probe_period (m a v z s : ℤ) :
    (∃ j : ℤ,v=a+2*(z+s*m)+j*m) ↔ ∃ j : ℤ,v=a+2*z+j*m := by
  constructor
  · rintro ⟨j,h⟩
    exact ⟨j+2*s,by nlinarith only [h]⟩
  · rintro ⟨j,h⟩
    exact ⟨j-2*s,by nlinarith only [h]⟩

theorem shift_probe_anchor {m a v c t : ℤ} (anchor : 3*a=c+t*m) (z : ℤ) :
    (∃ j : ℤ,v=a+2*(a+z)+j*m) ↔ ∃ j : ℤ,v=c+2*z+j*m := by
  constructor
  · rintro ⟨j,h⟩
    exact ⟨j+t,by nlinarith only [h,anchor]⟩
  · rintro ⟨j,h⟩
    exact ⟨j-t,by nlinarith only [h,anchor]⟩

theorem short_windings {m v a r : ℤ} (dim : 12 < m)
    (av : 0 ≤ a ∧ a < m) (vv : 0 ≤ v ∧ v < m) (radius : -12 ≤ r ∧ r ≤ 12) :
    (∃ j : ℤ,v=a+r+j*m) ↔ v=a+r ∨ v=a+r+m ∨ v=a+r-m := by
  constructor
  · rintro ⟨j,h⟩
    have lower : -2 < j := by
      by_contra! small
      nlinarith only [h,av.2,vv.1,radius.2,mul_le_mul_of_nonneg_right small (by omega : 0 ≤ m),dim]
    have upper : j < 2 := by
      by_contra! big
      nlinarith only [h,av.1,vv.2,radius.1,mul_le_mul_of_nonneg_right big (by omega : 0 ≤ m),dim]
    have cases : j= -1 ∨ j=0 ∨ j=1 := by omega
    rcases cases with e|e|e <;> rw [e] at h <;> omega
  · rintro (e|e|e)
    · exact ⟨0,by simpa using e⟩
    · exact ⟨1,by simpa using e⟩
    · exact ⟨-1,by nlinarith only [e]⟩

/-- Inserting a clean four-step interval transports every labelled offset
of absolute value at most twelve, including offsets crossing the seam. -/
theorem short_arc_after_gap {m v a t r : ℤ}
    (av : 0 ≤ a ∧ a < m) (vv : 0 ≤ v ∧ v < m) (clean : a+12 < t ∨ t+12 ≤ a)
    (inside : 12 < t ∧ t+12 < m) (radius : -12 ≤ r ∧ r ≤ 12) :
    let up (i : ℤ) := if i < t then i else i+4
    (∃ j : ℤ,v=a+r+j*m) ↔ ∃ j : ℤ,up v=up a+r+j*(m+4) := by
  intro up
  have au : 0 ≤ up a ∧ up a < m+4 := by dsimp [up]; split <;> omega
  have vu : 0 ≤ up v ∧ up v < m+4 := by dsimp [up]; split <;> omega
  rw [short_windings (by omega) av vv radius,short_windings (by omega) au vu radius]
  dsimp [up]
  split <;> split <;> omega

private theorem three_cases {k : ℕ} (h : k < 3) : k=0 ∨ k=1 ∨ k=2 := by omega

/-- The circular gaps between zero, a and the representative of 3a have
one of four parametrizations by two nonnegative integers. -/
theorem anchor_chambers {m a : ℕ} (pos : 0 < m) (inRange : a < m) :
    let c := (3*a)%m
    (∃ x y : ℕ,m=3*x+y ∧ a=x ∧ c=3*x) ∨
    (∃ x y : ℕ,m=3*x+2*y ∧ a=2*x+y ∧ c=3*x+y) ∨
    (∃ x y : ℕ,m=2*x+3*y ∧ a=x+y ∧ c=x) ∨
    (∃ x y : ℕ,m=x+3*y ∧ a=x+2*y ∧ c=x) := by
  intro c
  have cv : c < m := Nat.mod_lt _ pos
  have modEq : m*(3*a/m)+c=3*a := Nat.div_add_mod _ _
  have quot : 3*a/m < 3 := (Nat.div_lt_iff_lt_mul pos).mpr (by omega)
  have cases := three_cases quot
  rcases cases with q|q|q <;> rw [q] at modEq
  · exact Or.inl ⟨a,m-c,by omega,rfl,by omega⟩
  · by_cases ordr : a ≤ c
    · exact Or.inr (Or.inl ⟨c-a,m-c,by omega,by omega,by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c,a-c,by omega,by omega,rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c,m-a,by omega,by omega,rfl⟩))

end CriticalConicEvenResearch

namespace CriticalConicEvenSparse

open CriticalConicEvenResearch

/-- Circular equality at a short signed offset. -/
def arc (m v a z : ℤ) : Prop := ∃ j : ℤ,v=a+z+j*m

private def originTest (m a v z : ℤ) : Prop := (-1 ≤ z ∧ z ≤ m-2) ∧ arc m v a (2*z)
private def seamTest (m a v z : ℤ) : Prop := (-1 ≤ m+z ∧ m+z ≤ m-2) ∧ arc m v a (2*z)
private def hubTest (m a c v z : ℤ) : Prop := (-1 ≤ a+z ∧ a+z ≤ m-2) ∧ arc m v c (2*z)

/-- The column channel written in terms of bounded neighbourhoods of the
labels a and c. It remains defined while c and 3a mod m vary independently. -/
noncomputable def channelZ (m a c v r : ℤ) : ℤ := by
  classical
  exact if (originTest m a v (-1) ∧ r ≤ 0) ∨ (originTest m a v 0 ∧ r < 0) ∨
      (seamTest m a v (-2) ∧ 0 ≤ r) ∨ (seamTest m a v (-3) ∧ 1 ≤ r) ∨
      (seamTest m a v (-4) ∧ 2 ≤ r) then 0
    else if hubTest m a c v (1-r) then 17 else if hubTest m a c v (-r) then 13
    else if hubTest m a c v (-1-r) then 11 else if seamTest m a v (-3-r) then 7
    else if seamTest m a v (-4-r) then 5 else if originTest m a v (1-r) then 3
    else if originTest m a v (-r) then 2 else 1

noncomputable def synthetic (m a c : ℕ) : Profile where
  upper s := (weight m a ((s:ℤ)+1) : ℂ)
  lower s := (weight m a s : ℂ)
  before s := decide (s < a)
  channel v r := (channelZ m a c v r : ℂ)
  allow v := allowed m a v
  corner := (weight m a 0 : ℂ)

lemma position_spec {m : ℤ} (pos : 0 < m) (oddM : Odd m) (a v : ℤ) :
    -1 ≤ position m a v ∧ position m a v ≤ m-2 ∧
      ∃ n : ℤ,2*position m a v=v-a+n*m := by
  let z := (v-a)*((m+1)/2)+1
  change -1 ≤ z%m-1 ∧ z%m-1 ≤ m-2 ∧ ∃ n : ℤ,2*(z%m-1)=v-a+n*m
  have low := Int.emod_nonneg z (ne_of_gt pos)
  have high := Int.emod_lt_of_pos z pos
  refine ⟨by omega,by omega,(v-a)-2*(z/m),?_⟩
  have div := Int.emod_add_mul_ediv z m
  have half : 2*((m+1)/2)=m+1 := by obtain ⟨k,hk⟩ := oddM; omega
  have mult := congrArg (fun d : ℤ => (v-a)*d) half
  change z%m+m*(z/m)=(v-a)*((m+1)/2)+1 at div
  nlinarith only [mult,div]

lemma channel_physical {m a c h v r : ℤ} (pos : 0 < m) (oddM : Odd m)
    (ac : 3*a=c+h*m) (lb : -1 ≤ r) (ub : r ≤ 2) :
    channelZ m a c v r=weight m a (position m a v+r) := by
  let p := position m a v
  obtain ⟨lo,hi,n,phase⟩ := position_spec pos oddM a v
  change -1 ≤ p at lo
  change p ≤ m-2 at hi
  change 2*p=v-a+n*m at phase
  change channelZ m a c v r=weight m a (p+r)
  have test (z : ℤ) := column_probe (z:=z) pos oddM ⟨lo,hi⟩ phase
  have ori (z : ℤ) : originTest m a v z ↔ p=z := (test z).symm
  have seam (z : ℤ) : seamTest m a v z ↔ p=m+z := by
    rw [test]
    apply and_congr_right
    intro _
    symm
    simpa only [arc,one_mul,add_comm z m] using shift_probe_period m a v z 1
  have hub (z : ℤ) : hubTest m a c v z ↔ p=a+z := by
    rw [test]
    exact and_congr_right fun _ => (shift_probe_anchor ac z).symm
  have guard :
      ((p= -1 ∧ r ≤ 0) ∨ (p=0 ∧ r < 0) ∨ (p=m+ -2 ∧ 0 ≤ r) ∨
       (p=m+ -3 ∧ 1 ≤ r) ∨ (p=m+ -4 ∧ 2 ≤ r)) ↔ (p+r < 0 ∨ m-2 ≤ p+r) := by omega
  have g₆ : p=a+(1-r) ↔ p+r=a+1 := by omega
  have g₅ : p=a+ -r ↔ p+r=a := by omega
  have g₄ : p=a+(-1-r) ↔ p+r=a-1 := by omega
  have g₃ : p=m+(-3-r) ↔ p+r=m-3 := by omega
  have g₂ : p=m+(-4-r) ↔ p+r=m-4 := by omega
  have g₁ : p=1-r ↔ p+r=1 := by omega
  have g₀ : p= -r ↔ p+r=0 := by omega
  simp only [channelZ,weight,ori,seam,hub,guard,g₆,g₅,g₄,g₃,g₂,g₁,g₀]

end CriticalConicEvenSparse

namespace CriticalConicEvenSparse

/-- At the true third anchor, the synthetic system has literally the same
entries as the finite integral residue block. -/
theorem coefficient_at_physical {L a : ℕ} (oddL : Odd L) (s v : ℕ) :
    (synthetic (L+2) a ((3*a)%(L+2))).coeff L s v =
      (entry ((L:ℤ)+2) a s v : ℂ) := by
  let m : ℤ := (L:ℤ)+2
  let c : ℤ := ((3*a)%(L+2):ℕ)
  have om : Odd m := by obtain ⟨n,h⟩ := oddL; exact ⟨(n:ℤ)+1,by dsimp [m]; exact_mod_cast (show L+2=2*(n+1)+1 by omega)⟩
  have ac : 3*(a:ℤ)=c+((3*a)/(L+2):ℕ)*m := by
    dsimp [c,m]
    exact_mod_cast (Nat.mod_add_div (3*a) (L+2)).symm.trans (by ring)
  have eval (r : ℤ) (h₁ : -1 ≤ r) (h₂ : r ≤ 2) := channel_physical (v:=(v:ℤ))
    (by dsimp [m]; omega : 0 < m) om ac h₁ h₂
  let o : ℤ := if decide (s<a) then -1 else 0
  have bounds : -1 ≤ o ∧ o ≤ 0 := by dsimp [o]; split <;> omega
  have guard₁ : ((v:ℤ) ≤ s) ↔ v ≤ s := by omega
  have guard₂ : ((s:ℤ) ≤ v+1) ↔ s ≤ v+1 := by omega
  have guard₃ : ((s:ℤ)=1 ∧ (v:ℤ)=m-2) ↔ (s=1 ∧ v=L) := by dsimp [m]; omega
  have delta : position m a v-(if (s:ℤ) < a then 1 else 0)=position m a v+o := by
    by_cases l : s<a
    · have e : (s:ℤ) < a := by omega
      simp [l,e,o,sub_eq_add_neg]
    · have e : ¬ (s:ℤ) < a := by omega
      simp [l,e,o]
  change (if v ≤ s then (weight m a ((s:ℤ)+1):ℂ)*(channelZ m a c v o:ℂ) else 0) -
      (if s ≤ v+1 then (weight m a s:ℂ)*(channelZ m a c v (o+1):ℂ) else 0) +
      (if s=1 ∧ v=L then (weight m a 0:ℂ)*(channelZ m a c v (o+2):ℂ) else 0) =
      (entry m a s v : ℂ)
  rw [eval o (by omega) (by omega),eval (o+1) (by omega) (by omega),
    eval (o+2) (by omega) (by omega)]
  unfold entry
  simp only [delta,guard₁,guard₂,guard₃]
  push_cast
  simp only [add_assoc]

theorem physical_good_iff {L a : ℕ} (oddL : Odd L) :
    (synthetic (L+2) a ((3*a)%(L+2))).good L ↔ Good L a := by
  unfold Profile.good Good
  simp_rw [coefficient_at_physical oddL]
  rfl

end CriticalConicEvenSparse

namespace CriticalConicEvenSparse

open CriticalConicEvenResearch

def upZ (t i : ℤ) := if i < t then i else i+4

lemma cast_up (t i : ℕ) : ((up t i : ℕ) : ℤ)=upZ t i := by
  by_cases lt : i < t
  · simp [up,upZ,lt]
  · simp [up,upZ,lt]

end CriticalConicEvenSparse

namespace CriticalConicEvenSparse.Tight

private def originTest (m a v z : ℤ) : Prop := (-1 ≤ z ∧ z ≤ m-2) ∧ arc m v a (2*z)
private def seamTest (m a v z : ℤ) : Prop := (-1 ≤ m+z ∧ m+z ≤ m-2) ∧ arc m v a (2*z)
private def hubTest (m a c v z : ℤ) : Prop := (-1 ≤ a+z ∧ a+z ≤ m-2) ∧ arc m v c (2*z)

/-- The column channel written in terms of bounded neighbourhoods of the
labels a and c. It remains defined while c and 3a mod m vary independently. -/
private noncomputable def localChannel (m a c v r : ℤ) : ℤ := by
  classical
  exact if (originTest m a v (-1) ∧ r ≤ 0) ∨ (originTest m a v 0 ∧ r < 0) ∨
      (seamTest m a v (-2) ∧ 0 ≤ r) ∨ (seamTest m a v (-3) ∧ 1 ≤ r) ∨
      (seamTest m a v (-4) ∧ 2 ≤ r) then 0
    else if hubTest m a c v (1-r) then 17 else if hubTest m a c v (-r) then 13
    else if hubTest m a c v (-1-r) then 11 else if seamTest m a v (-3-r) then 7
    else if seamTest m a v (-4-r) then 5 else if originTest m a v (1-r) then 3
    else if originTest m a v (-r) then 2 else 1

/-- All four channels are unchanged by preservation of the two anchor
neighbourhoods. This does not require either endpoint to be physical. -/
lemma channel_congr {m m' a a' c c' v v' r : ℤ} (dm : 12 < m) (dm' : 12 < m')
    (low : ∀ z : ℤ, -12 ≤ z → z ≤ 4 → (arc m v a z ↔ arc m' v' a' z))
    (mid : ∀ z : ℤ, -12 ≤ z → z ≤ 4 → (arc m v c z ↔ arc m' v' c' z))
    (ends : ∀ z : ℤ, -3 ≤ z → z ≤ 2 → ((-1 ≤ a+z ∧ a+z ≤ m-2) ↔ (-1 ≤ a'+z ∧ a'+z ≤ m'-2)))
    (lb : -1 ≤ r) (ub : r ≤ 2) : channelZ m a c v r=channelZ m' a' c' v' r := by
  change localChannel m a c v r = localChannel m' a' c' v' r
  have ori (z : ℤ) (a₀ : -6 ≤ z) (a₁ : z ≤ 2) : originTest m a v z ↔ originTest m' a' v' z :=
    and_congr (by omega) (low (2*z) (by omega) (by omega))
  have seam (z : ℤ) (a₀ : -6 ≤ z) (a₁ : z ≤ 1) : seamTest m a v z ↔ seamTest m' a' v' z :=
    and_congr (by omega) (low (2*z) (by omega) (by omega))
  have hub (z : ℤ) (a₀ : -3 ≤ z) (a₁ : z ≤ 2) : hubTest m a c v z ↔ hubTest m' a' c' v' z :=
    and_congr (ends z a₀ a₁) (mid (2*z) (by omega) (by omega))
  simp only [localChannel]
  rw [ori (-1) (by decide) (by decide),ori 0 (by decide) (by decide),
    seam (-2) (by decide) (by decide),seam (-3) (by decide) (by decide),
    seam (-4) (by decide) (by decide),hub (1-r) (by omega) (by omega),
    hub (-r) (by omega) (by omega),hub (-1-r) (by omega) (by omega),
    seam (-3-r) (by omega) (by omega),seam (-4-r) (by omega) (by omega),
    ori (1-r) (by omega) (by omega),ori (-r) (by omega) (by omega)]

lemma channel_one {m a c v r : ℤ}
    (far : ∀ z : ℤ, -12 ≤ z → z ≤ 4 → ¬arc m v a z ∧ ¬arc m v c z)
    (lb : -1 ≤ r) (ub : r ≤ 2) : channelZ m a c v r=1 := by
  change localChannel m a c v r=1
  have ori (z : ℤ) (a₀ : -6 ≤ z) (a₁ : z ≤ 2) : ¬originTest m a v z := fun e =>
    (far (2*z) (by omega) (by omega)).1 e.2
  have seam (z : ℤ) (a₀ : -6 ≤ z) (a₁ : z ≤ 1) : ¬seamTest m a v z := fun e =>
    (far (2*z) (by omega) (by omega)).1 e.2
  have hub (z : ℤ) (a₀ : -3 ≤ z) (a₁ : z ≤ 2) : ¬hubTest m a c v z := fun e =>
    (far (2*z) (by omega) (by omega)).2 e.2
  simp only [localChannel,ori (-1) (by decide) (by decide),ori 0 (by decide) (by decide),
    seam (-2) (by decide) (by decide),seam (-3) (by decide) (by decide),
    seam (-4) (by decide) (by decide),hub (1-r) (by omega) (by omega),
    hub (-r) (by omega) (by omega),hub (-1-r) (by omega) (by omega),
    seam (-3-r) (by omega) (by omega),seam (-4-r) (by omega) (by omega),
    ori (1-r) (by omega) (by omega),ori (-r) (by omega) (by omega),
    false_and,false_or,ite_false]

end CriticalConicEvenSparse.Tight

namespace CriticalConicEvenSparse.Tight

open CriticalConicEvenResearch

private lemma short_arc {m v a t r : ℤ} (av : 0 ≤ a ∧ a < m) (vv : 0 ≤ v ∧ v < m)
    (clean : a+7 ≤ t ∨ t+12 ≤ a) (inside : 7 ≤ t ∧ t+12 ≤ m) (radius : -12 ≤ r ∧ r ≤ 4) :
    arc m v a r ↔ arc (m+4) (upZ t v) (upZ t a) r := by
  have au : 0 ≤ upZ t a ∧ upZ t a < m+4 := by dsimp [upZ]; split <;> omega
  have vu : 0 ≤ upZ t v ∧ upZ t v < m+4 := by dsimp [upZ]; split <;> omega
  have rad : -12 ≤ r ∧ r ≤ 12 := by omega
  unfold arc
  rw [short_windings (by omega) av vv rad,short_windings (by omega) au vu rad]
  dsimp [upZ]; split <;> split <;> omega

private lemma hub_offsets {m a t r : ℤ} (_av : 0 ≤ a ∧ a < m)
    (inside : 7 ≤ t ∧ t+12 ≤ m) (radius : -3 ≤ r ∧ r ≤ 2) :
    (-1 ≤ a+r ∧ a+r ≤ m-2) ↔ (-1 ≤ upZ t a+r ∧ upZ t a+r ≤ m+4-2) := by
  dsimp [upZ]; split <;> omega

private lemma row_offset {m a t s r : ℤ} (inside : 7 ≤ t ∧ t+12 ≤ m)
    (_av : 0 ≤ a ∧ a < m) (_sv : 0 ≤ s ∧ s < m) (clean : a+7 ≤ t ∨ t+12 ≤ a)
    (radius : -1 ≤ r ∧ r ≤ 1) :
    weight (m+4) (upZ t a) (upZ t s+r)=weight m a (s+r) := by
  have endGuard : (upZ t s+r < 0 ∨ m+4-2 ≤ upZ t s+r) ↔ (s+r < 0 ∨ m-2 ≤ s+r) := by
    dsimp [upZ]; split <;> omega
  have atLeft (c : ℤ) (c₀ : 0 ≤ c) (c₁ : c ≤ 1) : upZ t s+r=c ↔ s+r=c := by
    dsimp [upZ]; split <;> omega
  have atRight (c : ℤ) (c₀ : 3 ≤ c) (c₁ : c ≤ 4) : upZ t s+r=m+4-c ↔ s+r=m-c := by
    dsimp [upZ]; split <;> omega
  have atHub (c : ℤ) (c₀ : -1 ≤ c) (c₁ : c ≤ 1) : upZ t s+r=upZ t a+c ↔ s+r=a+c := by
    dsimp [upZ]; split <;> split <;> omega
  have hub₀ := atHub 0 (by decide) (by decide)
  have hub₁ := atHub 1 (by decide) (by decide)
  have hub₂ := atHub (-1) (by decide) (by decide)
  rw [add_zero,add_zero] at hub₀
  simp only [←sub_eq_add_neg] at hub₂
  unfold weight
  simp only [endGuard,hub₁,hub₀,hub₂,atRight 3 (by decide) (by decide),atRight 4 (by decide) (by decide),
    atLeft 1 (by decide) (by decide),atLeft 0 (by decide) (by decide)]

private lemma row_middle {m a t s : ℤ} (inside : 7 ≤ t ∧ t+12 ≤ m)
    (clean : a+7 ≤ t ∨ t+12 ≤ a) (middle : t-1 ≤ s ∧ s ≤ t+5) :
    weight (m+4) (upZ t a) s=1 := by
  unfold weight upZ
  split_ifs <;> omega

private lemma allowed_transport {m a t v : ℤ} (inside : 7 ≤ t ∧ t+12 ≤ m)
    (av : 0 ≤ a ∧ a ≤ m-3) (vv : 0 ≤ v ∧ v ≤ m-2) (clean : a+7 ≤ t ∨ t+12 ≤ a) :
    allowed (m+4) (upZ t a) (upZ t v) ↔ allowed m a v := by
  unfold allowed upZ
  split <;> split <;> omega

private lemma allowed_middle {m a t v : ℤ} (inside : 7 ≤ t ∧ t+12 ≤ m)
    (av : 0 ≤ a ∧ a ≤ m-3) (clean : a+7 ≤ t ∨ t+12 ≤ a) (middle : t ≤ v ∧ v ≤ t+3) :
    allowed (m+4) (upZ t a) v := by
  unfold allowed upZ
  split <;> omega

private lemma near_cut_absent {m a t r v : ℤ} (av : 0 ≤ a ∧ a < m)
    (inside : 7 ≤ t ∧ t+12 ≤ m) (clean : a+7 ≤ t ∨ t+12 ≤ a)
    (radius : -12 ≤ r ∧ r ≤ 4) (middle : t-2 ≤ v ∧ v ≤ t+3) :
    ¬arc (m+4) v (upZ t a) r := by
  have upBounds : 0 ≤ upZ t a ∧ upZ t a < m+4 := by dsimp [upZ]; split <;> omega
  unfold arc
  rw [short_windings (by omega) upBounds (show 0 ≤ v ∧ v < m+4 by omega) (show -12 ≤ r ∧ r ≤ 12 by omega)]
  dsimp [upZ]
  split <;> omega

/-- One clean insertion of four positions transports every actual bounded
channel of the synthetic problem, regardless of the winding of 3a. -/
theorem synthetic_splice {m a c t : ℕ} (av : a+3 ≤ m) (cv : c < m)
    (left : 7 ≤ t) (right : t+12 ≤ m) (cleanA : a+7 ≤ t ∨ t+12 ≤ a)
    (cleanC : c+7 ≤ t ∨ t+12 ≤ c) :
    Splice (m-2) t (synthetic m a c) (synthetic (m+4) (up t a) (up t c)) := by
  have inside : 7 ≤ (t:ℤ) ∧ (t:ℤ)+12 ≤ m := by omega
  have inA : 0 ≤ (a:ℤ) ∧ (a:ℤ) < m := by omega
  have inC : 0 ≤ (c:ℤ) ∧ (c:ℤ) < m := by omega
  have ca : (a:ℤ)+7 ≤ t ∨ (t:ℤ)+12 ≤ a := by omega
  have cc : (c:ℤ)+7 ≤ t ∨ (t:ℤ)+12 ≤ c := by omega
  refine ⟨by omega,by omega,?_,?_,?_,?_,?_,?_⟩
  · intro s below
    have bounds : 0 ≤ (s:ℤ) ∧ (s:ℤ) < m := by omega
    have ru := row_offset inside inA bounds ca (r:=1) (by decide)
    have rl := row_offset inside inA bounds ca (r:=0) (by decide)
    simp only [add_zero] at rl
    have order : up t s < up t a ↔ s < a := by dsimp [up]; split <;> split <;> omega
    simp only [synthetic,Nat.cast_add,Nat.cast_ofNat,cast_up,ru,rl,order,and_self]
  · intro v below
    have vv : 0 ≤ (v:ℤ) ∧ (v:ℤ) ≤ (m:ℤ)-2 := by omega
    have vv' : 0 ≤ (v:ℤ) ∧ (v:ℤ) < m := by omega
    have column := allowed_transport inside (a:=(a:ℤ)) (by omega) vv ca
    simp only [synthetic,Nat.cast_add,Nat.cast_ofNat,cast_up,column,iff_self,true_and]
    intro r lb ub
    congr 1
    apply Eq.symm
    apply channel_congr (by omega) (by omega) _ _ _ lb ub
    · intro z z₀ z₁
      exact short_arc inA vv' ca inside ⟨z₀,z₁⟩
    · intro z z₀ z₁
      exact short_arc inC vv' cc inside ⟨z₀,z₁⟩
    · intro z z₀ z₁
      exact hub_offsets inA inside ⟨z₀,z₁⟩
  · intro j
    have pos := j.isLt
    change allowed (m+4:ℕ) (up t a) (t+j.val:ℕ)
    push_cast
    rw [cast_up]
    exact allowed_middle inside (by omega) ca (by omega)
  · intro s ls us
    have rr := row_middle inside ca (s:=(s:ℤ)+1) (by omega)
    have rl := row_middle inside ca (s:=(s:ℤ)) (by omega)
    have order : (s < up t a) ↔ (t-1 < up t a) := by dsimp [up]; split <;> omega
    simp only [synthetic,Nat.cast_add,Nat.cast_ofNat,cast_up,rr,rl,order,Int.cast_one,and_self]
  · intro v l₀ l₁ r lb ub
    change (channelZ (m+4:ℕ) (up t a) (up t c) v r : ℂ)=1
    push_cast
    rw [cast_up,cast_up]
    norm_cast
    apply channel_one _ lb ub
    intro z z₀ z₁
    exact ⟨near_cut_absent inA inside ca ⟨z₀,z₁⟩ (by omega),
      near_cut_absent inC inside cc ⟨z₀,z₁⟩ (by omega)⟩
  · have eq := row_offset inside inA (s:=0) (by omega) ca (r:=0) (by decide)
    have uz : upZ t 0=0 := by dsimp [upZ]; rw [if_pos (by omega)]
    simp only [uz,add_zero] at eq
    simp only [synthetic,Nat.cast_add,Nat.cast_ofNat,cast_up,eq]


end CriticalConicEvenSparse.Tight

namespace CriticalConicEvenSparse

/-- Keep the two old intervals in their order and put four fresh elements
immediately before the old position t. The cut may coincide with an end. -/
theorem ordered_gap_equiv (N t : ℕ) (cut : t≤ N) :
    ∃ e : (Fin N ⊕ Fin 4) ≃ Fin (N+4),
      (∀ i,(e (.inl i)).val=up t i.val) ∧ (∀ j,(e (.inr j)).val=t+j.val) := by
  let f : Fin N ⊕ Fin 4 → Fin (N+4) := Sum.elim
    (fun i => ⟨up t i.val,by dsimp [up]; split <;> omega⟩)
    (fun j => ⟨t+j.val,by omega⟩)
  have inj : Function.Injective f := by
    rintro (i|j) (k|l) eq
    all_goals have h := congrArg Fin.val eq
    · change up t i.val=up t k.val at h
      apply congrArg Sum.inl
      apply Fin.ext
      dsimp [up] at h
      split at h <;> split at h <;> omega
    · change up t i.val=t+l.val at h
      dsimp [up] at h
      split at h <;> omega
    · change t+j.val=up t k.val at h
      dsimp [up] at h
      split at h <;> omega
    · apply congrArg Sum.inr
      apply Fin.ext
      change t+j.val=t+l.val at h
      omega
  have bij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp⟩
  exact ⟨Equiv.ofBijective f bij,fun _ => rfl,fun _ => rfl⟩

private theorem old_coefficient {L t s v : ℕ} {P Q : Profile}
    (S : Splice L t P Q) (hs : s < L) (hv : v≤ L) :
    Q.coeff (L+4) (up t s) (up t v)=P.coeff L s v+
      (if s=t ∧ v+1=t then P.lower s else 0) := by
  let off : ℤ := if P.before s then -1 else 0
  have bounds : -1≤ off ∧ off+2≤2 := by dsimp [off];split <;> omega
  obtain ⟨high,low,phase⟩ := S.row s hs
  have col := (S.col v hv).2
  have u := col off (by omega) (by omega)
  have l := col (off+1) (by omega) (by omega)
  have c := col (off+2) (by omega) (by omega)
  have corner := CriticalConicEvenResearch.old_corner_after_gap (s:=s) (v:=v) (L:=L) (t:=t)
    (by have := S.left;omega) (by have := S.right;omega)
  have old := CriticalConicEvenResearch.old_prefix_after_gap t s v
    (P.upper s*P.channel v off) (P.lower s*P.channel v (off+1))
  dsimp only at old
  have clean : (if s=t ∧ v+1=t then P.lower s*P.channel v (off+1) else 0)=
      (if s=t ∧ v+1=t then P.lower s else 0) := by
    split_ifs with e
    · have cut : up t v=v := if_pos (by omega)
      have ordinary := S.colClean v (by omega) (by omega) (off+1) (by omega) (by omega)
      rw [← l,cut,ordinary,mul_one]
    · rfl
  rw [clean] at old
  dsimp only [Profile.coeff]
  rw [phase,high,low,S.corner]
  change ((if up t v≤ up t s then P.upper s*Q.channel (up t v) off else 0)-
      (if up t s≤ up t v+1 then P.lower s*Q.channel (up t v) (off+1) else 0)+
      (if up t s=1 ∧ up t v=L+4 then P.corner*Q.channel (up t v) (off+2) else 0))=_
  rw [u,l,c]
  simp only [show (up t s=1 ∧ up t v=L+4)↔(s=1 ∧ v=L) from corner]
  have together := congrArg (fun z : ℂ => z+(if s=1 ∧ v=L then P.corner*P.channel v (off+2) else 0)) old
  refine together.trans ?_
  dsimp only [off]
  abel

private theorem fresh_coefficient {L t s : ℕ} {P Q : Profile}
    (S : Splice L t P Q) (hs : s < L) (j : Fin 4) :
    Q.coeff (L+4) (up t s) (t+j.val)=
      (if s < t then -P.lower s else P.upper s)-(if s=t ∧ j.val=3 then P.lower s else 0) := by
  let off : ℤ := if P.before s then -1 else 0
  have bounds : -1≤ off ∧ off+2≤2 := by dsimp [off];split <;> omega
  obtain ⟨high,low,phase⟩ := S.row s hs
  have clean := S.colClean (t+j.val) (by omega) (by omega)
  have away : t+j.val≠L+4 := by have := S.right;omega
  dsimp only [Profile.coeff]
  rw [phase,high,low,if_neg (show ¬(up t s=1 ∧ t+j.val=L+4) by omega),add_zero]
  change ((if t+j.val≤ up t s then P.upper s*Q.channel (t+j.val) off else 0)-
    (if up t s≤ t+j.val+1 then P.lower s*Q.channel (t+j.val) (off+1) else 0))=_
  rw [clean _ (by omega) (by omega),clean _ (by omega) (by omega),mul_one,mul_one]
  exact CriticalConicEvenResearch.fresh_prefix_after_gap t s j _ _

private theorem steady_difference {L t s v : ℕ} {P Q : Profile}
    (S : Splice L t P Q) (h₁ : t-1≤ s) (h₂ : s≤ t+2) :
    Q.coeff (L+4) (s+1) v-Q.coeff (L+4) s v=
      (if v=s+1 then (1:ℂ) else 0)+(if v+1=s then 1 else 0) := by
  have lo := S.rowClean s h₁ (by omega)
  have hi := S.rowClean (s+1) (by omega) (by omega)
  have cut := S.left
  let off : ℤ := if Q.before (t-1) then -1 else 0
  have bounds : -1≤ off ∧ off+2≤2 := by dsimp [off];split <;> omega
  dsimp only [Profile.coeff]
  rw [lo.1,lo.2.1,lo.2.2,hi.1,hi.2.1,hi.2.2,
    if_neg (show ¬(s=1 ∧ v=L+4) by omega),if_neg (show ¬(s+1=1 ∧ v=L+4) by omega)]
  simp only [one_mul,add_zero]
  change ((if v≤ s+1 then Q.channel v off else 0)-(if s+1≤ v+1 then Q.channel v (off+1) else 0))-
    ((if v≤ s then Q.channel v off else 0)-(if s≤ v+1 then Q.channel v (off+1) else 0))=_
  rw [CriticalConicEvenResearch.consecutive_prefix]
  split_ifs with h <;> first | rfl | omega | simp [S.colClean v (by omega) (by omega) off (by omega) (by omega),
    S.colClean v (by omega) (by omega) (off+1) (by omega) (by omega)]

end CriticalConicEvenSparse

namespace CriticalConicEvenSparse

private theorem reindexed_difference {L t : ℕ} {P Q : Profile} (S : Splice L t P Q)
    {I J : Type*} [Fintype J] [DecidableEq J] (row : I ≃ Fin (L+4)) (col : J ≃ Fin (L+4+1))
    (M : Matrix I J ℂ) (entry : ∀ i j,M i j=Q.coeff (L+4) (row i).val (col j).val)
    (z : J→ℂ) (s : ℕ) (lo : t-1≤ s) (hi : s≤ t+2) (i j : I) (a b : J)
    (ri : (row i).val=s) (rj : (row j).val=s+1)
    (ca : (col a).val+1=s) (cb : (col b).val=s+1) :
    M.mulVec z j-M.mulVec z i=z a+z b := by
  change (∑ l,M j l*z l)-(∑ l,M i l*z l)=_
  rw [← Finset.sum_sub_distrib]
  have delta (l : J) : M j l*z l-M i l*z l =
      (if l=b then z l else 0)+(if l=a then z l else 0) := by
    have high : (col l).val=s+1 ↔ l=b :=
      ⟨fun he => col.injective (Fin.ext (he.trans cb.symm)),fun he => he ▸ cb⟩
    have low : (col l).val+1=s ↔ l=a :=
      ⟨fun he => col.injective (Fin.ext (by omega)),fun he => he ▸ ca⟩
    rw [← sub_mul,entry,entry,ri,rj,steady_difference S lo hi,add_mul]
    simp only [high,low,ite_mul,one_mul,zero_mul]
  simp only [delta,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,add_comm]

/-- In the forward and reverse linear maps the new coordinates are fixed
by the old two coordinates next to the cut. The ambient vector is displayed
on its actual ordered columns. -/
theorem ordered_gap_kernel {L t : ℕ} {P Q : Profile} (S : Splice L t P Q) :
    let a : Fin (L+1) := ⟨t-2,by have := S.right;omega⟩
    let b : Fin (L+1) := ⟨t-1,by have := S.right;omega⟩
    ∃ col : (Fin (L+1) ⊕ Fin 4) ≃ Fin (L+4+1),
      (∀ j,(col (.inl j)).val=up t j.val) ∧ (∀ j,(col (.inr j)).val=t+j.val) ∧
      ∀ (x : Fin (L+1)→ℂ) (y : Fin 4→ℂ),
      (∀ s : Fin (L+4),(∑ v : Fin (L+4+1), Q.coeff (L+4) s.val v.val*(Sum.elim x y (col.symm v)))=0) ↔
      (∀ s : Fin L,(∑ v : Fin (L+1),P.coeff L s.val v.val*x v)=0) ∧
        y= ![-x a,-x b,x a,x b] := by
  classical
  intro a b
  have left := S.left
  have right := S.right
  obtain ⟨row,rowOld,rowNew⟩ := ordered_gap_equiv L t (by omega)
  obtain ⟨col,colOld,colNew⟩ := ordered_gap_equiv (L+1) t (by omega)
  let A : Matrix (Fin L) (Fin (L+1)) ℂ := fun s v => P.coeff L s.val v.val
  let M : Matrix (Fin L ⊕ Fin 4) (Fin (L+1) ⊕ Fin 4) ℂ :=
    fun s v => Q.coeff (L+4) (row s).val (col v).val
  let anchor : Fin L := ⟨t-1,by omega⟩
  let charge (s : Fin L) := if s.val<t then -P.lower s.val else P.upper s.val
  let edge (s : Fin L) := if s.val=t then P.lower s.val else 0
  have oldOld (s : Fin L) (v : Fin (L+1)) :
      M (.inl s) (.inl v)=A s v+(if v=b then edge s else 0) := by
    dsimp only [M,A]
    rw [rowOld,colOld,old_coefficient S s.isLt (by omega)]
    have cond : v.val+1=t ↔ v=b :=
      ⟨fun h => Fin.ext (show v.val=t-1 by omega),fun h => by rw [h];change t-1+1=t;omega⟩
    simp only [cond,edge]
    split_ifs <;> tauto
  have oldNew (s : Fin L) (j : Fin 4) :
      M (.inl s) (.inr j)=charge s-(if j=3 then edge s else 0) := by
    dsimp only [M,charge,edge]
    rw [rowOld,colNew,fresh_coefficient S s.isLt]
    have cond : j.val=3 ↔ j=3 := ⟨fun h => Fin.ext h,fun h => h ▸ rfl⟩
    simp only [cond]
    split_ifs <;> tauto
  have old (x : Fin (L+1)→ℂ) (y : Fin 4→ℂ) (i : Fin L) :
      M.mulVec (Sum.elim x y) (.inl i)=A.mulVec x i+
        charge i*(∑ j,y j)+edge i*(x b-y 3) := by
    change (∑ v,M (Sum.inl i) v*Sum.elim x y v)=
      (∑ v,A i v*x v)+charge i*(∑ j,y j)+edge i*(x b-y 3)
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr,oldOld,oldNew,add_mul,sub_mul,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,ite_mul,zero_mul,
      Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.mul_sum]
    ring
  have rowAnchor : (row (.inl anchor)).val=t-1 := by
    rw [rowOld]
    exact if_pos (show t-1<t by omega)
  have colA : (col (.inl a)).val=t-2 := by
    rw [colOld]
    exact if_pos (show t-2<t by omega)
  have colB : (col (.inl b)).val=t-1 := by
    rw [colOld]
    exact if_pos (show t-1<t by omega)
  have fresh (x : Fin (L+1)→ℂ) (y : Fin 4→ℂ) :
      let v := M.mulVec (Sum.elim x y)
      v (.inr 0)-v (.inl anchor)=x a+y 0 ∧ v (.inr 1)-v (.inr 0)=x b+y 1 ∧
      v (.inr 2)-v (.inr 1)=y 0+y 2 ∧ v (.inr 3)-v (.inr 2)=y 1+y 3 := by
    let step := reindexed_difference S row col M (fun _ _ => rfl) (Sum.elim x y)
    refine ⟨step (t-1) (by omega) (by omega) (.inl anchor) (.inr 0) (.inl a) (.inr 0) rowAnchor ?_ ?_ ?_,
      step t (by omega) (by omega) (.inr 0) (.inr 1) (.inl b) (.inr 1) ?_ ?_ ?_ ?_,
      step (t+1) (by omega) (by omega) (.inr 1) (.inr 2) (.inr 0) (.inr 2) ?_ ?_ ?_ ?_,
      step (t+2) (by omega) (by omega) (.inr 2) (.inr 3) (.inr 1) (.inr 3) ?_ ?_ ?_ ?_⟩
    all_goals first | (rw [rowNew];omega) | (rw [colNew];omega) | (rw [colA];omega) | (rw [colB];omega)
  refine ⟨col,colOld,colNew,?_⟩
  intro x y
  let z := Sum.elim x y
  have repr (s : Fin L ⊕ Fin 4) :
      M.mulVec z s=∑ v : Fin (L+4+1),Q.coeff (L+4) (row s).val v.val*z (col.symm v) := by
    change (∑ v,Q.coeff (L+4) (row s).val (col v).val*z v)=_
    simpa only [col.symm_apply_apply] using
      col.sum_comp (fun v => Q.coeff (L+4) (row s).val v.val*z (col.symm v))
  have kernel := CriticalConicEvenResearch.four_gap_kernel A M anchor a b charge edge old fresh x y
  constructor
  · intro h
    have all : M.mulVec z=0 := funext (fun s => (repr s).trans (h (row s)))
    obtain ⟨sml,coords⟩ := kernel.mp all
    exact ⟨fun s => congrFun sml s,coords⟩
  · rintro ⟨small,coords⟩ s
    obtain ⟨s,rfl⟩ := row.surjective s
    have all := kernel.mpr ⟨funext small,coords⟩
    exact (repr s).symm.trans (congrFun all s)

/-- Inserting four clean positions preserves and reflects zero kernel on
the allowed columns, using the original row and column order. -/
theorem good_iff_after_gap {L t : ℕ} {P Q : Profile} (S : Splice L t P Q) :
    P.good L ↔ Q.good (L+4) := by
  classical
  obtain ⟨col,old,fresh,ker⟩ := ordered_gap_kernel S
  let a : Fin (L+1) := ⟨t-2,by have := S.right;omega⟩
  let b : Fin (L+1) := ⟨t-1,by have := S.right;omega⟩
  constructor
  · intro small w allowed rows
    let x (i : Fin (L+1)) := w (col (.inl i))
    let y (j : Fin 4) := w (col (.inr j))
    have transport (v : Fin (L+4+1)) : Sum.elim x y (col.symm v)=w v := by
      obtain ⟨i|j,rfl⟩ := col.surjective v <;> simp only [col.symm_apply_apply,Sum.elim_inl,Sum.elim_inr] <;> rfl
    have null := (ker x y).mp (by simpa only [transport] using rows)
    have x0 : x=0 := small x (fun v hv => allowed (col (.inl v)) (by
      rw [old];exact fun h => hv ((S.col v.val (by omega)).1.mp h))) null.1
    have y0 : y=0 := by
      rw [null.2,x0]
      funext j
      fin_cases j <;> simp
    funext v
    obtain ⟨i|j,rfl⟩ := col.surjective v
    · exact congrFun x0 i
    · exact congrFun y0 j
  · intro large x allowed rows
    let y : Fin 4→ℂ := ![-x a,-x b,x a,x b]
    let w (v : Fin (L+4+1)) := Sum.elim x y (col.symm v)
    have w0 : w=0 := large w (by
      intro v bad
      obtain ⟨i|j,rfl⟩ := col.surjective v
      · simpa only [w,col.symm_apply_apply,Sum.elim_inl] using
          allowed i (fun permissible => bad (by rw [old];exact (S.col i.val (by omega)).1.mpr permissible))
      · exact (bad (by rw [fresh];exact S.newAllow j)).elim)
      ((ker x y).mpr ⟨rows,rfl⟩)
    funext i
    simpa only [w,col.symm_apply_apply,Sum.elim_inl,Pi.zero_apply] using congrFun w0 (col (.inl i))

end CriticalConicEvenSparse

namespace CriticalConicEvenSparse.Tight

/-- A parameter greater than 22 is reduced to the congruent value in 19..22.
The distance to the original value is a nonnegative multiple of four. -/
theorem chamber_representative (n : ℕ) :
    ∃ b k : ℕ,b≤22 ∧ n=b+4*k ∧ (k=0 ∨ 19≤b) := by
  by_cases h : n≤22
  · exact ⟨n,0,h,by omega,Or.inl rfl⟩
  · let b := 19+(n-19)%4
    let k := (n-19)/4
    have split := Nat.div_add_mod (n-19) 4
    exact ⟨b,k,by dsimp [b]; omega,by dsimp [b,k]; omega,Or.inr (by dsimp [b]; omega)⟩

private theorem grow_by_fours (A : ℕ→Prop) (step : ∀ x,19≤x → A x → A (x+4))
    {x n : ℕ} (room : n=0 ∨ 19≤x) (start : A x) : A (x+4*n) := by
  rcases room with rfl|room
  · simpa only [Nat.mul_zero,Nat.add_zero] using start
  · induction n with
    | zero => simpa only [Nat.mul_zero,Nat.add_zero] using start
    | succ n ih =>
      have next := step (x+4*n) (by omega) ih
      exact (show x+4*n+4=x+4*(n+1) by omega) ▸ next

private theorem up_left {i t : ℕ} (h : i<t) : up t i=i := if_pos h
private theorem up_right {i t : ℕ} (h : t≤ i) : up t i=i+4 := if_neg (by omega)

/-- With anchors in increasing order, arbitrarily many insertions in each
long gap can be certified from one elementary insertion with margins seven and twelve.
An unchanged gap can have any size, including zero. -/
theorem stretch_ordered_gaps (P : ℕ→ℕ→ℕ→Prop)
    (step : ∀ m a c t : ℕ,7≤t → t+12≤ m →
      (a+7≤t ∨ t+12≤a) → (c+7≤t ∨ t+12≤c) →
      P m a c → P (m+4) (up t a) (up t c))
    (x y z i j k : ℕ) (rx : i=0 ∨ 19≤x) (ry : j=0 ∨ 19≤y) (rz : k=0 ∨ 19≤z)
    (start : P (x+y+z) x (x+y)) :
    P ((x+4*i)+(y+4*j)+(z+4*k)) (x+4*i) ((x+4*i)+(y+4*j)) := by
  let gap (a b c : ℕ) := P (a+b+c) a (a+b)
  have before (a b c : ℕ) (room : 19≤a) (old : gap a b c) : gap (a+4) b c := by
    have next := step (a+b+c) a (a+b) 7 (by omega) (by omega)
      (.inr (by omega)) (.inr (by omega)) old
    rw [up_right (by omega : 7≤a),up_right (by omega : 7≤a+b)] at next
    change P ((a+4)+b+c) (a+4) ((a+4)+b)
    convert! next using 1 <;> omega
  have between (a b c : ℕ) (room : 19≤b) (old : gap a b c) : gap a (b+4) c := by
    have next := step (a+b+c) a (a+b) (a+7) (by omega) (by omega)
      (.inl (by omega)) (.inr (by omega)) old
    rw [up_left (by omega : a<a+7),up_right (by omega : a+7≤a+b)] at next
    change P (a+(b+4)+c) a (a+(b+4))
    convert! next using 1
    omega
  have afterBoth (a b c : ℕ) (room : 19≤c) (old : gap a b c) : gap a b (c+4) := by
    have next := step (a+b+c) a (a+b) (a+b+7) (by omega) (by omega)
      (.inl (by omega)) (.inl (by omega)) old
    rw [up_left (by omega : a<a+b+7),up_left (by omega : a+b<a+b+7)] at next
    change P (a+b+(c+4)) a (a+b)
    exact next
  have lx := grow_by_fours (fun a => gap a y z) (fun a => before a y z) rx start
  have ly := grow_by_fours (fun b => gap (x+4*i) b z) (fun b => between (x+4*i) b z) ry lx
  exact grow_by_fours (fun c => gap (x+4*i) (y+4*j) c) (afterBoth (x+4*i) (y+4*j)) rz ly

end CriticalConicEvenSparse.Tight

namespace CriticalConicEvenSparse.Tight

/-- The four finite chambers up to coordinate 22 imply the property for all
odd sizes and physical anchors. Each enlargement is a sequence of clean
four-position insertions; its intermediate anchors need not be physical. -/
theorem chamber_induction (P : ℕ→ℕ→ℕ→Prop)
    (insert : ∀ m a c t : ℕ,9≤ m → Odd m → a+3≤ m → c< m →
      7≤t → t+12≤ m → (a+7≤t ∨ t+12≤a) → (c+7≤t ∨ t+12≤c) →
      P m a c → P (m+4) (up t a) (up t c))
    (base : ∀ m a x y : ℕ,9≤ m → Odd m → a+3≤ m → x≤22 → y≤22 →
      ((m=3*x+y ∧ a=x) ∨ (m=3*x+2*y ∧ a=2*x+y) ∨
       (m=2*x+3*y ∧ a=x+y) ∨ (m=x+3*y ∧ a=x+2*y)) → P m a ((3*a)%m)) :
    ∀ m a : ℕ,9≤ m → Odd m → a+3≤ m → P m a ((3*a)%m) := by
  let R (m a c : ℕ) := 9≤ m ∧ m%2=1 ∧ a+3≤ m ∧ c< m ∧ P m a c
  have move (m a c t : ℕ) (near : 7≤t) (far : t+12≤ m)
      (ax : a+7≤t ∨ t+12≤a) (cx : c+7≤t ∨ t+12≤c)
      (old : R m a c) : R (m+4) (up t a) (up t c) := by
    obtain ⟨hm,mo,ha,hc,H⟩ := old
    have newP := insert m a c t hm (Nat.odd_iff.mpr mo) ha hc near far ax cx H
    refine ⟨by omega,by omega,?_,?_,newP⟩ <;> dsimp [up] <;> split <;> omega
  have swapped (m a c t : ℕ) (near : 7≤t) (far : t+12≤ m)
      (ax : a+7≤t ∨ t+12≤a) (cx : c+7≤t ∨ t+12≤c)
      (old : R m c a) : R (m+4) (up t c) (up t a) := move m c a t near far cx ax old
  let family (m a x y : ℕ) :=
    (m=3*x+y ∧ a=x) ∨ (m=3*x+2*y ∧ a=2*x+y) ∨
      (m=2*x+3*y ∧ a=x+y) ∨ (m=x+3*y ∧ a=x+2*y)
  have seed (m a c x y j : ℕ) (hm : 9≤ m) (mo : m%2=1) (ha : a+3≤ m) (hc : c< m)
      (hx : x≤22) (hy : y≤22) (zone : family m a x y) (phase : 3*a=c+m*j) : R m a c := by
    have z := base m a x y hm (Nat.odd_iff.mpr mo) ha hx hy zone
    rw [phase,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hc] at z
    exact ⟨hm,mo,ha,hc,z⟩
  have all (m a c : ℕ) (hm : 9≤ m) (mo : m%2=1) (ha : a+3≤ m) (hc : c< m) (zones :
      (∃ x y : ℕ,m=3*x+y ∧ a=x ∧ c=3*x) ∨
      (∃ x y : ℕ,m=3*x+2*y ∧ a=2*x+y ∧ c=3*x+y) ∨
      (∃ x y : ℕ,m=2*x+3*y ∧ a=x+y ∧ c=x) ∨
      (∃ x y : ℕ,m=x+3*y ∧ a=x+2*y ∧ c=x)) : P m a c := by
    rcases zones with ⟨x,y,mm,aa,cc⟩|⟨x,y,mm,aa,cc⟩|⟨x,y,mm,aa,cc⟩|⟨x,y,mm,aa,cc⟩
    · obtain ⟨x₀,i,bx,expandX,bigX⟩ := chamber_representative x
      obtain ⟨y₀,j,by₀,expandY,bigY⟩ := chamber_representative y
      let A := x₀
      let B := 2*x₀
      let C := y₀
      let p := i
      let q := 2*i
      let r := j
      have valid : 9≤A+B+C ∧ (A+B+C)%2=1 ∧ (A)+3≤A+B+C ∧ (A+B)<A+B+C := by
        dsimp only [A,B,C]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have room : (p=0 ∨ 19≤A) ∧ (q=0 ∨ 19≤B) ∧ (r=0 ∨ 19≤C) := by
        dsimp only [A,B,C,p,q,r]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have small : R (A+B+C) (A) (A+B) := by
        apply seed (A+B+C) (A) (A+B) x₀ y₀ 0 valid.1 valid.2.1 valid.2.2.1 valid.2.2.2 bx by₀
        · dsimp only [family,A,B,C]
          exact Or.inl ⟨by omega,by omega⟩
        · dsimp only [A,B,C]
          omega
      have expanded := stretch_ordered_gaps R move A B C p q r room.1 room.2.1 room.2.2 small
      have fm : m=(A+4*p)+(B+4*q)+(C+4*r) := by dsimp only [A,B,C,p,q,r]; omega
      have fa : a=A+4*p := by dsimp only [A,B,p,q]; omega
      have fc : c=(A+4*p)+(B+4*q) := by dsimp only [A,B,p,q]; omega
      rw [fm,fa,fc]
      exact expanded.2.2.2.2
    · obtain ⟨x₀,i,bx,expandX,bigX⟩ := chamber_representative x
      obtain ⟨y₀,j,by₀,expandY,bigY⟩ := chamber_representative y
      let A := 2*x₀+y₀
      let B := x₀
      let C := y₀
      let p := 2*i+j
      let q := i
      let r := j
      have valid : 9≤A+B+C ∧ (A+B+C)%2=1 ∧ (A)+3≤A+B+C ∧ (A+B)<A+B+C := by
        dsimp only [A,B,C]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have room : (p=0 ∨ 19≤A) ∧ (q=0 ∨ 19≤B) ∧ (r=0 ∨ 19≤C) := by
        dsimp only [A,B,C,p,q,r]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have small : R (A+B+C) (A) (A+B) := by
        apply seed (A+B+C) (A) (A+B) x₀ y₀ 1 valid.1 valid.2.1 valid.2.2.1 valid.2.2.2 bx by₀
        · dsimp only [family,A,B,C]
          exact Or.inr (.inl ⟨by omega,by omega⟩)
        · dsimp only [A,B,C]
          omega
      have expanded := stretch_ordered_gaps R move A B C p q r room.1 room.2.1 room.2.2 small
      have fm : m=(A+4*p)+(B+4*q)+(C+4*r) := by dsimp only [A,B,C,p,q,r]; omega
      have fa : a=A+4*p := by dsimp only [A,B,p,q]; omega
      have fc : c=(A+4*p)+(B+4*q) := by dsimp only [A,B,p,q]; omega
      rw [fm,fa,fc]
      exact expanded.2.2.2.2
    · obtain ⟨x₀,i,bx,expandX,bigX⟩ := chamber_representative x
      obtain ⟨y₀,j,by₀,expandY,bigY⟩ := chamber_representative y
      let A := x₀
      let B := y₀
      let C := x₀+2*y₀
      let p := i
      let q := j
      let r := i+2*j
      have valid : 9≤A+B+C ∧ (A+B+C)%2=1 ∧ (A+B)+3≤A+B+C ∧ (A)<A+B+C := by
        dsimp only [A,B,C]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have room : (p=0 ∨ 19≤A) ∧ (q=0 ∨ 19≤B) ∧ (r=0 ∨ 19≤C) := by
        dsimp only [A,B,C,p,q,r]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have small : R (A+B+C) (A+B) (A) := by
        apply seed (A+B+C) (A+B) (A) x₀ y₀ 1 valid.1 valid.2.1 valid.2.2.1 valid.2.2.2 bx by₀
        · dsimp only [family,A,B,C]
          exact Or.inr (.inr (.inl ⟨by omega,by omega⟩))
        · dsimp only [A,B,C]
          omega
      have expanded := stretch_ordered_gaps (fun m a c => R m c a) swapped A B C p q r room.1 room.2.1 room.2.2 small
      have fm : m=(A+4*p)+(B+4*q)+(C+4*r) := by dsimp only [A,B,C,p,q,r]; omega
      have fa : a=(A+4*p)+(B+4*q) := by dsimp only [A,B,p,q]; omega
      have fc : c=A+4*p := by dsimp only [A,B,p,q]; omega
      rw [fm,fa,fc]
      exact expanded.2.2.2.2
    · obtain ⟨x₀,i,bx,expandX,bigX⟩ := chamber_representative x
      obtain ⟨y₀,j,by₀,expandY,bigY⟩ := chamber_representative y
      let A := x₀
      let B := 2*y₀
      let C := y₀
      let p := i
      let q := 2*j
      let r := j
      have valid : 9≤A+B+C ∧ (A+B+C)%2=1 ∧ (A+B)+3≤A+B+C ∧ (A)<A+B+C := by
        dsimp only [A,B,C]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have room : (p=0 ∨ 19≤A) ∧ (q=0 ∨ 19≤B) ∧ (r=0 ∨ 19≤C) := by
        dsimp only [A,B,C,p,q,r]
        rcases bigX with hx|hx <;> rcases bigY with hy|hy <;> omega
      have small : R (A+B+C) (A+B) (A) := by
        apply seed (A+B+C) (A+B) (A) x₀ y₀ 2 valid.1 valid.2.1 valid.2.2.1 valid.2.2.2 bx by₀
        · dsimp only [family,A,B,C]
          exact Or.inr (.inr (.inr ⟨by omega,by omega⟩))
        · dsimp only [A,B,C]
          omega
      have expanded := stretch_ordered_gaps (fun m a c => R m c a) swapped A B C p q r room.1 room.2.1 room.2.2 small
      have fm : m=(A+4*p)+(B+4*q)+(C+4*r) := by dsimp only [A,B,C,p,q,r]; omega
      have fa : a=(A+4*p)+(B+4*q) := by dsimp only [A,B,p,q]; omega
      have fc : c=A+4*p := by dsimp only [A,B,p,q]; omega
      rw [fm,fa,fc]
      exact expanded.2.2.2.2
  intro m a hm mo ha
  exact all m a ((3*a)%m) hm (Nat.odd_iff.mp mo) ha (Nat.mod_lt _ (by omega))
    (CriticalConicEvenResearch.anchor_chambers (by omega) (by omega))

end CriticalConicEvenSparse.Tight

namespace CriticalConicEvenSparse.Tight

/-- The finite local rank certificates at the bounded independent gap lengths
imply full column rank at every physical residue in every odd width L≥7. -/
theorem all_good_of_representatives
    (finite : ∀ L a x y : ℕ, 7 ≤ L → Odd L → a < L → x ≤ 22 → y ≤ 22 →
      ((L+2=3*x+y ∧ a=x) ∨ (L+2=3*x+2*y ∧ a=2*x+y) ∨
       (L+2=2*x+3*y ∧ a=x+y) ∨ (L+2=x+3*y ∧ a=x+2*y)) → Good L a)
    {L a : ℕ} (large : 7 ≤ L) (odd : Odd L) (index : a < L) : Good L a := by
  let P (m a c : ℕ) := (synthetic m a c).good (m-2)
  have step (m a c t : ℕ) (size : 9 ≤ m) (_om : Odd m) (av : a+3 ≤ m) (cv : c < m)
      (left : 7 ≤ t) (right : t+12 ≤ m) (ca : a+7 ≤ t ∨ t+12 ≤ a) (cc : c+7 ≤ t ∨ t+12 ≤ c)
      (old : P m a c) : P (m+4) (up t a) (up t c) := by
    have moved := (good_iff_after_gap (synthetic_splice av cv left right ca cc)).mp old
    change (synthetic (m+4) (up t a) (up t c)).good (m+4-2)
    rwa [show m+4-2=m-2+4 by omega]
  have base (m a x y : ℕ) (size : 9 ≤ m) (om : Odd m) (av : a+3 ≤ m)
      (hx : x ≤ 22) (hy : y ≤ 22)
      (cases : (m=3*x+y ∧ a=x) ∨ (m=3*x+2*y ∧ a=2*x+y) ∨
        (m=2*x+3*y ∧ a=x+y) ∨ (m=x+3*y ∧ a=x+2*y)) : P m a ((3*a)%m) := by
    have len : m-2+2=m := by omega
    have oddL : Odd (m-2) := by
      obtain ⟨n,hn⟩ := om
      exact ⟨n-1,by omega⟩
    have cert := finite (m-2) a x y (by omega) oddL (by omega) hx hy (by rwa [len])
    have val := (physical_good_iff oddL).mpr cert
    simpa only [P,len] using val
  have oddM : Odd (L+2) := by obtain ⟨n,h⟩ := odd; exact ⟨n+1,by omega⟩
  have value := chamber_induction P step base (L+2) a (by omega) oddM (by omega)
  apply (physical_good_iff odd).mp
  simpa only [P,Nat.add_sub_cancel] using value

end CriticalConicEvenSparse.Tight

namespace CriticalConic

open Polynomial

/-- The divided pole equations are the values at the physical nodes of
the polynomial whose coefficient slots are the signed weighted moments. -/
theorem rectangular_tile_roots {F : Type*} [Field F] {L K b : ℕ} (even : Even K)
    (t q : Fin b→F) (regular : ∀ i j,t i+t j≠0)
    (f : Fin b→Fin (L+1)→F) (g : Fin b→Fin L→F)
    (factor : ∀ i (x : F),(∑ j,x^j.val*f i j)=(x-t i^K)*(∑ s,x^s.val*g i s))
    (poles : ∀ j,(∑ i,q i*((∑ s,t j^(K*s.val)*f i s)/(t i+t j)))=0) :
    let c (s : Fin L) (l : Fin K) := ∑ i,q i*(-t i)^l.val*g i s
    let P := ∑ s : Fin L,∑ l : Fin K,monomial (K*s.val+(K-1-l.val)) (c s l)
    ∀ j,P.eval (t j)=0 := by
  classical
  intro c P j
  let x := t j
  have row (i : Fin b) :
      (∑ s,x^(K*s.val)*f i s)/(t i+x)=
        (∑ s,x^(K*s.val)*g i s)*(∑ l : Fin K,(-t i)^l.val*x^(K-1-l.val)) := by
    have h := factor i (x^K)
    simp only [← pow_mul] at h
    rw [h,← boundary_geometric_sum even (t i) x (regular i j)]
    ring
  have commute3 (v : Fin L→Fin K→Fin b→F) :
      (∑ s,∑ l,∑ i,v s l i)=(∑ i,∑ s,∑ l,v s l i) := by
    calc
      _ = ∑ s,∑ i,∑ l,v s l i := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  change P.eval x=0
  simp only [P,c,eval_finsetSum,eval_monomial,pow_add,Finset.sum_mul]
  rw [commute3]
  calc
    _ = ∑ i,q i*((∑ s,x^(K*s.val)*g i s)*(∑ l : Fin K,(-t i)^l.val*x^(K-1-l.val))) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ i,q i*((∑ s,x^(K*s.val)*f i s)/(t i+x)) := by simp_rw [row]
    _ = 0 := poles j

end CriticalConic

namespace CriticalConic

open Polynomial

/-- The quotient by K recovers the block index; the remainder recovers
the reversed position within that block. -/
theorem rectangular_index_eq {L K : ℕ} (hK : 0 < K)
    (u : Fin L) (v : Fin K) (s : Fin L) (l : Fin K) :
    K*u.val+(K-1-v.val) = K*s.val+(K-1-l.val) ↔ u=s ∧ v=l := by
  have quotient (x : Fin L) (y : Fin K) :
      (K*x.val+(K-1-y.val))/K=x.val := by
    rw [Nat.mul_add_div hK,Nat.div_eq_of_lt (by omega : K-1-y.val<K),Nat.add_zero]
  constructor
  · intro eq
    have blocks := congrArg (fun n : ℕ => n/K) eq
    simp only [quotient] at blocks
    have first := Fin.ext blocks
    subst u
    have reversed := Nat.add_left_cancel eq
    exact ⟨rfl,Fin.ext (by omega)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem rectangular_monomial_coefficient {L K : ℕ} (hK : 0 < K)
    (c : Fin L → Fin K → ℂ) (s : Fin L) (l : Fin K) :
    (∑ u : Fin L, ∑ v : Fin K, Polynomial.monomial (K*u.val+(K-1-v.val)) (c u v)).coeff
        (K*s.val+(K-1-l.val)) = c s l := by
  classical
  simp only [finsetSum_coeff,coeff_monomial,rectangular_index_eq hK]
  simp [ite_and,Finset.sum_ite_irrel]

/-- Erasing the top corner bounds the encoded polynomial degree by KL−2,
including a one-cell rectangle. -/
theorem rectangular_polynomial_degree {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (c : Fin L → Fin K → ℂ)
    (top : ∀ (s : Fin L) (l : Fin K), s.val+1=L → l.val=0 → c s l=0) :
    (∑ s : Fin L, ∑ l : Fin K, Polynomial.monomial (K*s.val+(K-1-l.val)) (c s l)).natDegree ≤ K*L-2 := by
  classical
  have lastBlock := congrArg (fun i : ℕ => K*i) (Nat.sub_add_cancel (by omega : 1≤L))
  rw [Nat.mul_add,Nat.mul_one] at lastBlock
  apply natDegree_sum_le_of_forall_le
  intro s _
  apply natDegree_sum_le_of_forall_le
  intro l _
  by_cases small : K*s.val+(K-1-l.val) ≤ K*L-2
  · exact (natDegree_monomial_le _).trans small
  have last : s.val+1=L := by
    by_contra h
    have less : s.val<L-1 := by omega
    have strict := Nat.mul_lt_mul_of_pos_left less hK
    omega
  have same : s.val=L-1 := by omega
  have first : l.val=0 := by
    rw [same] at small
    omega
  rw [top s l last first]
  simp

/-- All node values vanish, so the encoded polynomial equals its monic
node factor times a quotient with the stated degree budget. -/
theorem rectangular_polynomial_readout {L K b : ℕ} (hL : 0 < L) (hK : 0 < K)
    (t : Fin b → ℂ) (distinct : Function.Injective t) (c : Fin L → Fin K → ℂ)
    (top : ∀ (s : Fin L) (l : Fin K), s.val+1=L → l.val=0 → c s l=0) :
    let P := ∑ s : Fin L, ∑ l : Fin K, Polynomial.monomial (K*s.val+(K-1-l.val)) (c s l)
    (∀ i, P.eval (t i)=0) → ∃ B : Polynomial ℂ, B.natDegree≤K*L-2-b ∧
      ∀ s l, c s l = ((∏ i, (Polynomial.X-Polynomial.C (t i)))*B).coeff (K*s.val+(K-1-l.val)) := by
  classical
  intro P vanish
  let D : Polynomial ℂ := ∏ i, (X-C (t i))
  have degree : P.natDegree ≤ K*L-2 := rectangular_polynomial_degree hL hK c top
  have divisor : D ∣ P :=
    Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C distinct)
      (fun i => dvd_iff_isRoot.mpr (vanish i))
  obtain ⟨B,eq⟩ := divisor
  refine ⟨B,?_,?_⟩
  · by_cases zero : B=0
    · simp [zero]
    have monic : D.Monic := monic_prod_X_sub_C t _
    have nodes : D.natDegree=b := by simp [D]
    rw [eq,natDegree_mul monic.ne_zero zero,nodes] at degree
    omega
  · intro s l
    have atCoeff := congrArg (fun p : Polynomial ℂ => p.coeff (K*s.val+(K-1-l.val))) eq
    exact (rectangular_monomial_coefficient hK c s l).symm.trans atCoeff

end CriticalConic

namespace CriticalConic

open Polynomial

/-- Rectangular coefficient blocks with even width K. Each right row yields
a polynomial quotient of degree at most KL−2−b. The top moment of each
block comes from the original unweighted column equations. -/
theorem rectangular_boundary_interpolation (L K b u : ℕ) (hL : 0<L) (hK : 0<K) (even : Even K) :
    ∀ t : Fin b→ℂ,Function.Injective t → (∀ i j,t i+t j≠0) →
    let M : Matrix (Fin b) (Fin (L+1)) ℂ := fun j s => t j^(K*s.val)
    let Q : Matrix (Fin u) (Fin b) ℂ := fun k i => t i^((K+1)*k.val)
    let D := ∏ i : Fin b,(X-C (t i))
    ∀ f : Fin b→Fin (L+1)→ℂ,(∀ i,M.mulVec (f i) i=0) →
      (∀ k j,(∑ i,Q k i*f i j)=0) →
      (∀ k j,(∑ i,Q k i*(M.mulVec (f i) j/(t i+t j)))=0) →
      ∃ g : Fin b→Fin L→ℂ,∃ B : Fin u→ℂ[X],(g=0 → f=0) ∧ (∀ k,(B k).natDegree≤K*L-2-b) ∧
        ∀ s : Fin L,∀ k : Fin u,∀ l : Fin (K+1),
          (∑ i,t i^((K+1)*k.val+l.val)*g i s)=(-1:ℂ)^l.val*
            (if l.val<K*(s.val+1) then (D*B k).coeff (K*(s.val+1)-1-l.val) else 0) := by
  classical
  intro t distinct regular M Q D f diag mass poles
  have root (i : Fin b) : (∑ j,(t i^K)^j.val*f i j)=0 := by
    simp only [← pow_mul]
    exact diag i
  choose g kill factor rows using fun i => boundary_row_factor hL (t i^K) (f i) (root i)
  let pad (i : Fin b) (n : ℕ) := if h : n<L then g i ⟨n,h⟩ else 0
  have padAt (i : Fin b) (s : Fin L) : pad i s.val=g i s := by simp [pad,s.isLt]
  have padEnd (i : Fin b) : pad i L=0 := by simp [pad]
  have coeffRow (i : Fin b) (j : Fin (L+1)) :
      f i j=(if j.val=0 then 0 else pad i (j.val-1))-t i^K*pad i j.val := rows i j
  have topRow (s : Fin L) (hs : s.val+1=L) (i : Fin b) : f i (Fin.last L)=g i s := by
    have ce := coeffRow i (Fin.last L)
    simpa only [Fin.val_last,if_neg (by omega : L≠0),show L-1=s.val by omega,
      padAt,padEnd,mul_zero,sub_zero] using ce
  let tile (k : Fin u) (s : Fin L) (l : Fin K) := ∑ i,Q k i*(-t i)^l.val*g i s
  have crest (k : Fin u) (s : Fin L) (l : Fin K) (hs : s.val+1=L) (hl : l.val=0) : tile k s l=0 := by
    have z := mass k (Fin.last L)
    simpa only [tile,hl,pow_zero,mul_one,topRow s hs] using z
  have vanish (k : Fin u) := rectangular_tile_roots even t (Q k) regular f g factor (fun j => poles k j)
  choose B degreeB lookup using fun k : Fin u =>
    rectangular_polynomial_readout hL hK t distinct (tile k) (crest k) (vanish k)
  let moment (k : Fin u) (s : Fin L) (l : ℕ) := ∑ i,t i^((K+1)*k.val+l)*g i s
  have signed (k : Fin u) (s : Fin L) (l : Fin K) :
      moment k s l.val=(-1:ℂ)^l.val*(D*B k).coeff (K*s.val+(K-1-l.val)) := by
    have untwist : (-1:ℂ)^l.val*tile k s l=moment k s l.val := by
      dsimp only [tile,moment]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have sq : (-1:ℂ)^l.val*(-1:ℂ)^l.val=1 := by rw [← mul_pow]; simp
      rw [show -t i=(-1:ℂ)*t i by ring,mul_pow,pow_add]
      change (-1:ℂ)^l.val*((t i^((K+1)*k.val))*((-1)^l.val*t i^l.val)*g i s)=_
      linear_combination (t i^((K+1)*k.val)*t i^l.val*g i s)*sq
    calc
      _ = (-1:ℂ)^l.val*tile k s l := untwist.symm
      _ = _ := by rw [lookup]
  have lag (k : Fin u) (s : Fin L) :
      moment k s K=∑ i,Q k i*(if s.val=0 then 0 else pad i (s.val-1)) := by
    calc
      _ = (∑ i,Q k i*(if s.val=0 then 0 else pad i (s.val-1))) -
          (∑ i,Q k i*f i s.castSucc) := by
        change (∑ i,t i^((K+1)*k.val+K)*g i s)=_
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [coeffRow i s.castSucc,Fin.val_castSucc,padAt,pow_add]
        dsimp only [Q]
        ring
      _ = _ := by rw [mass,sub_zero]
  refine ⟨g,B,fun hz => funext fun i => kill i (congrFun hz i),degreeB,?_⟩
  intro s k l
  change moment k s l.val=_
  by_cases low : l.val<K
  · let ell : Fin K := ⟨l.val,low⟩
    have index : K*s.val+(K-1-l.val)=K*(s.val+1)-1-l.val := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    have guard : l.val<K*(s.val+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    have h := signed k s ell
    change moment k s l.val=(-1:ℂ)^l.val*(D*B k).coeff (K*s.val+(K-1-l.val)) at h
    simpa only [if_pos guard,index] using h
  · have endval : l.val=K := by have := l.isLt; omega
    rw [endval,even.neg_one_pow,one_mul,lag]
    by_cases zero : s.val=0
    · simp [zero]
    · let prev : Fin L := ⟨s.val-1,by have := s.isLt; omega⟩
      have pprev : prev.val+1=s.val := by dsimp [prev]; omega
      have index : K*prev.val+(K-1)=K*(s.val+1)-1-K := by
        have hmul := congrArg (K*·) pprev
        change K*(prev.val+1)=K*s.val at hmul
        rw [Nat.mul_add,Nat.mul_one] at hmul ⊢
        omega
      have guard : K<K*(s.val+1) := by
        simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (show 1<s.val+1 by omega) hK
      rw [if_pos guard]
      simp only [if_neg zero]
      change (∑ i,Q k i*pad i prev.val)=_
      simp_rw [padAt]
      let z : Fin K := ⟨0,by omega⟩
      have row0 := signed k prev z
      simpa only [moment,Q,z,pow_zero,one_mul,Nat.add_zero,Nat.sub_zero,index] using row0

/-- At even hub count, the adjacent even block width K=L+1 leaves a
quotient polynomial of degree at most L for each of the L−1 right rows. -/
theorem even_boundary_interpolation (L : ℕ) (hL : 5≤L) (odd : Odd L) :
    let K := L+1
    let b := L^2-2
    let u := L-1
    ∀ t : Fin b→ℂ,Function.Injective t → (∀ i j,t i+t j≠0) →
    let M : Matrix (Fin b) (Fin (L+1)) ℂ := fun j s => t j^(K*s.val)
    let Q : Matrix (Fin u) (Fin b) ℂ := fun k i => t i^((K+1)*k.val)
    let D := ∏ i : Fin b,(X-C (t i))
    ∀ f : Fin b→Fin (L+1)→ℂ,(∀ i,M.mulVec (f i) i=0) →
      (∀ k j,(∑ i,Q k i*f i j)=0) →
      (∀ k j,(∑ i,Q k i*(M.mulVec (f i) j/(t i+t j)))=0) →
      ∃ g : Fin b→Fin L→ℂ,∃ B : Fin u→ℂ[X],(g=0 → f=0) ∧ (∀ k,(B k).natDegree≤L) ∧
        ∀ s : Fin L,∀ k : Fin u,∀ l : Fin (K+1),
          (∑ i,t i^((K+1)*k.val+l.val)*g i s)=(-1:ℂ)^l.val*
            (if l.val<K*(s.val+1) then (D*B k).coeff (K*(s.val+1)-1-l.val) else 0) := by
  intro K b u t distinct regular M Q D f diag mass poles
  have even : Even K := by
    obtain ⟨j,hj⟩ := odd
    exact ⟨j+1,by dsimp [K]; omega⟩
  have deg : K*L-2-b=L := by
    have square : 2≤L^2 := by nlinarith
    have prod : K*L=L^2+L := by dsimp [K];ring
    dsimp [b]
    omega
  obtain ⟨g,B,zero,bound,rows⟩ := rectangular_boundary_interpolation L K b u (by omega)
    (by dsimp [K]; omega) even t distinct regular f diag mass poles
  exact ⟨g,B,zero,fun k => deg ▸ bound k,rows⟩

end CriticalConic

namespace CriticalConicEvenBoundary

/-- Read a polynomial coefficient by an integer index, extended by zero
on both sides of the closed degree interval. -/
def guardedCoeff {R : Type*} [Zero R] (b : ℕ) (d : ℕ → R) (n : ℤ) : R :=
  if 0 ≤ n ∧ n ≤ (b : ℤ) then d n.toNat else 0

/-- The rectangular shifted coefficient matrix. The row pair is `(s,j)`
and the column pair is `(k,v)`. -/
noncomputable abbrev coefficientMatrix {R : Type*} [CommRing R] (L K u b : ℕ) (d : ℕ → R) :
    Matrix (Fin L × Fin L) (Fin u × Fin (L+1)) R :=
  Matrix.of (fun sj kv => ∑ l : Fin (K+1), (-1 : R)^l.val *
    guardedCoeff b d ((((K+1)*kv.1.val+l.val : ℕ) : ℤ)-(sj.2.val : ℤ)) *
    guardedCoeff b d (((K*(sj.1.val+1) : ℕ) : ℤ)-1-(l.val : ℤ)-(kv.2.val : ℤ)))

/-- At the even-hub boundary, the excess over the physical-node count is
exactly the number of independent nodal shifts. -/
theorem boundary_size {L : ℕ} (hL : 2≤L) : (L-1)*((L+1)+1)=(L^2-2)+L := by
  have step : (L-1+1)*(L+2)=L^2+2*L := by rw [Nat.sub_add_cancel (by omega : 1≤L)]; ring
  rw [Nat.add_mul,Nat.one_mul] at step
  have sq : 2≤L^2 := by nlinarith only [Nat.mul_self_le_mul_self hL]
  rw [show L+1+1=L+2 by omega]
  omega

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open Polynomial

private lemma guard_sub {b : ℕ} (D : ℂ[X]) (deg : D.natDegree≤b) (n j : ℕ) :
    guardedCoeff b D.coeff ((n : ℤ)-(j : ℤ)) = if j≤n then D.coeff (n-j) else 0 := by
  by_cases lower : j≤n
  · have ge : 0 ≤ (n : ℤ)-(j : ℤ) := by omega
    have number : ((n : ℤ)-(j : ℤ)).toNat=n-j := by omega
    simp only [guardedCoeff,ge,true_and,number,if_pos lower]
    split
    · rfl
    · exact (coeff_eq_zero_of_natDegree_lt (by omega : D.natDegree<n-j)).symm
  · simp [guardedCoeff,lower]

private lemma block_sum {u K : ℕ} (v : ℕ → ℂ) :
    (∑ k : Fin u, ∑ l : Fin (K+1), v ((K+1)*k.val+l.val)) =
      ∑ a ∈ Finset.range (u*(K+1)), v a := by
  have reindex := (finProdFinEquiv : Fin u × Fin (K+1) ≃ Fin (u*(K+1))).sum_comp (fun i => v i.val)
  rw [Fintype.sum_prod_type] at reindex
  rw [← Fin.sum_univ_eq_sum_range]
  change (∑ k : Fin u,∑ l : Fin (K+1), v (l.val+(K+1)*k.val)) = _ at reindex
  simpa only [Nat.add_comm] using reindex

/-- For each shift `j<L`, the coefficients of `X^j D` give one recurrence
on the entire rectangular list of physical moments. -/
theorem shifted_nodal_relation {L K u b : ℕ} (size : u*(K+1)=b+L) (t : Fin b → ℂ)
    (D : ℂ[X]) (deg : D.natDegree≤b) (roots : ∀ i, D.eval (t i)=0) (g : Fin b → ℂ) (j : Fin L) :
    (∑ k : Fin u, ∑ l : Fin (K+1),
      guardedCoeff b D.coeff ((((K+1)*k.val+l.val : ℕ) : ℤ)-(j.val : ℤ)) *
      (∑ i,t i^((K+1)*k.val+l.val)*g i))=0 := by
  let P := X^j.val*D
  have coeff (n : ℕ) : guardedCoeff b D.coeff ((n : ℤ)-(j.val : ℤ))=P.coeff n := by
    rw [guard_sub D deg,show P=X^j.val*D from rfl,coeff_X_pow_mul']
  have short : P.natDegree < u*(K+1) := by
    have upper : P.natDegree≤j.val+b := natDegree_mul_le_of_le (natDegree_X_pow_le _) deg
    have := j.isLt
    omega
  simp_rw [coeff]
  rw [block_sum (u:=u) (K:=K) (fun n => P.coeff n*(∑ i,t i^n*g i))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul,← P.eval_eq_sum_range' short (t i)]
  simp only [P,eval_mul,eval_pow,eval_X,roots,mul_zero,zero_mul]

/-- Coefficient convolution for a degree-bounded quotient, including the
out-of-range coefficients at either end. -/
theorem product_readout {b L : ℕ} (D B : ℂ[X]) (dD : D.natDegree≤b) (dB : B.natDegree≤L)
    (n l : ℕ) : (if l<n then (D*B).coeff (n-1-l) else 0) =
    ∑ v : Fin (L+1), B.coeff v.val * guardedCoeff b D.coeff ((n : ℤ)-1-(l : ℤ)-(v.val : ℤ)) := by
  by_cases inside : l<n
  · rw [if_pos inside]
    have expansion : B = ∑ v : Fin (L+1), C (B.coeff v.val)*X^v.val := by
      rw [Fin.sum_univ_eq_sum_range (fun v : ℕ => C (B.coeff v)*X^v)]
      exact B.as_sum_range_C_mul_X_pow' (by omega)
    have multiply : D*B = ∑ v : Fin (L+1), C (B.coeff v.val)*(X^v.val*D) := by
      conv_lhs => rw [expansion]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [multiply,finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro v _
    have offset : (n : ℤ)-1-(l : ℤ)-(v.val : ℤ) = ((n-1-l : ℕ) : ℤ)-(v.val : ℤ) := by omega
    rw [coeff_C_mul,coeff_X_pow_mul',offset,guard_sub D dD]
  · rw [if_neg inside]
    symm
    apply Finset.sum_eq_zero
    intro v _
    have neg : ¬ 0 ≤ (n : ℤ)-1-(l : ℤ)-(v.val : ℤ) := by omega
    simp only [guardedCoeff,neg,false_and,if_false,mul_zero]

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open Polynomial

/-- Injectivity of the rectangular coefficient matrix eliminates every
quotient polynomial and every physical column of the signed moment system. -/
theorem zero_of_nodal_moments {L K u b : ℕ} (size : u*(K+1)=b+L)
    (t : Fin b → ℂ) (distinct : Function.Injective t) (D : ℂ[X]) (deg : D.natDegree≤b)
    (roots : ∀ i, D.eval (t i)=0) (g : Fin b → Fin L → ℂ) (B : Fin u → ℂ[X])
    (bound : ∀ k, (B k).natDegree≤L)
    (moments : ∀ (s : Fin L) (k : Fin u) (l : Fin (K+1)),
      (∑ i, t i^((K+1)*k.val+l.val)*g i s) = (-1 : ℂ)^l.val *
        (if l.val < K*(s.val+1) then (D*B k).coeff (K*(s.val+1)-1-l.val) else 0))
    (injective : Function.Injective (coefficientMatrix L K u b D.coeff).mulVec) : B=0 ∧ g=0 := by
  let M := coefficientMatrix L K u b D.coeff
  let v (p : Fin u × Fin (L+1)) := (B p.1).coeff p.2.val
  have killed : M.mulVec v=0 := by
    funext sj
    obtain ⟨s,j⟩ := sj
    change (∑ p, M (s,j) p*v p)=0
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ k : Fin u, ∑ l : Fin (K+1),
          guardedCoeff b D.coeff ((((K+1)*k.val+l.val : ℕ) : ℤ)-(j.val : ℤ)) *
          (∑ i,t i^((K+1)*k.val+l.val)*g i s) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [M,coefficientMatrix,Matrix.of_apply,v,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [moments,product_readout D (B k) deg (bound k)]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
      _ = 0 := shifted_nodal_relation size t D deg roots (fun i => g i s) j
  have all_coeff : v=0 := injective (killed.trans (Matrix.mulVec_zero M).symm)
  have polynomials : B=0 := by
    funext k
    apply Polynomial.ext
    intro n
    by_cases small : n≤L
    · exact congrFun all_coeff (k,⟨n,by omega⟩)
    · change (B k).coeff n=(0 : ℂ[X]).coeff n
      rw [coeff_eq_zero_of_natDegree_lt (by have := bound k; omega : (B k).natDegree<n),coeff_zero]
  refine ⟨polynomials,?_⟩
  have column (s : Fin L) : (fun i => g i s)=0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero distinct
    intro j
    let k : Fin u := ⟨j.val/(K+1),(Nat.div_lt_iff_lt_mul (by omega : 0<K+1)).mpr (by have := j.isLt; omega)⟩
    let l : Fin (K+1) := ⟨j.val%(K+1),Nat.mod_lt _ (by omega)⟩
    have ordinal : (K+1)*k.val+l.val=j.val := Nat.div_add_mod _ _
    have zero := moments s k l
    rw [ordinal,polynomials] at zero
    simpa only [Pi.zero_apply,mul_zero,coeff_zero,ite_self,mul_comm (g _ _)] using zero
  funext i s
  exact congrFun (column s) i

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open Polynomial

/-- At the even-hub boundary, full column rank of the explicit shifted
coefficient matrix alone closes the conic normal system. -/
theorem kernel_of_boundary_matrix (L : ℕ) (hL : 5≤L) (odd : Odd L) :
    let K := L+1
    let b := L^2-2
    let u := L-1
    ∀ t : Fin b → ℂ, Function.Injective t → (∀ i j,t i+t j≠0) →
    let M : Matrix (Fin b) (Fin (L+1)) ℂ := fun j s => t j^(K*s.val)
    let Q : Matrix (Fin u) (Fin b) ℂ := fun k i => t i^((K+1)*k.val)
    let D := ∏ i : Fin b, (X-C (t i))
    Function.Injective (coefficientMatrix L K u b D.coeff).mulVec →
    ∀ f : Fin b → Fin (L+1) → ℂ, (∀ i,M.mulVec (f i) i=0) →
      (∀ k j,(∑ i,Q k i*f i j)=0) →
      (∀ k j,(∑ i,Q k i*(M.mulVec (f i) j/(t i+t j)))=0) → f=0 := by
  intro K b u t distinct regular M Q D injective f diagonal mass poles
  obtain ⟨g,B,finish,bound,moments⟩ := CriticalConic.even_boundary_interpolation L hL odd t distinct regular f diagonal mass poles
  have degree : D.natDegree≤b := by simp [D]
  have roots (i : Fin b) : D.eval (t i)=0 := by
    rw [show D=_ from rfl,eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  exact finish (zero_of_nodal_moments (boundary_size (by omega : 2≤L)) t distinct D degree roots g B bound moments injective).2

end CriticalConicEvenBoundary

namespace CriticalConicBoundary

open MvPolynomial

private lemma quadratic_det {I σ : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial σ ℂ)) (quadratic : ∀ i j,(M i j).IsHomogeneous 2) :
    M.det.IsHomogeneous (Fintype.card I*2) := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro τ _
  have prod := IsHomogeneous.prod (Finset.univ : Finset I) (fun i => M (τ i) i)
    (fun _ => 2) (fun i _ => quadratic _ _)
  have card : (∑ _ : I,2)=Fintype.card I*2 := by simp
  rw [card] at prod
  simpa only [map_intCast] using prod.C_mul (((Equiv.Perm.sign τ : ℤ) : ℂ))

/-- A full-column-rank quadratic matrix of independent coefficients
retains full rank for a nodal polynomial with distinct, regular sample points. -/
theorem specialize_quadratic_matrix {I J : Type*} [Fintype I] [Fintype J] {b K : ℕ}
    (positive : 0<K) (M : Matrix I J (MvPolynomial (Fin (b+1)) ℂ))
    (quadratic : ∀ i j,(M i j).IsHomogeneous 2)
    (v : Fin (b+1)→ℂ) (inject : Function.Injective (M.map (eval v)).mulVec) :
    ∃ t : Fin b→ℂ, Function.Injective (fun i => t i^K) ∧ (∀ i j,t i+t j≠0) ∧
      Function.Injective (M.map (eval (fun i : Fin (b+1) =>
        (∏ j : Fin b,(Polynomial.X-Polynomial.C (t j))).coeff i.val))).mulVec := by
  classical
  let A := M.map (eval v)
  obtain ⟨left,identity⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr inject)
  let B := LinearMap.toMatrix' left
  have leftInv : B*A=1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' left)).comp A.mulVecLin=LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact identity
  let P := B.map (MvPolynomial.C : ℂ→+*MvPolynomial (Fin (b+1)) ℂ)
  have spec (u : Fin (b+1)→ℂ) : eval u (P*M).det=(B*M.map (eval u)).det := by
    have atPoint : P.map (eval u)=B := by ext; simp [P,Matrix.map_apply]
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,atPoint]
  have valid : eval v (P*M).det=1 := (spec v).trans ((congrArg Matrix.det leftInv).trans Matrix.det_one)
  have homogeneous := quadratic_det (P*M) (fun i j => by
    rw [Matrix.mul_apply]
    apply IsHomogeneous.sum
    intro k _
    exact (quadratic k j).C_mul (B i k))
  obtain ⟨t,_,poles,powers,good⟩ := CriticalHigher.ConicBoundary.good_roots_of_homogeneous
    positive (P*M).det homogeneous (fun h => zero_ne_one (by simpa only [h,map_zero] using valid))
  refine ⟨t,powers,poles,?_⟩
  rw [spec] at good
  have detected := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr good))
  intro x y same
  apply detected
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,same]

end CriticalConicBoundary

namespace CriticalConicEvenBoundary

open MvPolynomial

/-- Integer subscripts remain bounded when the coefficient variables are
evaluated, including at both ends of the truncated convolution. -/
theorem regular_nodes_of_matrix {L K u b : ℕ} (positive : 0<K) (d : ℕ→ℂ)
    (test : Function.Injective (coefficientMatrix L K u b d).mulVec) :
    ∃ t : Fin b→ℂ,Function.Injective (fun i => t i^K) ∧ (∀ i j,t i+t j≠0) ∧
      Function.Injective (coefficientMatrix L K u b (∏ j,(Polynomial.X-Polynomial.C (t j))).coeff).mulVec := by
  classical
  let x (j : ℕ) : MvPolynomial (Fin (b+1)) ℂ := if h : j<b+1 then X ⟨j,h⟩ else 0
  let A := coefficientMatrix L K u b x
  have linear (n : ℤ) : (guardedCoeff b x n).IsHomogeneous 1 := by
    dsimp only [guardedCoeff,x]
    split
    · split
      · exact isHomogeneous_X _ _
      · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _
  have quadratic (sj : Fin L × Fin L) (kv : Fin u × Fin (L+1)) : (A sj kv).IsHomogeneous 2 := by
    dsimp only [A,coefficientMatrix,Matrix.of_apply]
    apply IsHomogeneous.sum
    intro l _
    change ((-1 : MvPolynomial (Fin (b+1)) ℂ)^l.val * _ * _).IsHomogeneous (1+1)
    have c : (-1 : MvPolynomial (Fin (b+1)) ℂ)^l.val=C ((-1:ℂ)^l.val) := by simp
    rw [c]
    exact ((linear _).C_mul _).mul (linear _)
  have eval_guard (v : ℕ→ℂ) (n : ℤ) :
      eval (fun i : Fin (b+1) => v i.val) (guardedCoeff b x n) = guardedCoeff b v n := by
    dsimp only [guardedCoeff]
    split
    · rename_i nrange
      have bound : n.toNat<b+1 := by omega
      simp only [x,dif_pos bound,eval_X]
    · exact map_zero _
  have expr (v : ℕ→ℂ) : A.map (eval (fun i : Fin (b+1) => v i.val))=coefficientMatrix L K u b v := by
    ext sj kv
    simp only [A,coefficientMatrix,Matrix.map_apply,Matrix.of_apply,map_sum,map_mul,
      map_pow,map_neg,map_one,eval_guard]
  have start : Function.Injective (A.map (eval (fun i : Fin (b+1) => d i.val))).mulVec := by
    rw [expr]
    exact test
  obtain ⟨t,powers,poles,atNodes⟩ := CriticalConicBoundary.specialize_quadratic_matrix positive
    A quadratic _ start
  refine ⟨t,powers,poles,?_⟩
  rwa [expr] at atNodes

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open Arxiv.«0805.3777» Polynomial

/-- On every even hub level at the sharp boundary, full column rank
of the rectangular moment matrix at any coefficient vector suffices.
There are L² rows and L²−1 columns. -/
theorem rank_of_even_boundary_matrix {L : ℕ} (five : 5≤L) (odd : Odd L)
    (d : ℕ→ℂ) (test : Function.Injective (coefficientMatrix L (L+1) (L-1) (L^2-2) d).mulVec) :
    let b := L^2-2
    let r := 2*b-(L+1)
    IsGenericRank [3,b,r-(2*(L+1)-5)] r := by
  intro b r
  have tile : (L+1)*(L+1-2)-1=b := by
    have inc := congrArg (fun n : ℕ => (L+1)*n) (show (L+1-2)+1=L by omega)
    have e : (L+1)*(L+1-2)+1=L^2 := by nlinarith only [inc]
    dsimp only [b]
    omega
  have room : L+1≤b := by
    have sq : 5*L≤L^2 := by nlinarith only [Nat.mul_le_mul_left L five]
    dsimp only [b]
    omega
  have finish := CriticalConic.boundary_rank_of_local (L+1) (by omega)
  dsimp only at finish
  rw [tile,show L+1-2=L-1 by omega] at finish
  apply finish
  obtain ⟨t,powers,poles,valid⟩ := regular_nodes_of_matrix (by omega : 0<L+1) d test
  have distinct : Function.Injective t := by
    intro i j same
    exact powers (congrArg (fun z : ℂ => z^(L+1)) same)
  let M : Matrix (Fin b) (Fin (L+1)) ℂ := fun i j => t i^((L+1)*j.val)
  let Q : Matrix (Fin (L-1)) (Fin b) ℂ := fun j i => t i^((L+1+1)*j.val)
  apply CriticalConic.local_component t distinct poles M (CriticalConicBoundary.powers_frame room t powers) Q
  exact kernel_of_boundary_matrix L five odd t distinct poles valid

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

def rowGrade {L : ℕ} (sj : Fin L × Fin L) : ZMod L := (sj.1.val : ZMod L) - sj.2.val

def columnGrade {L u : ℕ} (o : ZMod L) (kv : Fin u × Fin (L+1)) : ZMod L :=
  (kv.2.val : ZMod L)-2*(kv.1.val : ZMod L)+2*o

/-- The row in the same residue class as the candidate column, at row position s. -/
def sparseRow {L u : ℕ} [NeZero L] (o : ZMod L) (kv : Fin u × Fin (L+1)) (s : Fin L) : Fin L × Fin L :=
  (s,⟨((s.val : ZMod L)-columnGrade o kv).val,ZMod.val_lt _⟩)

theorem sparseRow_grade {L u : ℕ} [NeZero L] (o : ZMod L) (kv : Fin u × Fin (L+1)) (s : Fin L) :
    rowGrade (sparseRow o kv s)=columnGrade o kv := by
  change (s.val : ZMod L) - ((((s.val : ZMod L)-columnGrade o kv).val : ℕ) : ZMod L)=columnGrade o kv
  rw [ZMod.natCast_zmod_val]
  abel

/-- A nonzero guarded integer-index coefficient retains its residue after
conversion to a natural number. Both guards are used before the conversion. -/
theorem nonzero_guarded_grade {R : Type*} [Zero R] {L b : ℕ} (o : ZMod L)
    (d : ℕ → R) (sparse : ∀ v : ℕ, (v : ZMod L) ≠ o → d v=0) (n : ℤ)
    (nonzero : guardedCoeff b d n≠0) : (n : ZMod L)=o := by
  by_cases inside : 0≤n ∧ n≤(b : ℤ)
  · have nz : d n.toNat≠0 := by simpa [guardedCoeff,inside] using nonzero
    have eq : (n.toNat : ZMod L)=o := by by_contra h; exact nz (sparse _ h)
    have cast : ((n.toNat : ℤ) : ZMod L)=(n : ZMod L) :=
      congrArg (fun z : ℤ => (z : ZMod L)) (Int.toNat_of_nonneg inside.1)
    simp only [Int.cast_natCast] at cast
    exact cast.symm.trans eq
  · simp [guardedCoeff,inside] at nonzero

/-- At K=L+1 the two surviving coefficient indices add to the row grade
minus the shifted column grade plus twice the coefficient residue. -/
theorem coefficientMatrix_off_grade {R : Type*} [CommRing R] {L u b : ℕ}
    (o : ZMod L) (d : ℕ → R) (sparse : ∀ v : ℕ, (v : ZMod L) ≠ o → d v=0)
    (sj : Fin L × Fin L) (kv : Fin u × Fin (L+1)) (different : rowGrade sj≠columnGrade o kv) :
    coefficientMatrix L (L+1) u b d sj kv=0 := by
  classical
  unfold coefficientMatrix
  change (∑ l : Fin ((L+1)+1), _) = 0
  apply Finset.sum_eq_zero
  intro l _
  let p : ℤ := ((((L+1)+1)*kv.1.val+l.val : ℕ) : ℤ) - (sj.2.val : ℤ)
  let q : ℤ := (((L+1)*(sj.1.val+1) : ℕ) : ℤ)-1-(l.val : ℤ)-(kv.2.val : ℤ)
  change (-1 : R)^l.val*guardedCoeff b d p*guardedCoeff b d q=0
  by_cases fp : guardedCoeff b d p=0
  · rw [fp,mul_zero,zero_mul]
  by_cases fq : guardedCoeff b d q=0
  · rw [fq,mul_zero]
  exfalso
  apply different
  have hp := nonzero_guarded_grade o d sparse p fp
  have hq := nonzero_guarded_grade o d sparse q fq
  dsimp only [p,q] at hp hq
  push_cast at hp hq
  simp only [ZMod.natCast_self,zero_add] at hp hq
  unfold rowGrade columnGrade
  linear_combination hp+hq

/-- Independent blocks of a rectangular matrix combine to full column
rank. Row- and column-fiber cardinalities need not coincide. -/
theorem injective_of_fiber_blocks {R I J G : Type*} [CommSemiring R] [Fintype J] [DecidableEq G]
    (M : Matrix I J R) (row : I → G) (col : J → G)
    (off : ∀ i j, row i≠col j → M i j=0)
    (blocks : ∀ a, Function.Injective
      (M.submatrix (fun i : {i // row i=a} => i.val) (fun j : {j // col j=a} => j.val)).mulVec) :
    Function.Injective M.mulVec := by
  classical
  have restriction (g : G) (i : {i // row i=g}) (f : J→R) :
      (∑ j : {j // col j=g}, M i.val j.val*f j.val)=M.mulVec f i.val := by
    have disjoint : (∑ j : {j // ¬col j=g}, M i.val j.val*f j.val)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [off i.val j.val (fun e => j.property (e.symm.trans i.property)),zero_mul]
    have all := Fintype.sum_subtype_add_sum_subtype (fun j => col j=g) (fun j => M i.val j*f j)
    rw [disjoint,add_zero] at all
    exact all
  intro f g same
  funext j
  have each (a : G) : (fun j : {j // col j=a} => f j.val) = (fun j : {j // col j=a} => g j.val) := by
    apply blocks a
    funext i
    change (∑ x : {x // col x=a}, M i.val x.val*f x.val) = ∑ x : {x // col x=a}, M i.val x.val*g x.val
    rw [restriction a i f,restriction a i g,same]
  exact congrFun (each (col j)) ⟨j,rfl⟩

/-- The residues split the original guarded coefficient matrix into L blocks. -/
theorem coefficientMatrix_injective_of_stride {R : Type*} [CommRing R] {L u b : ℕ}
    (o : ZMod L) (d : ℕ → R) (sparse : ∀ v : ℕ, (v : ZMod L) ≠ o → d v=0)
    (blocks : ∀ a, Function.Injective
      ((coefficientMatrix L (L+1) u b d).submatrix
        (fun i : {i : Fin L × Fin L // rowGrade i=a} => i.val)
        (fun j : {j : Fin u × Fin (L+1) // columnGrade o j=a} => j.val)).mulVec) :
    Function.Injective (coefficientMatrix L (L+1) u b d).mulVec :=
  injective_of_fiber_blocks _ rowGrade (columnGrade o) (coefficientMatrix_off_grade o d sparse) blocks

/-- Each row block has the natural order s↦(s,s−a). -/
noncomputable def strideRows {L : ℕ} [NeZero L] (a : ZMod L) :
    Fin L ≃ {v : Fin L × Fin L // rowGrade v=a} where
  toFun i := ⟨(i,⟨((i.val : ZMod L)-a).val,ZMod.val_lt _⟩),by
    change (i.val : ZMod L) - ((((i.val : ZMod L)-a).val : ℕ) : ZMod L)=a
    rw [ZMod.natCast_zmod_val]
    abel⟩
  invFun v := v.val.1
  left_inv _ := rfl
  right_inv v := by
    obtain ⟨⟨i,j⟩,eq⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ((i.val : ZMod L)-a).val=j.val
      change (i.val : ZMod L)-j.val=a at eq
      have shift : (i.val : ZMod L)-a=j.val := by rw [←eq]; abel
      rw [shift,ZMod.val_natCast_of_lt j.isLt]

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

theorem guardedCoeff_int_cast (b : ℕ) (d : ℕ → ℤ) (n : ℤ) :
    ((guardedCoeff b d n : ℤ) : ℂ) = guardedCoeff b (fun j => (d j : ℂ)) n := by
  by_cases p : 0 ≤ n ∧ n ≤ (b : ℤ) <;> simp [guardedCoeff,p]

theorem coefficientMatrix_int_cast (L K u b : ℕ) (d : ℕ → ℤ)
    (i : Fin L × Fin L) (j : Fin u × Fin (L+1)) :
    ((coefficientMatrix L K u b d i j : ℤ) : ℂ) =
      coefficientMatrix L K u b (fun z => (d z : ℂ)) i j := by
  simp only [coefficientMatrix, Matrix.of_apply, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, guardedCoeff_int_cast]

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open MvPolynomial

theorem guardedCoeff_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (b : ℕ) (d : ℕ → R) (z : ℤ) :
    φ (guardedCoeff b d z) = guardedCoeff b (fun i => φ (d i)) z := by
  by_cases hz : 0 ≤ z ∧ z ≤ (b : ℤ) <;> simp [guardedCoeff,hz]

theorem coefficientMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (L K u b : ℕ) (d : ℕ → R) :
    (coefficientMatrix L K u b d).map φ = coefficientMatrix L K u b (fun i => φ (d i)) := by
  ext x y
  simp only [Matrix.map_apply,coefficientMatrix,Matrix.of_apply,map_sum,map_mul,
    map_pow,map_neg,map_one,guardedCoeff_map]

theorem coefficientMatrix_congr_bounded {R : Type*} [CommRing R] (L K u b : ℕ)
    {d e : ℕ → R} (agree : ∀ i, i ≤ b → d i=e i) :
    coefficientMatrix L K u b d = coefficientMatrix L K u b e := by
  have guarded (z : ℤ) : guardedCoeff b d z=guardedCoeff b e z := by
    by_cases inside : 0 ≤ z ∧ z ≤ (b : ℤ)
    · simp only [guardedCoeff,if_pos inside]
      exact agree _ (by omega)
    · simp only [guardedCoeff,if_neg inside]
  ext x y
  simp only [coefficientMatrix,Matrix.of_apply,guarded]

/-- A single polynomial cuts out a nonempty open set of specializations at
which a given rectangular matrix remains injective. The left inverse at the
witness determines the determinant to test. -/
theorem nonzero_full_rank_test {σ I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J (MvPolynomial σ ℂ)) (u : σ→ℂ)
    (start : Function.Injective (M.map (eval u)).mulVec) :
    ∃ P : MvPolynomial σ ℂ, P ≠ 0 ∧ ∀ v : σ→ℂ, eval v P ≠ 0 →
      Function.Injective (M.map (eval v)).mulVec := by
  classical
  let A := M.map (eval u)
  obtain ⟨left,identity⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr start)
  let B := LinearMap.toMatrix' left
  have one : B*A=1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' left)).comp A.mulVecLin=LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact identity
  let T := B.map (MvPolynomial.C : ℂ→+*MvPolynomial σ ℂ)
  have atPoint (v : σ→ℂ) : eval v (T*M).det = (B*M.map (eval v)).det := by
    have constant : T.map (eval v)=B := by ext; simp [T,Matrix.map_apply]
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,constant]
  have atStart : eval u (T*M).det=1 := (atPoint u).trans ((congrArg Matrix.det one).trans Matrix.det_one)
  refine ⟨(T*M).det,fun none => zero_ne_one (by simpa only [none,map_zero] using atStart),?_⟩
  intro v good
  rw [atPoint] at good
  have inj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr good))
  intro x y eq
  apply inj
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,eq]

def boundedSparse {R : Type*} [Zero R] {L b : ℕ} (o : ZMod L)
    (v : Fin (b+1)→R) (j : ℕ) : R :=
  if h : j < b+1 then if (j : ZMod L)=o then v ⟨j,h⟩ else 0 else 0

theorem boundedSparse_off {R : Type*} [Zero R] {L b : ℕ} (o : ZMod L)
    (v : Fin (b+1)→R) (j : ℕ) (out : (j : ZMod L) ≠ o) : boundedSparse o v j = 0 := by
  simp [boundedSparse,out]

noncomputable abbrev residueBlock {R : Type*} [CommRing R] {L u b : ℕ}
    (o a : ZMod L) (d : ℕ→R) :=
  (coefficientMatrix L (L+1) u b d).submatrix
    (fun i : {i : Fin L × Fin L // rowGrade i=a} => i.val)
    (fun j : {j : Fin u × Fin (L+1) // columnGrade o j=a} => j.val)

/-- Different residue blocks may have different coefficient witnesses. A
finite product of their nonzero determinant tests gives one common vector. -/
theorem common_sparse_coefficients {L u b : ℕ} [NeZero L] (o : ZMod L)
    (witness : ∀ a : ZMod L, ∃ d : ℕ→ℂ,
      (∀ i : ℕ, (i : ZMod L) ≠ o → d i=0) ∧
        Function.Injective (residueBlock (u := u) (b := b) o a d).mulVec) :
    ∃ d : ℕ→ℂ, (∀ i : ℕ, (i : ZMod L) ≠ o → d i=0) ∧
      Function.Injective (coefficientMatrix L (L+1) u b d).mulVec := by
  classical
  let z : ℕ → MvPolynomial (Fin (b+1)) ℂ := boundedSparse o (fun i => X i)
  have specialize (v : Fin (b+1)→ℂ) (a : ZMod L) :
      (residueBlock (u := u) (b := b) o a z).map (eval v) =
        residueBlock (u := u) (b := b) o a (boundedSparse o v) := by
    have ev (j : ℕ) : eval v (z j)=boundedSparse o v j := by
      by_cases size : j < b+1 <;> by_cases grade : (j : ZMod L)=o <;>
        simp [z,boundedSparse,size,grade]
    ext i j
    change eval v (coefficientMatrix L (L+1) u b z i.val j.val) =
      coefficientMatrix L (L+1) u b (boundedSparse o v) i.val j.val
    have mat := congrFun (congrFun (coefficientMatrix_map (eval v) L (L+1) u b z) i.val) j.val
    simpa only [Matrix.map_apply,ev] using mat
  have each (a : ZMod L) : ∃ P : MvPolynomial (Fin (b+1)) ℂ, P ≠ 0 ∧
      ∀ v : Fin (b+1)→ℂ, eval v P ≠ 0 →
        Function.Injective (residueBlock (u := u) (b := b) o a (boundedSparse o v)).mulVec := by
    obtain ⟨d,off,inj⟩ := witness a
    let w (j : Fin (b+1)) := d j.val
    have agree (j : ℕ) (bound : j ≤ b) : boundedSparse o w j=d j := by
      have small : j < b+1 := by omega
      by_cases grade : (j : ZMod L)=o
      · simp [boundedSparse,w,small,grade]
      · simp [boundedSparse,small,grade,off j grade]
    have eq := coefficientMatrix_congr_bounded L (L+1) u b agree
    have start : Function.Injective ((residueBlock (u := u) (b := b) o a z).map (eval w)).mulVec := by
      rw [specialize]
      unfold residueBlock
      rw [eq]
      exact inj
    obtain ⟨P,nonzero,good⟩ := nonzero_full_rank_test _ _ start
    exact ⟨P,nonzero,fun v h => by rw [← specialize]; exact good v h⟩
  choose P nonzero good using each
  have whole : ∏ a, P a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a _ => nonzero a)
  obtain ⟨v,hv⟩ : ∃ v : Fin (b+1)→ℂ, eval v (∏ a, P a) ≠ 0 := by
    by_contra! vanish
    exact whole (MvPolynomial.funext (fun x => by rw [vanish x,map_zero]))
  rw [map_prod] at hv
  refine ⟨boundedSparse o v,boundedSparse_off o v,coefficientMatrix_injective_of_stride o _ (boundedSparse_off o v) ?_⟩
  exact fun a => good a v (Finset.prod_ne_zero_iff.mp hv a (Finset.mem_univ a))

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

/-- The private stride specialization of the coefficient vector for block a. -/
def localCoeff (L a n : ℕ) : ℤ :=
  if n % L = 0 then CriticalConicEvenSparse.weight ((L : ℤ)+2) a ((n/L : ℕ) : ℤ) else 0

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

/-- A matrix may be presented with missing columns padded by zeros and with
nonzero row and column scalings. Detection of the padded kernel implies
injectivity on the actual columns. -/
theorem injective_of_padded_kernel {I J V K : Type*} [Field K] [Fintype J] [Fintype V]
    (A : Matrix I J K) (B : Matrix I V K) (index : J → V) (unique : Function.Injective index)
    (allowed : V → Prop) (inside : ∀ j, allowed (index j))
    (ρ : I → K) (σ : J → K) (hr : ∀ i, ρ i ≠ 0) (hc : ∀ j, σ j ≠ 0)
    (entry : ∀ i j, A i j = ρ i * σ j * B i (index j))
    (kernel : ∀ y : V → K, (∀ v, ¬allowed v → y v=0) →
      (∀ i, (∑ v, B i v*y v)=0) → y=0) :
    Function.Injective A.mulVec := by
  classical
  intro f g same
  let x := f-g
  have zero : A.mulVec x=0 := by
    change A.mulVec (f-g) = 0
    rw [Matrix.mulVec_sub,same,sub_self]
  let y (v : V) := ∑ j, if index j=v then σ j*x j else 0
  have supported (v : V) (out : ¬allowed v) : y v=0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro h
    exact out (h ▸ inside j)
  have recover (j : J) : y (index j)=σ j*x j := by
    simp [y,unique.eq_iff]
  have collapse (i : I) : (∑ v, B i v*y v)=∑ j, B i (index j)*(σ j*x j) := by
    simp only [y,Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    simp
  have vanish (i : I) : (∑ v, B i v*y v)=0 := by
    have h : ρ i*(∑ v, B i v*y v)=0 := calc
      _ = ρ i*(∑ j, B i (index j)*(σ j*x j)) := by rw [collapse]
      _ = ∑ j, A i j*x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [entry]
        ring
      _ = 0 := congrFun zero i
    exact (mul_eq_zero.mp h).resolve_left (hr i)
  have detected := kernel y supported vanish
  funext j
  have result := (recover j).symm.trans (congrFun detected (index j))
  exact sub_eq_zero.mp ((mul_eq_zero.mp result).resolve_left (hc j))

/-- The signed local arithmetic identities and the padded-system certificate
give full rank of one genuine complex residue block. -/
theorem local_block_injective {L : ℕ} [NeZero L] (a : ZMod L) (good : CriticalConicEvenSparse.Good L a.val)
    (unique : Function.Injective
      (fun kv : {kv : Fin (L-1) × Fin (L+1) // columnGrade 0 kv = a} => kv.val.2))
    (inside : ∀ kv : {kv : Fin (L-1) × Fin (L+1) // columnGrade 0 kv = a},
      CriticalConicEvenSparse.allowed ((L : ℤ)+2) a.val kv.val.2.val)
    (entry : ∀ (s : Fin L) (kv : {kv : Fin (L-1) × Fin (L+1) // columnGrade 0 kv = a}),
      coefficientMatrix L (L+1) (L-1) (L^2-2) (localCoeff L a.val) (strideRows a s).val kv.val =
        (-1 : ℤ)^(s.val+kv.val.2.val) * CriticalConicEvenSparse.entry ((L : ℤ)+2) a.val s.val kv.val.2.val) :
    Function.Injective (residueBlock (u := L-1) (b := L^2-2) 0 a (fun n => (localCoeff L a.val n : ℂ))).mulVec := by
  classical
  let block := residueBlock (u := L-1) (b := L^2-2) 0 a (fun n => (localCoeff L a.val n : ℂ))
  let A := block.submatrix (strideRows a) id
  let B : Matrix (Fin L) (Fin (L+1)) ℂ :=
    fun s v => (CriticalConicEvenSparse.entry ((L : ℤ)+2) a.val s.val v.val : ℂ)
  have matchEntry (s : Fin L) (kv : {kv : Fin (L-1) × Fin (L+1) // columnGrade 0 kv = a}) :
      A s kv = (-1 : ℂ)^s.val * (-1 : ℂ)^kv.val.2.val * B s kv.val.2 := by
    change coefficientMatrix L (L+1) (L-1) (L^2-2) (fun n => (localCoeff L a.val n : ℂ))
      (strideRows a s).val kv.val = _
    have casted := congrArg (fun x : ℤ => (x : ℂ)) (entry s kv)
    simpa only [B,coefficientMatrix_int_cast,Int.cast_mul,Int.cast_pow,
      Int.cast_neg,Int.cast_one,pow_add] using casted
  have inj : Function.Injective A.mulVec := injective_of_padded_kernel A B _ unique _ inside
    (fun s => (-1 : ℂ)^s.val) (fun kv => (-1 : ℂ)^kv.val.2.val)
    (fun _ => pow_ne_zero _ (by norm_num)) (fun _ => pow_ne_zero _ (by norm_num)) matchEntry good
  intro f g same
  apply inj
  funext s
  exact congrFun same (strideRows a s)

theorem localCoeff_outside {L : ℕ} (a j : ℕ) (out : (j : ZMod L) ≠ 0) : localCoeff L a j=0 := by
  have ne : j % L ≠ 0 := by
    intro eq
    apply out
    rw [←ZMod.natCast_mod j L,eq,Nat.cast_zero]
  simp only [localCoeff,if_neg ne]

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

/-- Select the prescribed representative of the doubled column coordinate
modulo an odd integer, allowing negative windings. -/
theorem position_of_phase {m a v p n : ℤ} (odd : Odd m) (bounds : -1 ≤ p ∧ p ≤ m-2)
    (phase : 2*p=v-a+n*m) : CriticalConicEvenSparse.position m a v=p := by
  let half := (m+1)/2
  have twice : 2*half=m+1 := by
    obtain ⟨k,hk⟩ := odd
    dsimp only [half]
    omega
  have congruence : (v-a)*half+1=(p+1)+(p-n*half)*m := by
    linear_combination -half*phase+p*twice
  change ((v-a)*half+1)%m-1=p
  rw [congruence,Int.add_mul_emod_self_right,Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- The omitted physical column would correspond to layer `L-1`, which
lies just beyond the declared first coordinate. -/
private lemma column_not_missing {L : ℕ} [NeZero L] (odd : Odd L) (a : ZMod L)
    (kv : Fin (L-1) × Fin (L+1)) (member : columnGrade 0 kv=a) : (kv.2.val : ZMod L)≠a-2 := by
  intro missing
  change (kv.2.val : ZMod L)-2*(kv.1.val : ZMod L)+2*0=a at member
  have zero : (kv.1.val : ZMod L)+1=0 := by
    apply (ZMod.add_self_eq_zero_iff_eq_zero odd).mp
    linear_combination missing-member
  have cast : ((kv.1.val+1 : ℕ) : ZMod L)=0 := by simpa only [Nat.cast_add,Nat.cast_one] using zero
  have short : kv.1.val+1<L := by have := kv.1.isLt; omega
  have val := congrArg ZMod.val cast
  rw [ZMod.val_natCast_of_lt short,ZMod.val_zero] at val
  omega

/-- A column in the zero-offset residue class gives an allowed physical
index and its signed winding relative to the integer position. -/
theorem physical_column {L : ℕ} [NeZero L] (large : 7≤L) (odd : Odd L) (a : ZMod L)
    (kv : Fin (L-1) × Fin (L+1)) (member : columnGrade 0 kv=a) :
    CriticalConicEvenSparse.allowed ((L : ℤ)+2) a.val kv.2.val ∧
    ∃ n : ℤ, 2*(kv.1.val : ℤ)+(a.val : ℤ)-(kv.2.val : ℤ)=n*(L : ℤ) ∧
      CriticalConicEvenSparse.position ((L : ℤ)+2) a.val kv.2.val=(kv.1.val : ℤ)+n := by
  have missing := column_not_missing odd a kv member
  change (kv.2.val : ZMod L)-2*(kv.1.val : ZMod L)+2*0=a at member
  constructor
  · constructor
    · intro eq
      apply missing
      have val := congrArg (fun z : ℤ => (z : ZMod L)) eq
      simpa only [Int.cast_sub,Int.cast_natCast,Int.cast_ofNat,ZMod.natCast_zmod_val] using val
    · intro eq
      apply missing
      have val := congrArg (fun z : ℤ => (z : ZMod L)) eq
      simp only [Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,ZMod.natCast_zmod_val,
        ZMod.natCast_self,zero_add] at val
      linear_combination val
  · have congruence : ((2*(kv.1.val : ℤ)+(a.val : ℤ)-(kv.2.val : ℤ) : ℤ) : ZMod L)=0 := by
      simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,ZMod.natCast_zmod_val]
      linear_combination -member
    obtain ⟨n,hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp congruence
    have join := hn.trans (mul_comm (L : ℤ) n)
    have ab : 0 ≤ (a.val : ℤ) ∧ (a.val : ℤ)<L := ⟨Int.natCast_nonneg _,by exact_mod_cast a.val_lt⟩
    have kb : 0 ≤ (kv.1.val : ℤ) ∧ (kv.1.val : ℤ)<(L : ℤ)-1 := by have := kv.1.isLt; omega
    have vb : 0 ≤ (kv.2.val : ℤ) ∧ (kv.2.val : ℤ)≤L := by have := kv.2.isLt; omega
    obtain ⟨lo,hi,phase⟩ := CriticalConicEvenResearch.physical_column_index (by omega : (5:ℤ)≤L) ab kb vb join
    have om : Odd ((L : ℤ)+2) := odd_add_two.mpr ((Int.odd_coe_nat L).mpr odd)
    exact ⟨n,join,position_of_phase om ⟨lo,by omega⟩ phase⟩

/-- Integer row coordinate after subtracting the residue and wrapping once
when the first coordinate precedes the residue representative. -/
theorem physical_row {L : ℕ} [NeZero L] (a : ZMod L) (sj : Fin L × Fin L) (member : rowGrade sj=a) :
    (sj.2.val : ℤ)=(sj.1.val : ℤ)-(a.val : ℤ)+(if sj.1.val<a.val then 1 else 0)*(L : ℤ) := by
  let y : ℤ := (sj.1.val : ℤ)-(a.val : ℤ)+(if sj.1.val<a.val then 1 else 0)*(L : ℤ)
  have sy := sj.1.isLt
  have ay := a.val_lt
  have range : 0≤y ∧ y<(L : ℤ) := by
    dsimp only [y]
    split <;> simp only [one_mul,zero_mul,add_zero] <;> omega
  have val : (y : ZMod L)=(sj.2.val : ZMod L) := by
    change (sj.1.val : ZMod L)-(sj.2.val : ZMod L)=a at member
    dsimp only [y]
    split <;> simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_one,
      Int.cast_zero,ZMod.natCast_zmod_val,ZMod.natCast_self,mul_zero,add_zero] <;> linear_combination member
  have read := congrArg (fun z : ZMod L => (z.val : ℤ)) val
  change (((y : ZMod L).val : ℕ) : ℤ)=((((sj.2.val : ZMod L).val) : ℕ) : ℤ) at read
  rw [ZMod.val_intCast,ZMod.val_natCast_of_lt sj.2.isLt,Int.emod_eq_of_lt range.1 range.2] at read
  exact read.symm

/-- The visible column index identifies the full column within a fixed
residue, since doubling is injective modulo odd `L`. -/
theorem physical_v_injective {L : ℕ} [NeZero L] (large : 7≤L) (odd : Odd L) (a : ZMod L) :
    Function.Injective (fun q : {kv : Fin (L-1) × Fin (L+1) // columnGrade 0 kv=a} => q.val.2) := by
  rintro ⟨⟨k,v⟩,hk⟩ ⟨⟨k',v'⟩,hk'⟩ eq
  change v=v' at eq
  subst v'
  change (v.val : ZMod L)-2*(k.val : ZMod L)+2*0=a at hk
  change (v.val : ZMod L)-2*(k'.val : ZMod L)+2*0=a at hk'
  have congruence : (k.val : ZMod L)=(k'.val : ZMod L) := by
    apply sub_eq_zero.mp
    apply (ZMod.add_self_eq_zero_iff_eq_zero odd).mp
    linear_combination hk'-hk
  have small : L-1<L := by omega
  have val := congrArg ZMod.val congruence
  rw [ZMod.val_natCast_of_lt (k.isLt.trans small),ZMod.val_natCast_of_lt (k'.isLt.trans small)] at val
  exact Subtype.ext (Prod.ext (Fin.ext val) rfl)

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open CriticalConicEvenSparse (weight position entry)

/-- A supported multiple of L reads the corresponding private weight.
Both guards exactly implement its zero extension. -/
private lemma weight_multiple {L : ℕ} (large : 7 ≤ L) (a : ℕ) (x : ℤ) :
    guardedCoeff (L^2-2) (localCoeff L a) ((L:ℤ)*x) = weight ((L:ℤ)+2) a x := by
  have lp : 0 < (L:ℤ) := by omega
  have square : 2 ≤ L^2 := by nlinarith only [large, Nat.mul_self_le_mul_self large]
  have cast : ((L^2-2 : ℕ):ℤ) = (L:ℤ)^2-2 := by
    rw [Nat.cast_sub square,Nat.cast_pow,Nat.cast_ofNat]
  by_cases neg : x < 0
  · have h := mul_neg_of_pos_of_neg lp neg
    simp [guardedCoeff,not_le.mpr h,weight,neg]
  by_cases high : (L:ℤ) ≤ x
  · have atLeast := mul_le_mul_of_nonneg_left high lp.le
    have end_before : ((L^2-2 : ℕ):ℤ) < (L:ℤ)*x := by rw [cast]; nlinarith only [atLeast]
    rw [weight,if_pos (Or.inr (by omega) : x<0 ∨ (L:ℤ)+2-2≤x)]
    simp [guardedCoeff,not_le.mpr end_before]
  lift x to ℕ using (le_of_not_gt neg) with q
  have hr : q+1 ≤ L := by omega
  have hm := Nat.mul_le_mul_left L hr
  have bounded : L*q ≤ L^2-2 := by
    rw [Nat.mul_add,Nat.mul_one] at hm
    rw [pow_two]
    omega
  have lower : 0 ≤ (L:ℤ)*(q:ℤ) := by positivity
  have upper : (L:ℤ)*(q:ℤ) ≤ ((L^2-2 : ℕ):ℤ) := by exact_mod_cast bounded
  have natural : ((L:ℤ)*(q:ℤ)).toNat=L*q := by norm_cast
  simp only [guardedCoeff,lower,upper,and_true,if_true,natural,localCoeff,Nat.mul_mod_right]
  simp [Nat.mul_div_cancel_left _ (show 0<L by omega)]

private lemma grade_of_guarded {L b a : ℕ} (z : ℤ)
    (nonzero : guardedCoeff b (localCoeff L a) z ≠ 0) : (L:ℤ) ∣ z := by
  by_cases inside : 0≤z ∧ z≤(b:ℤ)
  · rw [guardedCoeff,if_pos inside,localCoeff] at nonzero
    split at nonzero
    next h =>
      have div := Nat.dvd_of_mod_eq_zero h
      have : (L:ℤ) ∣ (z.toNat:ℤ) := by exact_mod_cast div
      simpa only [Int.toNat_of_nonneg inside.1] using this
    next => exact False.elim (nonzero rfl)
  · exact False.elim (nonzero (by simp [guardedCoeff,inside]))

private lemma three_multiples {L z : ℤ} (pos : 0<L) (lower : -L<z) (upper : z<3*L)
    (div : L ∣ z) : z=0 ∨ z=L ∨ z=2*L := by
  obtain ⟨w,rfl⟩ := div
  have lo : 0≤w := by
    by_contra! h
    have bad := mul_le_mul_of_nonneg_left (show w≤ -1 by omega) pos.le
    nlinarith only [lower,bad]
  have hi : w≤2 := by
    by_contra! h
    have bad := mul_le_mul_of_nonneg_left (show 3≤w by omega) pos.le
    nlinarith only [upper,bad]
  rcases (show w=0 ∨ w=1 ∨ w=2 by omega) with rfl|rfl|rfl <;> simp [mul_comm]

private lemma summand_sign {L l s v w : ℕ} (odd : Odd L) (h : l+v=s+w*L) :
    (-1:ℤ)^l = (-1:ℤ)^(s+v)*(-1:ℤ)^w := by
  have signs : (-1:ℤ)^l*(-1:ℤ)^v=(-1:ℤ)^s*(-1:ℤ)^w := by
    rw [←pow_add,h,pow_add,Nat.mul_comm w L,pow_mul,odd.neg_one_pow]
  have twice : (-1:ℤ)^v*(-1:ℤ)^v=1 := by rw [←mul_pow]; norm_num
  calc
    _ = ((-1:ℤ)^l*(-1:ℤ)^v)*(-1:ℤ)^v := by rw [mul_assoc,twice,mul_one]
    _ = _ := by rw [signs,pow_add]; ring

private lemma sum_at_integer (N : ℕ) (z c : ℤ) :
    (∑ i : Fin N, if (i.val:ℤ)=z then c else 0) =
      if 0≤z ∧ z<(N:ℤ) then c else 0 := by
  classical
  by_cases inRange : 0≤z ∧ z<(N:ℤ)
  · let a : Fin N := ⟨z.toNat,by omega⟩
    have atIndex (i : Fin N) : ((i.val:ℤ)=z) ↔ i=a := by
      rw [Fin.ext_iff]
      change _ ↔ i.val=z.toNat
      omega
    simp_rw [atIndex]
    simp [inRange]
  · have off (i : Fin N) : (i.val:ℤ) ≠ z := by have := i.isLt; omega
    simp [off,inRange]

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open CriticalConicEvenSparse (weight entry position)

private def shiftValue (W : ℤ → ℤ) (s v : ℕ) (p : ℤ) (w : ℕ) : ℤ :=
  (-1:ℤ)^(s+v)*(-1:ℤ)^w * W ((s:ℤ)+1-w) * W (p+w)

/-- A surviving summand is at one of the three spaced integer offsets. -/
private theorem convolution {L : ℕ} (large : 7≤L) (odd : Odd L) (a s j : Fin L)
    (k : Fin (L-1)) (v : Fin (L+1)) (n : ℤ)
    (join : 2*(k.val:ℤ)+(a.val:ℤ)-(v.val:ℤ)=n*(L:ℤ))
    (row : (j.val:ℤ)=(s.val:ℤ)-(a.val:ℤ)+(if s.val<a.val then 1 else 0)*(L:ℤ)) :
    coefficientMatrix L (L+1) (L-1) (L^2-2) (localCoeff L a.val) (s,j) (k,v) =
      ∑ w : Fin 3, if 0 ≤ (s.val:ℤ)-v.val+(w.val:ℤ)*L ∧
          (s.val:ℤ)-v.val+(w.val:ℤ)*L < ((L+2:ℕ):ℤ) then
        shiftValue (weight ((L:ℤ)+2) a.val) s.val v.val
          ((k.val:ℤ)+n-(if s.val<a.val then 1 else 0)) w.val else 0 := by
  classical
  let z := (s.val:ℤ)-v.val
  let δ : ℤ := if s.val<a.val then 1 else 0
  let p := (k.val:ℤ)+n-δ
  let W := weight ((L:ℤ)+2) a.val
  let G := guardedCoeff (L^2-2) (localCoeff L a.val)
  let leftArg (l : Fin (L+2)) : ℤ := ((((L+2)*k.val+l.val:ℕ):ℤ)-(j.val:ℤ))
  let rightArg (l : Fin (L+2)) : ℤ := ((((L+1)*(s.val+1):ℕ):ℤ)-1-l.val-v.val)
  let term (l : Fin (L+2)) := (-1:ℤ)^l.val * G (leftArg l) * G (rightArg l)
  let val (w : Fin 3) := shiftValue W s.val v.val p w.val
  have lp : 0<(L:ℤ) := by omega
  have rightIdentity (l : Fin (L+2)) :
      rightArg l = (L:ℤ)*(s.val+1) - ((l.val:ℤ)+v.val-s.val) := by
    dsimp [rightArg]
    ring
  have supported (l : Fin (L+2)) (nz : term l ≠ 0) :
      ∃ w : Fin 3, (l.val:ℤ) = z + (w.val:ℤ)*L := by
    have nonzero : G (rightArg l) ≠ 0 := by
      intro bad
      exact nz (by simp [term,bad])
    have multiple := grade_of_guarded (rightArg l) nonzero
    rw [rightIdentity] at multiple
    obtain ⟨coef,eq⟩ := multiple
    have div : (L:ℤ) ∣ ((l.val:ℤ)+v.val-s.val) := by
      refine ⟨(s.val:ℤ)+1-coef,?_⟩
      linear_combination -eq
    have lh:=l.isLt
    have sh:=s.isLt
    have vh:=v.isLt
    rcases three_multiples lp (by omega) (by omega) div with h | h | h
    · exact ⟨0,by change (l.val:ℤ) = (s.val:ℤ)-v.val+0*L; omega⟩
    · exact ⟨1,by change (l.val:ℤ) = (s.val:ℤ)-v.val+1*L; omega⟩
    · exact ⟨2,by change (l.val:ℤ) = (s.val:ℤ)-v.val+2*L; omega⟩
  have selected (l : Fin (L+2)) (w : Fin 3) (hw : (l.val:ℤ) = z + (w.val:ℤ)*L) :
      term l = val w := by
    have hleft : leftArg l = (L:ℤ)*(p+w.val) := by
      dsimp [leftArg,p,δ]
      rw [hw,row]
      dsimp [z]
      linear_combination join
    have hright : rightArg l = (L:ℤ)*((s.val:ℤ)+1-w.val) := by
      rw [rightIdentity,hw]
      dsimp [z]
      ring
    have parity : l.val+v.val=s.val+w.val*L := by
      exact_mod_cast (show (l.val:ℤ)+v.val=s.val+(w.val:ℤ)*L by dsimp [z] at hw; linarith only [hw])
    dsimp only [term,G,val,shiftValue,W]
    rw [hleft,hright,weight_multiple large,weight_multiple large,summand_sign odd parity]
    ring
  have decode (l : Fin (L+2)) : term l =
      ∑ w : Fin 3, if (l.val:ℤ) = z+(w.val:ℤ)*L then val w else 0 := by
    by_cases hit : ∃ w : Fin 3, (l.val:ℤ)=z+(w.val:ℤ)*L
    · obtain ⟨w,hw⟩ := hit
      rw [Finset.sum_eq_single w]
      · rw [if_pos hw,selected l w hw]
      · intro u _ une
        apply if_neg
        intro hu
        have equal : (u.val:ℤ)*(L:ℤ) = (w.val:ℤ)*L := by linear_combination hw-hu
        have cancel := mul_right_cancel₀ lp.ne' equal
        exact une (Fin.ext (by exact_mod_cast cancel))
      · simp
    · have off (w : Fin 3) : (l.val:ℤ) ≠ z+(w.val:ℤ)*L := fun h => hit ⟨w,h⟩
      have zero : term l=0 := by_contra fun h => hit (supported l h)
      simp [off,zero]
  change (∑ l, term l) = _
  simp_rw [decode]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact sum_at_integer (L+2) (z+(w.val:ℤ)*L) (val w)

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

open CriticalConicEvenSparse (weight entry position)

/-- Summing the three offsets gives two interval indicators and the one
exceptional corner. The possible second wrap at s=0 has zero weight. -/
private lemma evaluate_offsets {L : ℕ} (large : 7≤L) (s v : ℕ) (hs : s<L) (hv : v<L+1)
    (W : ℤ → ℤ) (outside : W (-1)=0) (p : ℤ) :
    (∑ w : Fin 3, if 0 ≤ (s:ℤ)-v+(w.val:ℤ)*L ∧ (s:ℤ)-v+(w.val:ℤ)*L < ((L+2:ℕ):ℤ) then
      shiftValue W s v p w.val else 0) =
    (-1:ℤ)^(s+v) *
      ((if (v:ℤ)≤ s then W ((s:ℤ)+1)*W p else 0) -
       (if (s:ℤ)≤v+1 then W s*W (p+1) else 0) +
       (if (s:ℤ)=1 ∧ (v:ℤ)=L then W 0*W (p+2) else 0)) := by
  let gate (i : ℤ) := 0≤(s:ℤ)-v+i*L ∧ (s:ℤ)-v+i*L<((L+2:ℕ):ℤ)
  rw [Fin.sum_univ_three]
  change (if gate 0 then shiftValue W s v p 0 else 0) +
    (if gate 1 then shiftValue W s v p 1 else 0) +
    (if gate 2 then shiftValue W s v p 2 else 0) = _
  have first : gate 0 ↔ (v:ℤ)≤ s := by dsimp [gate]; omega
  have middle : gate 1 ↔ (s:ℤ)≤v+1 := by dsimp [gate]; omega
  have last : (if gate 2 then shiftValue W s v p 2 else 0) =
      (if (s:ℤ)=1 ∧ (v:ℤ)=L then (-1:ℤ)^(s+v)*W 0*W (p+2) else 0) := by
    by_cases empty : s=0
    · subst s
      simp [shiftValue,outside]
    have condition : gate 2 ↔ (s:ℤ)=1 ∧ (v:ℤ)=L := by dsimp [gate]; omega
    simp only [condition]
    split
    next hit =>
      have one : (s:ℤ)=1 := hit.1
      simp [shiftValue,one]
    next => rfl
  simp only [first,middle,last]
  split_ifs <;> simp [shiftValue] <;> ring

/-- On a physical row/column grade the canonical guarded coefficient sum
is precisely the row- and column-sign-scaled sparse entry. -/
theorem signed_entry {L : ℕ} (large : 7≤L) (odd : Odd L) (a s j : Fin L)
    (k : Fin (L-1)) (v : Fin (L+1)) (n : ℤ)
    (join : 2*(k.val:ℤ)+(a.val:ℤ)-(v.val:ℤ)=n*(L:ℤ))
    (row : (j.val:ℤ)=(s.val:ℤ)-(a.val:ℤ)+(if s.val<a.val then 1 else 0)*(L:ℤ))
    (pos : position ((L:ℤ)+2) a.val v.val=(k.val:ℤ)+n) :
    coefficientMatrix L (L+1) (L-1) (L^2-2) (localCoeff L a.val) (s,j) (k,v) =
      (-1:ℤ)^(s.val+v.val)*entry ((L:ℤ)+2) a.val s.val v.val := by
  rw [convolution large odd a s j k v n join row]
  rw [evaluate_offsets large s.val v.val s.isLt v.isLt _ (by simp [weight])]
  simp only [entry,pos,Int.ofNat_lt,add_sub_cancel_right]

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

theorem residue_injective_of_good {L : ℕ} [NeZero L] (large : 7 ≤ L) (odd : Odd L)
    (a : ZMod L) (good : CriticalConicEvenSparse.Good L a.val) :
    Function.Injective (residueBlock (u := L-1) (b := L^2-2) 0 a (fun n => (localCoeff L a.val n : ℂ))).mulVec := by
  apply local_block_injective a good (physical_v_injective large odd a)
  · exact fun kv => (physical_column large odd a kv.val kv.property).1
  · intro s kv
    obtain ⟨n,join,pos⟩ := (physical_column large odd a kv.val kv.property).2
    let row := strideRows a s
    have represented := physical_row a row.val row.property
    exact signed_entry large odd ⟨a.val,ZMod.val_lt _⟩ s row.val.2 kv.val.1 kv.val.2 n join represented pos

/-- Each local certificate can use its own integral weights. Their independent
witnesses suffice for a single complex matrix of full column rank. -/
theorem matrix_of_good {L : ℕ} (large : 7 ≤ L) (odd : Odd L)
    (good : ∀ a : ℕ, a < L → CriticalConicEvenSparse.Good L a) :
    ∃ d : ℕ→ℂ, Function.Injective (coefficientMatrix L (L+1) (L-1) (L^2-2) d).mulVec := by
  let _ : NeZero L := ⟨by omega⟩
  obtain ⟨d,_,inj⟩ := common_sparse_coefficients (u := L-1) (b := L^2-2) (0 : ZMod L) (fun a =>
    ⟨fun n => (localCoeff L a.val n : ℂ),
      fun n off => by
        change (localCoeff L a.val n : ℂ) = 0
        rw [localCoeff_outside a.val n off,Int.cast_zero],
      residue_injective_of_good large odd a (good a.val (ZMod.val_lt _))⟩)
  exact ⟨d,inj⟩

end CriticalConicEvenBoundary

namespace CriticalConicEvenBoundary

/-- At an even sharp boundary the residue cores supply a full-column-rank
coefficient matrix. The conic rank theorem converts it to generic rank. -/
theorem higher_sharp_even
    (finite : ∀ L a x y : ℕ, 7≤L → Odd L → a < L → x≤22 → y≤22 →
      ((L+2=3*x+y ∧ a=x) ∨ (L+2=3*x+2*y ∧ a=2*x+y) ∨
       (L+2=2*x+3*y ∧ a=x+y) ∨ (L+2=x+3*y ∧ a=x+2*y)) → CriticalConicEvenSparse.Good L a) :
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2.H2 := by
  intro h ten even
  obtain ⟨L,rfl⟩ : ∃ L,h=L+1 := ⟨h-1,by omega⟩
  have oddL : Odd L := by
    obtain ⟨k,hk⟩ := even
    exact ⟨k-1,by omega⟩
  obtain ⟨d,full⟩ := matrix_of_good (L:=L) (by omega) oddL
    (fun a i => CriticalConicEvenSparse.Tight.all_good_of_representatives finite (by omega) oddL i)
  have top := rank_of_even_boundary_matrix (by omega : 5≤L) oddL d full
  have room := congrArg (fun t : ℕ => (L+1)*t) (show L+1-2+1=L by omega)
  have width : (L+1)*(L+1-2)-1=L^2-2 := by
    have e : (L+1)*(L+1-2)+1=L^2 := by nlinarith only [room]
    omega
  simpa only [width] using top

end CriticalConicEvenBoundary

namespace CriticalConicEvenFinite
open CriticalConicEvenSparse

def ordinary (m a s : ℤ) : Prop :=
  3 ≤ s ∧ s < m-2 ∧ (s-1 < a ↔ s < a) ∧
    weight m a (s-1)=1 ∧ weight m a s=1 ∧ weight m a (s+1)=1 ∧
    weight m a (position m a s - (if s < a then 1 else 0))=1 ∧
    weight m a (position m a (s-2)+1 - (if s < a then 1 else 0))=1

instance (m a s : ℤ) : Decidable (ordinary m a s) := by unfold ordinary;infer_instance

private lemma threshold_difference (s v b c : ℤ) :
    (if v ≤ s then b else 0) - (if s ≤ v+1 then c else 0) -
        ((if v ≤ s-1 then b else 0) - (if s-1 ≤ v+1 then c else 0)) =
      (if v=s then b else 0) + (if v=s-2 then c else 0) := by
  split_ifs <;> omega

theorem ordinary_difference {m a s : ℤ} (clean : ordinary m a s) (v : ℤ) :
    entry m a s v-entry m a (s-1) v=(if v=s then 1 else 0)+(if v=s-2 then 1 else 0) := by
  obtain ⟨low,_,same,prior,this,next,here,back⟩:=clean
  have d : (if s-1 < a then (1:ℤ) else 0)=(if s < a then 1 else 0) :=
    if_congr same rfl rfl
  have eq : position m a v-(if s < a then 1 else 0)+1 = position m a v+1-(if s < a then 1 else 0) := by ring
  simp only [entry,d,sub_add_cancel,prior,this,next,one_mul,show s≠1 by omega,
    show s-1≠1 by omega,false_and,if_false,add_zero,eq,threshold_difference]
  by_cases e : v=s
  · subst v; simp [here,show s ≠ s-2 by omega]
  by_cases f : v=s-2
  · subst v; simp [back,e]
  simp [e,f]

def previous {L : ℕ} (v : Fin (L+1)) : Fin (L+1) := ⟨v.val-2,lt_of_le_of_lt (Nat.sub_le ..) v.isLt⟩

lemma ordinary_equation {L a : ℕ} (x : Fin (L+1) → ℂ)
    (eqs : ∀ s : Fin L,∑ v,(entry (L+2) a s.val v.val : ℂ)*x v=0)
    (s : Fin L) (clean : ordinary (L+2) a s.val) :
    x s.castSucc = -x (previous s.castSucc) := by
  classical
  have low : 3 ≤ s.val := by have := clean.1;omega
  let prior : Fin L := ⟨s.val-1,lt_of_le_of_lt (Nat.sub_le ..) s.isLt⟩
  have ip : (prior.val : ℤ) = (s.val:ℤ)-1 := by dsimp [prior];omega
  have ev (v : Fin (L+1)) : ((v.val:ℤ)=(s.val:ℤ)) ↔ v=s.castSucc := by
    constructor
    · intro h;apply Fin.ext;exact_mod_cast h
    · rintro rfl;rfl
  have ep (v : Fin (L+1)) : ((v.val:ℤ)=(s.val:ℤ)-2) ↔ v=previous s.castSucc := by
    constructor
    · intro h; apply Fin.ext;change v.val=s.val-2;omega
    · rintro rfl;change ((s.val-2:ℕ):ℤ)=(s.val:ℤ)-2;omega
  have z : (∑ v : Fin (L+1), ((entry (L+2) a s.val v.val - entry (L+2) a ((s.val:ℤ)-1) v.val : ℤ):ℂ)*x v)=0 := by
    simp only [Int.cast_sub,sub_mul,Finset.sum_sub_distrib,← ip,eqs,sub_self]
  simp only [ordinary_difference clean,Int.cast_add,ev,ep] at z
  have castOne (v t : Fin (L+1)) :
      ((if v=t then (1:ℤ) else 0 : ℤ):ℂ)*x v = if v=t then x v else 0 := by
    by_cases e : v=t <;> simp [e]
  simp only [add_mul,castOne,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at z
  exact eq_neg_of_add_eq_zero_left z

/-- A signed code denotes zero or one signed occurrence of a retained coordinate. -/
def indicator (code : ℤ) {k : ℕ} (i : Fin k) : ℤ :=
  if code=(i.val:ℤ)+1 then 1 else if code= -((i.val:ℤ)+1) then -1 else 0

lemma indicator_neg {k : ℕ} (s : ℤ) (i : Fin k) :
    indicator (-s) i = -indicator s i := by
  unfold indicator
  split_ifs <;> omega

lemma reconstruct {L a k : ℕ} (code : Fin (L+1) → ℤ) (free : Fin k → Fin (L+1))
    (choice : ∀ v, (¬allowed (L+2) a v.val ∧ code v=0) ∨
        (∃ i,free i=v ∧ code v=(i.val:ℤ)+1) ∨
        (∃ s : Fin L,s.castSucc=v ∧ ordinary (L+2) a s.val ∧ code v = -code (previous v)))
    (x : Fin (L+1) → ℂ) (miss : ∀ v,¬allowed (L+2) a v.val → x v=0)
    (eqs : ∀ s : Fin L,∑ v,(entry (L+2) a s.val v.val : ℂ)*x v=0)
    (v : Fin (L+1)) : x v=∑ i,(indicator (code v) i : ℂ)*x (free i) := by
  classical
  induction v using Fin.strong_induction_on with
  | h v ih =>
    rcases choice v with ⟨absent,z⟩ | ⟨j,atj,z⟩ | ⟨s,atv,clean,z⟩
    · rw [miss v absent,z]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro i _
      have ind : indicator 0 i=0 := by unfold indicator;split_ifs <;> omega
      simp [ind]
    · rw [z,← atj]
      rw [Finset.sum_eq_single j]
      · simp [indicator]
      · intro i _ ne
        have ind : indicator ((j.val:ℤ)+1) i = 0 := by
          have neq : i.val≠j.val := by intro h;exact ne (Fin.ext h)
          unfold indicator;split_ifs <;> omega
        simp [ind]
      · simp
    · subst v
      have lt : previous s.castSucc < s.castSucc := by
        have := clean.1
        change s.val-2 < s.val
        omega
      rw [ordinary_equation x eqs s clean,ih _ lt,z]
      simp [indicator_neg,Finset.sum_neg_distrib]

theorem good_of_core {L a k : ℕ} (code : Fin (L+1) → ℤ) (free : Fin k → Fin (L+1))
    (row : Fin k → Fin L) (A : Matrix (Fin k) (Fin k) ℤ)
    (choice : ∀ v, (¬allowed (L+2) a v.val ∧ code v=0) ∨
        (∃ i,free i=v ∧ code v=(i.val:ℤ)+1) ∨
        (∃ s : Fin L,s.castSucc=v ∧ ordinary (L+2) a s.val ∧ code v = -code (previous v)))
    (readback : ∀ i j,A i j = ∑ v,entry (L+2) a (row i).val v.val * indicator (code v) j)
    (inj : Function.Injective (A.map (Int.castRingHom ℂ)).mulVec) : Good L a := by
  classical
  intro x miss eqs
  let y (i : Fin k) := x (free i)
  have rep (v : Fin (L+1)) : x v=∑ j,(indicator (code v) j : ℂ)*y j :=
    reconstruct code free choice x miss eqs v
  have kernel : (A.map (Int.castRingHom ℂ)).mulVec y=0 := by
    funext i
    change (∑ j, (A i j : ℂ)*y j)=0
    simp only [readback,Int.cast_sum,Int.cast_mul,Finset.sum_mul]
    rw [Finset.sum_comm,←eqs (row i)]
    apply Finset.sum_congr rfl
    intro v _
    rw [rep,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have zero := inj (kernel.trans (Matrix.mulVec_zero _).symm)
  funext v
  simp [rep,zero]

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
open CriticalConicEvenSparse

def radix : ℤ := 524288

/-- One signed integer evaluates all coordinates at widely separated powers. -/
def tagPower (t : ℤ) : ℤ :=
  if t=0 then 0 else if 0<t then radix^(t.natAbs-1) else -(radix^(t.natAbs-1))

lemma pack_tag {k : ℕ} (t : ℤ) (bound : t.natAbs ≤ k) :
    (∑ j : Fin k,indicator t j*radix^j.val)=tagPower t := by
  classical
  by_cases zero : t=0
  · subst t
    simp only [tagPower,ite_true]
    apply Finset.sum_eq_zero
    intro j _
    have z : indicator 0 j=0 := by unfold indicator; split_ifs <;> omega
    rw [z,zero_mul]
  have pos : 0<t.natAbs := Int.natAbs_pos.mpr zero
  let j : Fin k := ⟨t.natAbs-1,by omega⟩
  have value : t=(j.val:ℤ)+1 ∨ t= -((j.val:ℤ)+1) := by
    dsimp [j]
    cases t <;> simp_all <;> omega
  rw [Finset.sum_eq_single j]
  · rcases value with plus | minus
    · have ind : indicator t j=1 := by rw [indicator,if_pos plus]
      rw [ind,one_mul,tagPower,if_neg zero,if_pos (show 0<t by omega)]
    · have distinct : t≠(j.val:ℤ)+1 := by omega
      have ind : indicator t j= -1 := by rw [indicator,if_neg distinct,if_pos minus]
      rw [ind,neg_one_mul,tagPower,if_neg zero,if_neg (show ¬0<t by omega)]
  · intro i _ diff
    have ne : i.val≠j.val := by intro z;exact diff (Fin.ext z)
    have other : indicator t i=0 := by unfold indicator;split_ifs <;> omega
    simp [other]
  · simp

lemma pack_zero {n : ℕ} (f : Fin n → ℤ)
    (bounded : ∀ i, -radix < f i ∧ f i < radix)
    (eq : ∑ i, f i*radix^i.val = 0) : ∀ i,f i=0 := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    let tail : ℤ := ∑ i : Fin n,f i.succ*radix^i.val
    have base : f 0+radix*tail=0 := by
      rw [Fin.sum_univ_succ] at eq
      simpa only [tail,Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,
        ←mul_assoc,←Finset.sum_mul,mul_comm radix] using eq
    have dvd : radix∣f 0 := ⟨-tail,by linear_combination base⟩
    have b := bounded 0
    have first : f 0=0 := by
      by_cases nn : 0 ≤ f 0
      · exact Int.eq_zero_of_dvd_of_nonneg_of_lt nn b.2 dvd
      · have := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ -f 0 by omega)
          (show -f 0<radix by omega) (dvd_neg.mpr dvd)
        omega
    rw [first,zero_add] at base
    have tail0 := (mul_eq_zero.mp base).resolve_left (by decide : radix≠0)
    exact Fin.cases first (ih (fun j => f j.succ) (fun j => bounded j.succ) tail0)

lemma weight_bounds (m a u : ℤ) : 0 ≤ weight m a u ∧ weight m a u ≤ 17 := by
  unfold weight
  split_ifs <;> decide

private lemma term_bound (m a i j : ℤ) (P : Prop) [Decidable P] :
    0 ≤ (if P then weight m a i*weight m a j else 0) ∧
      (if P then weight m a i*weight m a j else 0) ≤ 289 := by
  obtain ⟨lo,hi⟩:=weight_bounds m a i
  obtain ⟨lo',hi'⟩:=weight_bounds m a j
  by_cases f:P
  · simpa [f] using And.intro (mul_nonneg lo lo') (mul_le_mul hi hi' lo' (by decide : (0:ℤ) ≤ 17))
  · simp [f]

lemma entry_bounds (m a s v : ℤ) : -867 ≤ entry m a s v ∧ entry m a s v ≤ 867 := by
  let p := position m a v-(if s<a then 1 else 0)
  have t0 := term_bound m a (s+1) p (v ≤ s)
  have t1 := term_bound m a s (p+1) (s ≤ v+1)
  have t2 := term_bound m a 0 (p+2) (s=1 ∧ v=m-2)
  change -867 ≤ _ - _ + _ ∧ _ - _ + _ ≤ 867
  dsimp [p] at t0 t1 t2
  omega

lemma packed_readback {L a k : ℕ} (small : L ≤ 213) (code : Fin (L+1) → ℤ)
    (labels : ∀ v,(code v).natAbs ≤ k) (s : Fin L) (A : Fin k → ℤ)
    (size : ∀j,-512 ≤ A j ∧ A j ≤ 512)
    (cert : (∑ v,entry (L+2) a s.val v.val * tagPower (code v)) =
      ∑ j,A j * radix^j.val) :
    ∀ j,A j = ∑ v,entry (L+2) a s.val v.val*indicator (code v) j := by
  classical
  let entry' (v : Fin (L+1)) := entry (L+2) a s.val v.val
  let sum (j : Fin k) := ∑ v,entry' v*indicator (code v) j
  have eq : ∑j, (sum j-A j)*radix^j.val=0 := by
    simp only [sub_mul,Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    rw [← cert]
    simp only [sum,Finset.sum_mul,←pack_tag _ (labels _),Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have bounds (j : Fin k) : -radix < sum j-A j ∧ sum j-A j < radix := by
    have bounded (v : Fin (L+1)) : (-867:ℤ) ≤ entry' v*indicator (code v) j ∧
        entry' v*indicator (code v) j ≤ 867 := by
      have h := entry_bounds (L+2) a s.val v.val
      dsimp [entry',indicator]
      split_ifs <;> simp_all
      omega
    have lo := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => (bounded v).1)
    have hi := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => (bounded v).2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at lo hi
    change _ ≤ sum j at lo
    change sum j ≤ _ at hi
    have h := size j
    dsimp [radix]
    omega
  intro j
  exact (sub_eq_zero.mp (pack_zero (fun j => sum j-A j) bounds eq j)).symm

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
open CriticalConicEvenSparse

def allN (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => allN f n && f n

lemma allN_true {f : ℕ → Bool} {n : ℕ} (checked : allN f n=true) (i : ℕ) (hi : i < n) :
    f i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨prefixOk,last⟩ := Bool.and_eq_true_iff.mp checked
    by_cases prior : i < n
    · exact ih prefixOk prior
    · simpa only [show i=n by omega] using last

def channel (L a i v : ℕ) : ℤ := weight (L+2) a (position (L+2) a v + (i:ℤ)-1)

instance allowedDec (m a v : ℤ) : Decidable (allowed m a v) := by unfold allowed;infer_instance

end CriticalConicEvenFinite


namespace CriticalConicEvenFinite
open CriticalConicEvenSparse

def foldedRow (L a : ℕ) (code : ℕ → ℤ) (pre : ℕ → ℕ → ℤ) (s : ℕ) : ℤ :=
  let c := if s < a then 0 else 1
  let m : ℤ := L+2
  weight m a (s+1)*pre c (s+1) - weight m a s*(pre (c+1) (L+1)-pre (c+1) (s-1))
    + (if s=1 then weight m a 0*weight m a (position m a L + (c:ℤ)+1)*tagPower (code L) else 0)

private lemma finite_prefix_sum {n t : ℕ} (f p : ℕ → ℤ) (zero : p 0=0)
    (rec : ∀ i < n,p (i+1)=p i+f i) (ht : t ≤ n) :
    (∑ v : Fin n,if v.val < t then f v.val else 0)=p t := by
  classical
  induction t with
  | zero => simp [zero]
  | succ t ih =>
    let z : Fin n := ⟨t,by omega⟩
    have split (v : Fin n) : (if v.val < t+1 then f v.val else 0) =
        (if v.val < t then f v.val else 0) + (if v=z then f z.val else 0) := by
      by_cases hit : v=z
      · subst v;simp [z]
      · have diff : v.val≠t := by intro eq;exact hit (Fin.ext eq)
        by_cases low : v.val < t <;> simp [hit,low,show (v.val < t+1) ↔ (v.val < t) by omega]
    simp only [split,Finset.sum_add_distrib]
    rw [ih (by omega),Finset.sum_ite_eq',if_pos (Finset.mem_univ _)]
    exact (rec t (by omega)).symm

private lemma finite_suffix_sum {n t : ℕ} (f p : ℕ → ℤ) (zero : p 0=0)
    (rec : ∀ i < n,p (i+1)=p i+f i) (ht : t ≤ n) :
    (∑ v : Fin n,if t ≤ v.val then f v.val else 0)=p n-p t := by
  have all := finite_prefix_sum (n:=n) (t:=n) f p zero rec le_rfl
  simp only [Fin.isLt,ite_true] at all
  rw [← all,← finite_prefix_sum f p zero rec ht,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases e : t ≤ v.val <;> simp [e,show v.val < t ↔ ¬t ≤ v.val by omega]

theorem foldedRow_eq {L a : ℕ} (code : ℕ → ℤ) (pre : ℕ → ℕ → ℤ)
    (preSpec : ∀ i < 3, pre i 0=0 ∧
      ∀ j < L+1, pre i (j+1) = pre i j+channel L a i j*tagPower (code j))
    (s : Fin L) : (∑ v : Fin (L+1),entry (L+2) a s.val v.val*tagPower (code v.val)) =
      foldedRow L a code pre s.val := by
  classical
  let c : ℕ := if s.val < a then 0 else 1
  let f (i v : ℕ) := channel L a i v*tagPower (code v)
  have cB : c < 2 := by dsimp [c];split <;> decide
  have pref (i : ℕ) (hi : i < 3) : pre i 0=0 ∧
      ∀ j < L+1, pre i (j+1) = pre i j+f i j := preSpec i hi
  have ch (v : ℕ) : channel L a c v = weight (L+2) a (position (L+2) a v - (if (s.val:ℤ) < a then 1 else 0)) ∧
      channel L a (c+1) v = weight (L+2) a (position (L+2) a v - (if (s.val:ℤ) < a then 1 else 0)+1) := by
    by_cases e : s.val < a
    · have ei : (s.val:ℤ) < a := by exact_mod_cast e
      simp [channel,c,e,ei]
    · have ei : ¬(s.val:ℤ) < a := by exact_mod_cast e
      simp [channel,c,e,ei]
      congr 1
      ring
  have chCorner : position (L+2) a L + (c:ℤ)+1 =
      position (L+2) a L-(if (s.val:ℤ) < a then 1 else 0)+2 := by
    by_cases e : s.val < a
    · have ei : (s.val:ℤ) < a := by exact_mod_cast e
      simp [c,e,ei]
      ring
    · have ei : ¬(s.val:ℤ) < a := by exact_mod_cast e
      simp [c,e,ei]
      ring
  let corner := if s.val=1 then weight (L+2) a 0*weight (L+2) a (position (L+2) a L+(c:ℤ)+1)*tagPower (code L) else 0
  have component (v : Fin (L+1)) :
      entry (L+2) a s.val v.val*tagPower (code v.val) =
      weight (L+2) a (s.val+1)*(if v.val < s.val+1 then f c v.val else 0) -
      weight (L+2) a s.val*(if s.val-1 ≤ v.val then f (c+1) v.val else 0) +
      (if v=Fin.last L then corner else 0) := by
    have x : ((v.val:ℤ) ≤ s.val) ↔ v.val < s.val+1 := by omega
    have y : ((s.val:ℤ) ≤ (v.val:ℤ)+1) ↔ s.val-1 ≤ v.val := by omega
    have eqL : ((v.val:ℤ)=(L:ℤ)+2-2) ↔ v=Fin.last L := by
      constructor
      · intro eq;apply Fin.ext;change v.val=L;omega
      · rintro rfl;simp
    have eq1 : ((s.val:ℤ)=1) ↔ s.val=1 := by omega
    simp only [entry,x,y,eq1,eqL,add_mul,sub_mul,ite_mul,zero_mul,←(ch v.val).1,←(ch v.val).2]
    rw [show (if s.val=1 ∧ v=Fin.last L then weight (L+2) a 0 *
        weight (L+2) a (position (L+2) a v.val-(if (s.val:ℤ) < a then 1 else 0)+2) *
          tagPower (code v.val) else 0) = (if v=Fin.last L then corner else 0) by
      by_cases l : v=Fin.last L
      · subst v;simp [corner,chCorner,Fin.val_last]
      · simp [l]]
    simp [f,mul_ite,mul_assoc]
  simp only [component,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [finite_prefix_sum (f c) _ (pref c (by omega)).1 (pref c (by omega)).2 (by omega),
      finite_suffix_sum (f (c+1)) _ (pref (c+1) (by omega)).1 (pref (c+1) (by omega)).2 (by omega)]
  rfl


def intSum (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | z+1 => intSum f z + f z

end CriticalConicEvenFinite


namespace CriticalConicEvenFinite
open CriticalConicEvenSparse

def labelCheck (L a k : ℕ) (code : ℕ → ℤ) (root : ℕ → ℕ) (v : ℕ) : Bool :=
  let t := code v
  decide (t.natAbs ≤ k ∧
    (if ¬allowed (L+2) a v then t=0 else
     if ordinary (L+2) a v then t= -code (v-2) else 0<t ∧ root (t.natAbs-1)=v))

def evaluate (L a k : ℕ) (code : ℕ → ℤ) (root row : ℕ → ℕ) (wanted : ℕ → ℤ) : Bool :=
  let pre (i : ℕ) := intSum (fun t => channel L a i t * tagPower (code t))
  allN (labelCheck L a k code root) (L+1) &&
    allN (fun i => let s:=row i;decide (s < L ∧ foldedRow L a code pre s=wanted i)) k

theorem good_of_evaluate {L a k : ℕ} (small : L ≤ 213)
    (code : ℕ → ℤ) (roots rows : ℕ → ℕ) (wanted : ℕ → ℤ) (A : Matrix (Fin k) (Fin k) ℤ)
    (bound : ∀ i j,-512 ≤ A i j ∧ A i j ≤ 512)
    (target : ∀ i : Fin k,wanted i.val=∑ j,A i j*radix^j.val)
    (inj : Function.Injective (A.map (Int.castRingHom ℂ)).mulVec)
    (ok : evaluate L a k code roots rows wanted=true) : Good L a := by
  classical
  let pre (i : ℕ) := intSum (fun t => channel L a i t * tagPower (code t))
  obtain ⟨one,two⟩ := Bool.and_eq_true_iff.mp ok
  have chosen (v : Fin (L+1)) := of_decide_eq_true (allN_true one v.val v.isLt)
  have rowInfo (i : Fin k) : rows i.val < L ∧ foldedRow L a code pre (rows i.val)=wanted i.val :=
    of_decide_eq_true (allN_true two i.val i.isLt)
  let row (i : Fin k) : Fin L := ⟨rows i.val,(rowInfo i).1⟩
  let free (i : Fin k) : Fin (L+1) := Fin.ofNat _ (roots i.val)
  have choices (v : Fin (L+1)) :
      (¬allowed (L+2) a v.val ∧ code v.val=0) ∨
      (∃ i,free i=v ∧ code v.val=(i.val:ℤ)+1) ∨
      (∃ s : Fin L,s.castSucc=v ∧ ordinary (L+2) a s.val ∧ code v.val = -code (previous v).val) := by
    obtain ⟨size,info⟩ := chosen v
    by_cases no : ¬allowed (L+2) a v.val
    · exact Or.inl ⟨no,by simpa [no] using info⟩
    by_cases clean : ordinary (L+2) a v.val
    · have lt : v.val < L := by have := clean.2.1;omega
      exact Or.inr (Or.inr ⟨⟨v.val,lt⟩,rfl,clean,by simpa [no,clean,previous] using info⟩)
    have root : 0 < code v.val ∧ roots ((code v.val).natAbs-1)=v.val := by simpa [no,clean] using info
    let j : Fin k := ⟨(code v.val).natAbs-1,by omega⟩
    refine Or.inr (Or.inl ⟨j,?_,?_⟩)
    · apply Fin.ext
      change roots ((code v.val).natAbs-1)%(L+1)=v.val
      rw [root.2,Nat.mod_eq_of_lt v.isLt]
    · dsimp [j]
      have pos := root.1
      generalize code v.val=z at pos ⊢
      cases z <;> simp_all
  apply good_of_core (fun v => code v.val) free row A choices _ inj
  intro i
  have preSpec : ∀ c < 3, pre c 0=0 ∧ ∀ j < L+1,
      pre c (j+1)=pre c j + channel L a c j*tagPower (code j) := by
    exact fun _ _ => ⟨rfl,fun _ _ => rfl⟩
  exact packed_readback small (fun v => code v.val) (fun v => (chosen v).1) (row i) (A i) (bound i)
    ((foldedRow_eq code pre preSpec (row i)).trans ((rowInfo i).2.trans (target i)))

def readCode (packed v : ℕ) : ℤ :=
  let d := (packed >>> (6*v))%64
  if d%2=0 then ((d/2:ℕ):ℤ) else -((d/2:ℕ):ℤ)

def byte (packed i : ℕ) : ℕ := (packed >>> (8*i))%256

def checkedWords (L a k words roots rows : ℕ) (wanted : ℕ → ℤ) : Bool :=
  evaluate L a k (readCode words) (byte roots) (byte rows) wanted

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite.Catalog

/-- Five-bit table of the core orders in the source catalog. -/
def count (c : Fin 198) : ℕ := (0x210842108420f7c2107ba1084210735f0842107b9cf841ef841ed741f0839f0841cd7be0f6ba0f83dce73e0f739ef7c1ed6bdcf839af7b9f0731ce7bdae7b9ae7bdad6b9ce739ce6b9ee631cd639ad739ae7356d6b1ac6b9ad6b18c6296c6358d62d6c5214a5ad8c5a96a4a1295296a525283a1094a509418e7398e7 >>> (5*c.val)) % 32

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1500000 in
private def coreWords : Array ℕ := #[
  0x1a57e60080200802006fdfb80a319de2396df37fe0488e55866417cdff7fe0784205835f37fdff802107fa0d801ef7be007bd8e3b1577cdf3801f369600,
  0x1f97e60080200802007ee728c65b88e4d81dff7fe238c2198de057fdff801fc7fa0b805ef7be0037d8e4ba018a9f38012369612741f5515b35c5c961e02,
  0x6ae318322383a077be008aa1282a0537e0048d8e51e0148e0055da564dd05c5b361dc97aad2799f27a9f67f1fe,
  0x1a5801b380200802006fe0077a0083a7796d2380145689d79564155e005c5a57eee0b75876cddf725ea7ba8f7e5eb7ddf17e9cd949ea7c9fa7d9fc77a07,
  0x2007e5cf8020080200801ef801db96e4d802007cda57ee00aee006cddf515ea8020d96df97f5ef7f9f38024d7adf7735fa765e081df27e9de7f1e67aa15,
  0x1ef37dcd80200802007cd237ee1284600845df5c5ea6520db76277f5f37f9f582abb885fd7cdfe7d600846037e5d97e9df7f611801fa799fc7a9fe80207,
  0x55dd95c6008020061dea80aa986a8f7d5fe7fe8f85e797d5fe7fe0d80e0b7e5fa7f60080de47a9fc7fa0080207,
  0x695f98020080200802006fdfb80a3188e7081e5b7cdff8122386650816417cdff7fe07816118060d7cdff7fe007fa118060d7cdff7fe007e6117f20d801ef7be00626006b0ec55df37ce00696006fe00,
  0x1f97e6008020080200802007ee028c67788e5b81e4d81dff7fe2395219906058de057fdff802107fa0d8060b805ff7fe007fdfe7f20182e017fdff801ff7e5fc7f20b805ef7be007bd8937dac4ba017f9f3801f3695236fe12811f57d5b3515c95c5f561e02,
  0x7ee3181a239360783a077fe008c2128de0582a057fe007bdfe7fa0180a017fe007bdf97f9fc80a017be0037d8948dac51e017ce0048da555dbf64e04515b35c5c961df57aa02779f2799f67a9fe7f1fe,
  0x189801a58020080200802006ae00832008560783a079ddef801f384a048160a816557be007cdf97e1fc80a01844df80123625456b1cf8061148e0055da55c5bf7ee04c85716cd87725df7d5eab4aa97edeb77df17ddfd7e9fd971e67c9ea7d9fa7f9fc7fa05,
  0x2006cdcf802008020080200801c98021081e0e9de5b802007d5f983a0082a559060080145625ef6b1cf8460d802005c5a57cdbf7ef14b76006cdf5725df7d5ea7ba8f96df97fdfb7f5ff7f9ef9b24d7adfd7c5f77f5fa735e481df27f9f67e9fe7f1de79a15,
  0x1f973df98020080200802007eddd8425e83a5b9360081def625ef801d790637802057cda57cdbf7ee00aee00845f5725df515ea8020d96e0d7fdfb7f5ef7f9f38024d82dff7edfd7bdfe7cdf681e017fdf17ddcd7e9d977e077f9fe7d9fa779fc799ea80201,
  0x73df9626008020080200625ef4e9db9360080231695f348dfb84a0080277515df5c5ea6525b802dd7bdfd7cdfe7d64d806bb7bdfd7cdfe7d6078061176df7765fa77e00805fc779fa799fc7aa0080225,
  0x7bd237360080200802007cd577ed8280200c861177d877aa02b7600aa6277f5f57f9ffaee01a3e217f5f57f9ff84601836037f5f57f9ff802017f2037e5df7e9fd8020076a007e9ea7f1fe8020077a07,
  0x171765f380200802007d5ea80aa9a3e27835ff7f9ffa3e798820b7fdfe7fe0d82e02805ff7f9ff801fe80a0184dfa7f60076600781fe7f1fe801e67f9ed,
  0x695f98020080200802006fdfb80a3188e778025b7cdff8122386655802417cdff7fe07816108020d7cdff7fe007fa108020d7cdff7fe007e6108160d801ef7be00625ef914ec55df37ce00695f38d200,
  0x1f97e6008020080200802007ee028c6239c25b8024d81dff7fe2386651906008de057fdff801fe8460d8020b805ff7fe007e6118360582e017fdff801f9801fc8160b805ef7be006260037e454ba017f9f3801a5801238d212811f57d5b3725505c60061e02,
  0x1fb8c67288e5b9360083a077fe0095212906378020a815ff801ff7f9fc82e0080a017fe007fdf97f20b81602805ff801ff7e5ef7fa0580a017be007bd8937d2391547805f3801f36952355e3464e047d5b3515c95c587801ea809fe7c9de7d9e67aa007f1fe,
  0x7e600626008020080200802007ee0081a00936158020e81e077fe007be128aa0f8020a816057fe007bdf97fa0381602806017fe007bdf97cdf881602806017be0037d8948d45915cf806017ce0048da555d718d1fb81211515b35c5c961ddf801ea80add73deb765f177df7801fa7f6b8779f2799f67a9fa801fc7fa31,
  0x801a573e00802008020080200801bf801d08560083a079de00801f37e5fa83e0582a0595600801f37e5f580a0580a018460080123625457be4573e018460080157695717ce347ee04c86006cd87725f577e007aad2aa65b7e5f57edff7f6007f9ff9fa4d7addf7c5fd7de007e9fd76a077c9ea7d9fe7ea007f1fe77a15,
  0x1b373df980200802008020080200725dd809ee8560783a7796e00935f57e5ff8020e8160a95641802377d5f97fdfb80a0080a118360082d45625ef6adef7c1cf8460d8020b5c5a57cdbf7cdf37ef14b7600aedf5725f57d5df7d5ea7ba8f96e0d7fdfb7fdff7f5ff7f9ef9b24d82dff7edff7fdfd7fdfe7bdfe81e0184df17f5fd7ddfd7e9cd76607781fe7d9fe7f9fa7f9fc779e6801ed,
  0x73df977600802008020080200775fb7ba109de0e96e006ea317e5ff7ee0e9520a9060073a23625ef6adef801cf836007da07695f36fdf37cdfb8020055a77725f57d5df515ea8025b802417edff7fdfd7bdfe7ce4d82e377edff7fdfd7bdfe7ce0782e057fdfd7f5f7735fa7660087df07d9fe7f9fa779fc79a0085201,
  0x7e5dd7e6008020080200802007ede78420683a4d802008c6077bdab7bd2075e378020088e057cdbf7cd237ee12802009de117d54577d717a99496e009060d7fdef7f5f37f9f5936018de0b7fdef7f5f37f9f581e01816017fdef7f5f37f9f5802017fa017fdcd7ddd97e9df802007c1fe7f9de7e9e67f1ea802007ca01,
  0x1897e5a580200802008020037def5c1db81e008c6079dd237cd577ed8280277847215c5df61dea80a5bb760daa5f37f5f57f9ff936bb82a8f7cdfd7d5fe7fe0784600835f37f5f57f9ff8020a8020d7edf777dfa7f6007adfe769e67e9ea7f1fe801f27fa05,
  0x1ef515cd8020080200802007cd717ee0480321846dd845df7d5ea80addaa60da3e277f5ff7f9ffaee8f82a79885fd7fdfe7fe118360082e037f5ff7f9ff801fc8020b80dfd7fdfe7fe007be007fa037e5fd7e9fd801cd7f5e4801fa7f9fc7fa00779fe79a07,
  0x7cdd97ce0080200802007d5ea80aa9a3e0d86a0d7fdfe7fe8f9e60b85e0b7fdfe7fe0d82e0180e017fdfe7fe007fa0180e017fdfe7fe007cdf680e017fdfa7f600765df80dfe7f9fc7fa00799ea80201,
  0x1f97e6008020080200802007ee028c6239de5b81e4d81dff7fe2386654906058de057fdff801fe8420d8060b805ff7fe007e610835fc82e017fdff801f97fdfc7f20b805ef7be00625ef37dac4ba017f9f3801a57cd236fe12811f57d5b3725455c5f561e02,
  0x7ee3180a239de5b9360783a077fe0081212956418de0582a057fe007fdfe8420d82e0180a017fe007fdf98420d82dfc80a017fe007fdf97fdfc82dfc80a017fe007fdf97fdef7f9fc80a017be007bd897bcdf48dac51e017ce007cda57cd2355dbf64e047d5b37d5c95157161df57aa027f9f27f9f6779e67a9fe7f1fe,
  0x1f9801f9802008020080200802007ee009ca0096e4d8560783a0781dff801ff84a308de0f8160a816057fe007fdf97f20b80dfc80a01805ff801ff7e5ef7fa037f202806017fe007fdf97bdf37e1fc80a01805ef801ef624df48d456b1cf806017ce007cda548d575c5bf7ee04845f56cd457257161ddf7d5ea80a0d7fdeb735f1765df7ddfd7e9fd821fe7c9de7d9e67a9fa7f9fc7fa01,
  0x8018973e00802008020080200801ab8020c83a0783a0781e00801ef7e62a82a0082a0581600801ef7e5f3835fc80a0180600800df62523aa9ac73e01806008012369557a09bf7ee04846006cd71725877a9f57aa02b765b7e5f37edf57f9ff7f9ffaea4d7add97c5df7e9fd7e9fd83a077c9e67d9ea7f1fe7f1fe7fa15,
  0x1a573db3802008020080200802006fddd741ee83a0083a079de0096df37e5f58020b8020a81655802417cdf97d5fb80e0180a018460083523625456ae00805cf806118020d55da55c5bf802007ee04c8600b7587725f57d5ea801eab4aa996e8f7d5fb7fdff7fa007f9ff9fa4d9e5f57edff7fdfe801fe7fdfc81e0b7e5f17f5fd7ea007e9fd73607791ea7d9fe7f9fc801fc7f9de80207,
  0x73df97760080200802008020080200775fb7ba028560083a7796e00936317e5ff7ee0483e0182a55906008de237e5ff7edff80a0180a118360082e07625ef6adef7be0173e118360082e07695f36fdf37ce007ef14b7600aee77725f57d5f577e007a9eea3e5b836417edff7fdff7f6007f9ef9b24d82e377edff7fdff7f6007f9ef7fa07806057edff7fdff7f6007f9ef7ce077da057fdfd7f5fd7de007e9cd76600781f07d9fe7f9fe7ea007f1de79a007aa01,
  0x7e5dd7e600802008020080200802007ede780a028567783a5b801ba8c6077fdfb7fe0483a5582a41801ce88e057fdfb7fdff80a1080a0d801f681e017bdab7bdef7be0073e0d801f681e017cdbf7cdf37cdf37ee00801569de117d5f57d5f577d457aa0096e009060d7fdff7fdff7f5ef7f9f39360b8de0b7fdff7fdff7f5ef7f9f381e0b816017fdff7fdff7f5ef7f9f38020b7fa017fdfd7f5fd7ddcd7e9d98021e7c1fe7f9fe7f9fe7e9de7f1e6802147ca01,
  0x1dd7e5f98020080200802008020079dfb9ca1096e0e936008c60788dfb7fdff83a3082a3780223816196adef7bdef3b1cf82e0081e01815bf7cdf37cd237ee1280277846557d5f5515df5c5ea6525b9060d835ff7fdef7f5f37f9f59363782a0b7fdff7bdfd7cdfe7d60781600805ff7fdef7f5f37f9f5801fe8020181dfd735f7765fa77e007adfe7c9fe7f9de7e9e67f1ea801f27f9f9,
  0x1f9625f9802008020080200802007edab8420c83a078023181e2381def37def569d78160088e05866057cd237cd577ed828027784655845f55c5df61dea80a5b9060db760d7fdf37f5f57f9ff9363782abb82dff7cdfd7d5fe7fe0781600846017fdf37f5f57f9ff801fe80211805ff7cdfd7d5fe7fe007e600832017fdd97dddf7e9fd801eb7f6027f9fe799fa7a9fc7fa007c9fe7da01,
  0x695f96ce0080200802008020048def531db81e008c6778025b55df35c5fb812009df21802dd61ddf7d5ea80a5bb76a98028f7d5fd7fdfe7fe4daee8f806797d5fd7fdfe7fe078460d8060b7d5fd7fdfe7fe0082a0d8060b7d5fd7fdfe7fe007e5fc8060b7e5f77f5fa7f6007adcd805e47a9fa7f9fc7fa007c9de80207,
  0x7bdef736008020080200802007cdf37ee0480321b7600aee1177df57aa02b76a9a3e00836277f5ff7f9ffaee8f9e60182e217f5ff7f9ff8460d82e01806037f5ff7f9ff801fc82e01806037f5ff7f9ff801ef7fa01806037f5ff7f9ff801ef7ce017da037e5fd7e9fd801cd76600782007e9fe7f1fe801de79a007aa07,
  0x7cdd97ce0080200802007d5ea80aa9a3e0089e0d7fdfe7fe8f9e6008820b7fdfe7fe0d82e0080a017fdfe7fe007fa0080a017fdfe7fe007ce0b80a017fdfa7f6007661e801fe7f9fc7fa0079a147fa01,
  0x7ee3180a239c25b9360083a077fe0081212942418de0082a057fe007fdfe8460d82e0080a017fe007fdf98460d82e0580a017fe007fdf9801fc82e0580a017fe007fdf9801ef7fa0580a017be007bd89800df48e4551e017ce007cda58012355e3464e047d5b37d5c95417161e007aa027f9f27f9f6781e67aa007f1fe,
  0x7e6007e600802008020080200802007ee0080a009de5b936158020e81e077fe007fe12952418de0f8020a816057fe007fdf98420d82e0381602806017fe007fdf97fdfc82e0381602806017fe007fdf97fdef7fa0381602806017fe007fdf97fdef7cdf881602806017be007bd897bcdf48d45915cf806017ce007cda57cd2355d718d1fb812117d5b37d5c95157161ddf801ea80a0d7fdeb7f5f1735d977df7801fa7f6087f9f27f9f6779e67a9fa801fc7fa01,
  0x2007e5cf80200802008020080200801fb802069360e8020e81e07802007fdf98c23782a0582a0581600801ff7e5ef7fa028160280601802007fdf97bdf38360580a0180600801ef624df48eaa915cf80601802007cda548d57a0a347ee04846006cd457257161dea801ea80a0d96df97bdfb7cdf57fa007f9ff82a4d7adcd7c5d977dfa801fa7f5fe81df2779f6799ea7f2007f1fe7fa15,
  0x18973da5802008020080200802006addd831ee8560783a0781e009ddef7e5f3802048160a81605802557bdf97cdfb7e20080a0180600844df625236ad457c1cf806018021148da555dbf5c5f37ee0484600c8571725877d5df7d5ea80add96ea97cdfb7d5ff7f5ff7f9ffaea4da3df37edf57fdfd7fdfe7fe1081e0d7edf177dfd7ddfd7e9fd7f607769e67d9ea7f9fa7f9fc7f9fe80205,
  0x73db37760080200802008020080200775c97ba0283a0783a079de0096e317e5f57ee0482a0482a0595600906237e5f57edff80e0080a018460083607625456adef801f073e018460083607695716fdf3801f37ee04c8600b7677725f57d5f57a9f57aad2aa65ba3e417edff7fdff7f9ff7f9ff9fa4d9e6377edff7fdff7f9ff7f9ff7f20782e057edff7fdff7f9ff7f9ff7be077fa057fdfd7f5fd7e9fd7e9fd73600791f07d9fe7f9fe7f1fe7f1fe77a0079a01,
  0x1f9775f980200802008020080200802007ede780a0283a0083a7796e009363181dff7edff8120b8020a956418023788e057fdfb7fdff80e0180a118360082e07805ef6adef7be00805cf8460d8020b81e017cdbf7cdf3802007ef14b7600aee77845f57d5f57d5ea801ea7ba8f96e0d9060d7fdff7fdff7fa007f9ef9b24d82e3782dff7fdff7fdfe801fe7bdfe81e01816017fdff7fdff7fa007f9ef7ce077da05805ff7fdff7fdfe801fe7bdf3801f67fa017fdfd7f5fd7ea007e9cd7660077df07f9fe7f9fe7f9fc801fc779e6801ea7ca01,
  0x775f97e6008020080200802008020079dfb80a028567083a5b80231936237edff7fe0483e5182a41802238de197edff7fdff80a1180a0d8020782e056adef7bdef7be1173e0d8020782e056fdf37cdf37ce007ee0080277aee557d5f57d5f577d507aa0096e418360d7fdff7fdff7f5f07f9f3936378020b7fdff7fdff7f5f07f9f381e057da017fdff7fdff7f5f07f9f3801fe7da0181dfd7f5fd7ddd07e9d9801eb781f27f9fe7f9fe7e9e07f1e6801f27a9f9,
  0x1f97e5f980200802008020080200802007edfb80a728565b83a4d8023181e2381dff7fdff9520e9060a8de0088e05866057fdff7fdff809fc80a0b8020780605805ef7bdef7bdef3b1cf82e0081e01816017cdf37cdf37cd237ee128027784655845f57d5f5515df5c5ea6525b9060d8360d7fdff7fdef7f5f37f9f59363782a0b82dff7fdff7bdfd7cdfe7d60781600806017fdff7fdef7f5f37f9f5801fe80201805ff7fdff7bdfd7cdfe7d6007e6007f2017fdfd7f5cd7ddd97e9df801eb7f5f27f9fe7f9fe779fa799fc7aa007c9fe7da01,
  0x7e5f962600802008020080200802007edfb81a109360e81e008c623802077fdff7be0e8aa0a8160088e19802057bdef37def4b9cf8060081e05802017cdf348df355dfb60a009de5580211515f55c5df61dea80a5b9060d802dd7bdff7cdfd7d5fe7fe4d8de0b806bb7bdff7cdfd7d5fe7fe0781601806117bdff7cdfd7d5fe7fe007fa01806117bdff7cdfd7d5fe7fe007e5fc8061173dfd765f777dfa7f6007adf18060e779fe799fa7a9fc7fa007c9f680231,
  0x7e5a57e600802008020080200802007edbf841d083a078023188e009de077bd237bd4a75e058022386600956057cd577cd717ee048027795600c86117d58777df57aa0296e41b7600aa60d7fdf57f5ff7f9ff93637aee01a3e0b7fdf57f5ff7f9ff81e0584601836017fdf57f5ff7f9ff801fe84601836017fdf57f5ff7f9ff801f983201836017fdf57f5ff7f9ff801f97ee017f2017fddf7ddfd7e9fd801eb7c600769fe7f9ea7e9fe7f1fe801f27da0077a01,
  0x1b37e5f980200802008020080200515ef7d9db81e008c67796e07935717cdf37ee0480277c86dd846bb7d5df7d5ea80a5bb76a9a3e0d835ff7f5ff7f9ff936bba3e7982a0b7fdfd7fdfe7fe078460d82e00805ff7f5ff7f9ff8020a8360b802017fdfd7fdfe7fe007e5fc82e00805ff7f5ff7f9ff801f97bdfe8020184df77f5fa7f6007adcd765fe781fe7e9fe7f1fe801f2779e67f9ed,
  0x7bdef736008020080200802007cdf37ee0480321b761155a1177df57aa02b76a9a3e0d802277f5ff7f9ffaee8f9e60a802217f5ff7f9ff8460d82e00802037f5ff7f9ff801fc82e00802037f5ff7f9ff801ef7fa00802037f5ff7f9ff801ef7ce0082e037e5fd7e9fd801cd765fd87e007e9fe7f1fe801de799fe85207,
  0x7e6007e600802008020080200802007ee0080a009c25b9361581e0e81e077fe007fe12946418de0f8160a816057fe007fdf98460d82e037f202806017fe007fdf9801fc82e037f202806017fe007fdf9801ef7fa037f202806017fe007fdf9801ef7cdf87f202806017be007bd89800df48d456b1cf806017ce007cda58012355d716fdfb812117d5b37d5c95417161ddf7d5ea80a0d7fdeb7f5f1741d977df77f5fa7f6087f9f27f9f6781e67a9fa7f9fc7fa01,
  0x801f973e0080200802008020080200801fb8027296e4d83a0783a0781e00801ff7e6549063782a0082a0581600801ff7e5ff7f20b809fc80a0180600801ff7e5ff7bdfe809fc80a0180600801ff7e5ff7bdf3835fc80a0180600801ef625ef37d23aa9ac73e0180600801f3695f348d57a09bf7ee04846006cdf5725455c5877a9f57aa028365b7e5ff7edef7cdf57f9ff7f9ff82a4d7adfd7c5cd765df7e9fd7e9fd7fa077c9fe7d9de799ea7f1fe7f1fe7fa15,
  0x7e5cf62600802008020080200802007eddd819ee936158020e81e07802077fdf97be008aa0f8020a81605802057fdf97bdfb7fa038060280601802017fdf97bdfb7cdf88060280601802017bd8937dab48d45805cf80601802017cda548dbf55d71801fb8121180211515c95c5f561ddf801ea80a0d96edd7bdfb7cdff7d5fd801fe7fe0a936bb7bdfb7cdff7d5fd801fe7fe0081e1173df1765fd77df7801fa7f5fd81e0e779f6799fe7a9fa801fc7f9fe80231,
  0x73da57760080200802008020080200775bf7b9d08560083a0781e009de317e5f37edfa83e0182a0581600956237e5f37edf580a0180a018060084607625236ad457be0173e018060084607695576fd717ce007ee0484600c8677725877d5f577e007aa02b765baa6417edf57fdff7f6007f9ffaea4da3e377edf57fdff7f6007f9ff84207836057edf57fdff7f6007f9ff7fe077f2057fddf7f5fd7de007e9fd7f600769f07d9ea7f9fe7ea007f1fe7fa0077a01,
  0x1b3775f98020080200802008020080200725e780a028560783a079de0096e31935f57edff8120e8160a816558024188e377d5fb7fdff80a0080a01846008360782d456adef7bdef7c1cf806118020d81e0b5c5bf7cdf37cdf37ee04c8600b7677aedf57d5f57d5df7d5eab4aa996e8f9060d7fdff7fdff7f5ff7f9ff9fa4d9e63782dff7fdff7fdfd7fdfe7fdfc81e0b816017fdff7fdff7f5ff7f9ff7be077fa05805ff7fdff7fdfd7fdfe7fdef801fe7fa0184dfd7f5fd7ddfd7e9fd73600765f0781fe7f9fe7f9fa7f9fc7f9de801e67c9ed,
  0x1dd7e5f9802008020080200802008020079dfb80a0283a0783a7796e008c5ba88dfb7fdff8120a8120a956418022373a197edff7fdff80e0080a118360081df6815ab7bdef7be007c1cf8460d802077da056fdf37cdf3801f37ef14b76009dd56955f57d5f57d5ea7d5ea7ba8f96e418020d7fdff7fdff7f9ff7f9ef9b24d8de0082dff7fdff7fdfe7fdfe7bdfe81e05802017fdff7fdff7f9ff7f9ef7ce078160b805ff7fdff7fdfe7fdfe7bdf3801fe82e0181dfd7f5fd7e9fd7e9cd766007ae1f7c9fe7f9fe7f9fc7f9fc779e6801f2851f9,
  0x1f97e5f980200802008020080200802007edfb80a0283a7083a5b802319362381dff7fdff8120b9420a9060088e37866057fdff7fdff80e1180a0d8020782e05805ef7bdef7be00845cf8360081e0b816017cdf37cdf3802007ee0080277aee55845f57d5f57d5ea541ea8025b9060d8360d7fdff7fdff7f9f07f9f3936378020b82dff7fdff7fdfe7c1fe7ce07815f6806017fdff7fdff7f9f07f9f3801fe7da01805ff7fdff7fdfe7c1fe7ce007e5f67f2017fdfd7f5fd7e9d07e9d9801eb77df27f9fe7f9fe7f9fc781fc79a007c9ea7da01,
  0x7e5f97e60080200802008020080200802007edfb80a029de1596e0e936008c623802077fdff7fe049520f9060a8de0088e19802057fdff7fdff842028360282e0081e05802017fdff7fdff7fe027f20282e0081e05802017bdef7bdef7bdef3b1cf82e0081e05802017cdf37cdf37cdf348dfb84a009de55802117d5f57d5f5515df5c5ea6525b9060d8020d7fdff7fdff7bdfd7cdfe7d64d8de0b8060b7fdff7fdff7bdfd7cdfe7d60781601806017fdff7fdff7bdfd7cdfe7d6007fa01806017fdff7fdff7bdfd7cdfe7d6007e5fc806017fdfd7f5fd735f7765fa77e007adf1805fe7f9fe7f9fe779fa799fc7aa007c9f680201,
  0x1f97e5f980200802008020080200802007edfb80a068564d83a0780231801e481dff7fdff8c20e8de0a8160088e007b2057fdff7fdef809fe80a0180207801fc805ef7bdef37def4b9cf8060081e007f2017cdf37cd237cd577ed8280277801bc845f5515f55c5df61dea80a5b906008020d7fdef7fdf37f5f57f9ff936378060082dff7bdff7cdfd7d5fe7fe0781601802017fdef7fdf37f5f57f9ff801fe80600805ff7bdff7cdfd7d5fe7fe007e601816017fdcd7f5d97dddf7e9fd801eb8020d7f9fe779fe799fa7a9fc7fa007ca0082201,
  0x625f969600802008020080200802006adfb8321081e0e81e008c5e481e777bdff7ce0e7ea0a8160088dec8165537def48def519cf8060081dfc8061148df355df35c5fb812009ddbc847215c5f561ddf7d5ea80a5b906d0836a97cdff7d5fd7fdfe7fe4d8deb082a8f7cdff7d5fd7fdfe7fe07816108020d7cdff7d5fd7fdfe7fe007fa108020d7cdff7d5fd7fdfe7fe007e6158020d7edfd77df77f5fa7f6007ae0c7f9da799fe7a9fa7f9fc7fa007ca087fa05,
  0x1f96cdf980200802008020080200802007edc98420283a078023188e7781e5b81def515ef7d1d78160088e1995605906057cd717cdf37ee048027795721846dd845f57d5df7d5ea80a5b906ddaa60da3e0d7fdff7f5ff7f9ff93637aee8f82a7982dff7fdfd7fdfe7fe07816118360082e017fdff7f5ff7f9ff801fe8460d8020b805ff7fdfd7fdfe7fe007e60c8360082e017fdff7f5ff7f9ff801f97edfc8020b805ff7fdfd7fdfe7fe007e5fb7be007fa017fdfd7ddfd7e9fd801eb7c5cd7f5e47f9fe7f9fa7f9fc7fa007c9f6779fe79a01,
  0x7e5f97e600802008020080200802007bdef7d9db81e008c67796e4d802077cdf37cdfb812009df21b76bb802117d5df7d5ea80a5bb76a9a3e0d8020d7fdfd7fdfe7fe4daee8f9e60b8060b7fdfd7fdfe7fe078460d82e01806017fdfd7fdfe7fe0082a0d82e01806017fdfd7fdfe7fe007e5fc82e01806017fdfd7fdfe7fe007e5ef7fa01806017fdfd7fdfe7fe007e5ef7cdf6806017fdf77f5fa7f6007adcd765df805fe7f9fa7f9fc7fa007c9de799ea80201,
  0x2007e5cf8020080200802008020080200801fb802029de5b9360e8020e81e07802007fdf9812559063782a0582a0581600801ff7e5ff8420d82e028160280601802007fdf97fdff7f20b80a0580a0180600801ff7e5ff7fdef7fa028160280601802007fdf97fdff7bdf38360580a0180600801ef625ef7bcdf48eaa915cf80601802007cda57cdf348d57a0a347ee04846006cdf5725f55157161dea801ea80a0d96df97fdfb7fdef7cdf57fa007f9ff82a4d7adfd7c5fd735d977dfa801fa7f5fe81df27f9f67f9de799ea7f2007f1fe7fa15,
  0x1f973df980200802008020080200802007eddd9c9ee96e4d8560783a0781e0081dff7e5ff802308de0f8160a81605802057fdf97fdfb7f20b80e0080a0180600805ff7e5ff7edef7fa038020280601802017fdf97fdfb7bdf37e20080a0180600805ef625ef6acdf48d457c1cf80601802017cda57cdbf48d575c5f37ee0484600845f5725457d57161ddf7d5ea80a0d96e0d7fdfb7bdff7cdf57f5ff7f9ff82a4d82dff7edef7fdf37d5fd7fdfe7fe0081e017fdf1735fd765df7ddfd7e9fd7f6077f9fe7d9de7f9e67a9fa7f9fc7f9fe80201,
  0x1cf625dd80200802008020080200775ab7ba0c83a0783a07802008c5f97bdfb8aa0a8120a81600802237e5ef7edf38360080a018020081d8937dab48eaa7c1cf8060080207695236fd57a09f37ee04802009ddc95c5f561dea7d5ea80a5bb42417edf37fdf57f9ff7f9ff936b18ddfb7cdff7d5fe7fdfe7fe07846057fdd97f5df7e9fd7e9fd802117c1f6799fe7a9fc7f9fc7fa0080201,
  0x1a5775b380200802008020080200802006fde77420283a0083a0781e009de3196df37edf58120b8020a816058025588e417cdfb7d5ff80e0180a018060084607835236ad457be00805cf806018021181e0d55dbf5c5f3802007ee0484600c8677b75877d5f57d5ea801ea80add96ea99068f7d5ff7fdff7fa007f9ffaea4da3e379e5f57fdff7fdfe801fe7fe1081e0d8160b7d5ff7fdff7fa007f9ff7fe077f20582df57fdff7fdfe801fe7fdff801fc7fa0b7e5fd7f5fd7ea007e9fd7f600735f0791ea7f9fe7f9fc801fc7f9fe801de7ca07,
  0x775f97e600802008020080200802008020079dfb80a028560083a079de0096e31936237edff7fe0483e0182a0595600906238de197edff7fdff80a0180a01846008360782e056adef7bdef7be0173e01846008360782e056fdf37cdf37ce007ee04c8600b7677aee557d5f57d5f577e007aad2aa65ba3e418360d7fdff7fdff7f6007f9ff9fa4d9e63782e0b7fdff7fdff7f6007f9ff7f20782e05806017fdff7fdff7f6007f9ff7be077fa05806017fdff7fdff7f6007f9ff7be007f9fe806017fdff7fdff7f6007f9ff7be007cdfe7da0181dfd7f5fd7de007e9fd73600765eb781f27f9fe7f9fe7ea007f1fe77a00799f27a9f9,
  0x7e5f97e60080200802008020080200802007edfb80a028560783a7796e008c5ba88e077fdff7fe0483a0582a559060088dce866057fdff7fdff80a0080a118360081df6816017bdef7bdef7bdf073e118360081df6816017cdf37cdf37cdf37ef14b76009dd56956117d5f57d5f577df57a9eea3e5b906008360d7fdff7fdff7f5ff7f9ef9b24d8de0082e0b7fdff7fdff7f5ff7f9ef7fa0781600806017fdff7fdff7f5ff7f9ef7ce078160b806017fdff7fdff7f5ff7f9ef7ce007fa0b806017fdff7fdff7f5ff7f9ef7ce007e60b7f2017fdfd7f5fd7ddfd7e9cd766007ae1e7c9fe7f9fe7f9fe7e9fe7f1de79a007ca147da01,
  0x1f97e5f980200802008020080200802007edfb80a0283a7783a5b8023188dba81dff7fdff8120a9520a9060088e1973a057fdff7fdff80e1080a0d80207815f6805ef7bdef7be00801cf8360081e057da017cdf37cdf3801f37ee008027795556845f57d5f57d5ea515ea8025b9060d8020d7fdff7fdff7f9ef7f9f39363782e0b82dff7fdff7fdfe7bdfe7ce078160182e017fdff7fdff7f9ef7f9f3801fe8060b805ff7fdff7fdfe7bdfe7ce007e5fc82e017fdfd7f5fd7e9cd7e9d9801eb7c61f7f9fe7f9fe7f9fc779fc79a007c9f685201,
  0x7e5f97e60080200802008020080200802007edfb80a029de0e96e0e936008c600792077fdff7fe049560b9060a8de0088e007b2057fdff7fdff842038360282e0081e007f2017fdff7fdff7fe037f20282e0081e007f2017bdef7bdef7be003b1cf82e0081e007f2017cdf37cdf37ce0048dfb84a009de006f2117d5f57d5f5515ea5c5ea6525b906008020d7fdff7fdff7bdfe7cdfe7d64d8de018020b7fdff7fdff7bdfe7cdfe7d60781601802017fdff7fdff7bdfe7cdfe7d6007fa01802017fdff7fdff7bdfe7cdfe7d6007e601816017fdfd7f5fd735fa765fa77e007ae00835fe7f9fe7f9fe779fc799fc7aa007ca0082201,
  0x7e5f97e60080200802008020080200802007edfb9ca0296e159360e81e008c5e481e077fdff7fe048c20f8de0a8160088dec816057fdff7fdff7f20282e028060081dfc806017fdff7fdff7be027fa028060081dfc806017bdef7bdef37def4b9cf8060081dfc806017cdf37cdf348df355dfb60a009ddbc846117d5f5515f55c5df61dea80a5b906008360d7fdff7bdff7cdfd7d5fe7fe4d8de0082a0b7fdff7bdff7cdfd7d5fe7fe0781600802017fdff7bdff7cdfd7d5fe7fe007fa00802017fdff7bdff7cdfd7d5fe7fe007e605802017fdfd735fd765f777dfa7f6007ae0c7f9fe7f9fe779fe799fa7a9fc7fa007ca087fa01,
  0x1f9625f980200802008020080200802007edab80a0c8560783a078023181e2381dff7bdff8aa0e8160a8160088e05866057fdef7fdf3809f680a018020780605805ef37def48def519cf8060081e01816017cd237cd577cd717ee048027784655845f55c5f561ddf7d5ea80a5b9060db760d7fdf37fdf57f5ff7f9ff9363782abb82dff7cdff7d5fd7fdfe7fe0781600846017fdf37fdf57f5ff7f9ff801fe80211805ff7cdff7d5fd7fdfe7fe007e600832017fdd97f5df7ddfd7e9fd801eb7f6027f9fe799fe7a9fa7f9fc7fa007c9fe7da01,
  0x1a57e5b380200802008020080200802006fdfb7421081e0e81e008c5e49de0096df37fdf583a0482a05802237b2558024148def515ef7c1cf8060081dfc84600835577cd717cdf37ee04802776f321802dd61df57d5df7d5ea80a5b906d0aa600a3df57fdff7f5ff7f9ff93637ac28f806797d5ff7fdfd7fdfe7fe07816108360182df57fdff7f5ff7f9ff801fe8420d8060b7d5ff7fdfd7fdfe7fe007e6158360182df57fdff7f5ff7f9ff801f9811fc8060b7e5fd7f5f77f5fa7f6007ae0c73601791ea7f9fe7e9fe7f1fe801f2821de80207,
  0x7e5f97e60080200802008020080200802007edfb8420283a078023188e7796e00936077bdef7bdf475e058022386655906008de057cdf37cdf37ee048027795721b7600aee117d5f577df57aa0296e41b76a9a3e008360d7fdff7f5ff7f9ff93637aee8f9e60182e0b7fdff7f5ff7f9ff81e058460d82e01806017fdff7f5ff7f9ff801fe8460d82e01806017fdff7f5ff7f9ff801f98320d82e01806017fdff7f5ff7f9ff801f97edfc82e01806017fdff7f5ff7f9ff801f97edef7fa01806017fdff7f5ff7f9ff801f97edef7ce017da017fdfd7ddfd7e9fd801eb7c5cd76600781fe7f9fe7e9fe7f1fe801f27d9de79a007aa01,
  0x7e5f97e600802008020080200802007bdef7d9db81e008c67796dba81e077cdf37cdfb812009df21b7556846117d5df7d5ea80a5bb76a9a3e008360d7fdfd7fdfe7fe4daee8f9e60082a0b7fdfd7fdfe7fe078460d82e00802017fdfd7fdfe7fe0082a0d82e00802017fdfd7fdfe7fe007e5fc82e00802017fdfd7fdfe7fe007e5ef7fa00802017fdfd7fdfe7fe007e5ef7ce0b802017fdf77f5fa7f6007adcd7661e7f9fe7f9fa7f9fc7fa007c9de79a147fa01,
  0x2007e5cf8020080200802008020080200801fb802029c25b9360e81e0e81e07802007fdf9812509063782a0082a0581600801ff7e5ff8460d82e027f20280601802007fdf97fe007f20b809fc80a0180600801ff7e5ff801ef7fa027f20280601802007fdf97fe007bdf3835fc80a0180600801ef625ef800df48eaa6b1cf80601802007cda57ce0048d57a09bf7ee04846006cdf5725f55417161dea7d5ea80a0d96df97fdfb7fdf07cdf57f9ff7f9ff82a4d7adfd7c5fd741d977dfa7f5fa7f5fe81df27f9f67f9e0799ea7f1fe7f1fe7fa15,
  0x7e5cf7e60080200802008020080200802007eddd809ee9de5b936158020e81e07802077fdf97fe00952418de0f8020a81605802057fdf97fdfb8420d82e038060280601802017fdf97fdfb7fdfc82e038060280601802017fdf97fdfb7fdef7fa038060280601802017fdf97fdfb7fdef7cdf88060280601802017bd897bdab7bcdf48d45805cf80601802017cda57cdbf7cd2355d71801fb81211802117d5c97d5f55157161ddf801ea80a0d96e0d7fdfb7fdff7bdf37d5fd801fe7fe0a9360b7fdfb7fdff7bdf37d5fd801fe7fe0081e017fdf17f5fd735d977df7801fa7f5fd81dfe7f9f67f9fe779e67a9fa801fc7f9fe80201,
  0x73df97760080200802008020080200775fb7ba069360e8020e81e00802317e5ff7ee308de0a8060a81600802237e5ff7edef7fa028060280600802077e5ff7edef7ce0d806028060080207625ef6acdf48eaa805cf8060080207695f36fd2355e82801fb8120080277725457d57161dea801ea80a5b802417edef7fdf37d5fe801fe7fe4d806377edef7fdf37d5fe801fe7fe07806057fdcd7f5d977dfa801fa7f600805f07d9de7f9e67a9fc801fc7fa0080201,
  0x625dd69600802008020080200802006ade7832028560783a07802008c6777bdfb7ce048120582a058020088e557bdfb7cdff7e20080a018020081e1137dab48def515f073e018020081e1148dbf55df35c5f37ee04802009df215c5f561df577df57aa0296ed0906a97cdff7d5ff7f5ff7f9ff936b18de8f7cdff7d5ff7f5ff7f9ff81e118160d7cdff7d5ff7f5ff7f9ff802117fa0d7edfd77dfd7ddfd7e9fd802007c1da799fe7a9fe7e9fe7f1fe802007ca05,
  0x775b37e600802008020080200802008020079dc980a0283a0783a0781e009de3196e237edf57fe0482a0482a058160095623906197edf57fdff80e0080a018060084607836056ad457bdef801f073e018060084607836056fd717cdf3801f37ee0484600c8677b76557d5f57d5f57a9f57aa02b765baa641a3e0d7fdff7fdff7f9ff7f9ffaea4da3e379e60b7fdff7fdff7f9ff7f9ff842078360582e017fdff7fdff7f9ff7f9ff7fe077f20582e017fdff7fdff7f9ff7f9ff7fe007f1fe82e017fdff7fdff7f9ff7f9ff7fe007bdfe7fa0181dfd7f5fd7e9fd7e9fd7f600735eb791f27f9fe7f9fe7f1fe7f1fe7fa00779f2799f9,
  0x1f97e5f98020080200802008020080200802007edfb80a0283a0083a079de0096e319362381dff7fdff8120b8020a816558024188e37866057fdff7fdff80e0180a01846008360782e05805ef7bdef7be00805cf806118020d81e0b816017cdf37cdf3802007ee04c8600b7677aee55845f57d5f57d5ea801eab4aa996e8f9060d8360d7fdff7fdff7fa007f9ff9fa4d9e63782e0b82dff7fdff7fdfe801fe7fdfc81e0b81601806017fdff7fdff7fa007f9ff7be077fa0580601805ff7fdff7fdfe801fe7fdef801fe7fa01806017fdff7fdff7fa007f9ff7be007cdfe7da01805ff7fdff7fdfe801fe7fdef801f37e5f67f2017fdfd7f5fd7ea007e9fd73600765eb77df27f9fe7f9fe7f9fc801fc7f9de801e67c9ea7da01,
  0x7e5f97e60080200802008020080200802007edfb80a028560083a7796e008c623936077fdff7fe0483e0182a559060088e198de057fdff7fdff80a0180a118360081e0582e017bdef7bdef7be0173e118360081e0582e017cdf37cdf37ce007ef14b76009de55aee117d5f57d5f577e007a9eea3e5b9060d8360d7fdff7fdff7f6007f9ef9b24d8de0b82e0b7fdff7fdff7f6007f9ef7fa0781601806017fdff7fdff7f6007f9ef7ce07816017da017fdff7fdff7f6007f9ef7ce007fa017da017fdff7fdff7f6007f9ef7ce007e5fc7da017fdfd7f5fd7de007e9cd766007adf1781fe7f9fe7f9fe7ea007f1de79a007c9f67aa01,
  0x1f97e5f980200802008020080200802007edfb80a028567783a5b802316e9e481dff7fdff8120e9560a9060088dce7b2057fdff7fdff80a1080a0d802077d9fc805ef7bdef7bdef801cf8360081df67f2017cdf37cdf37cdf37ee0080277559bc845f57d5f57d5df515ea8025b906008020d7fdff7fdff7f5ef7f9f39363782e0082dff7fdff7fdfd7bdfe7ce078160b802017fdff7fdff7f5ef7f9f3801fe82e00805ff7fdff7fdfd7bdfe7ce007e60b816017fdfd7f5fd7ddcd7e9d9801eb87a0d7f9fe7f9fe7f9fa779fc79a007ca1482201,
  0x7e5f97e60080200802008020080200802007edfb80a029c20e96e0e936008c5e481e077fdff7fe049460a9060a8de0088dec816057fdff7fdff846038360282e0081dfc806017fdff7fdff802037f20282e0081dfc806017bdef7bdef802003b1cf82e0081dfc806017cdf37cdf38020048dfb84a009ddbc846117d5f57d5f5541ea5c5ea6525b906008360d7fdff7fdff7c1fe7cdfe7d64d8de0082a0b7fdff7fdff7c1fe7cdfe7d60781600802017fdff7fdff7c1fe7cdfe7d6007fa00802017fdff7fdff7c1fe7cdfe7d6007e605802017fdfd7f5fd741fa765fa77e007ae0c7f9fe7f9fe7f9fe781fc799fc7aa007ca087fa01,
  0x7e5f97e60080200802008020080200802007edfb80a7296e0e9360e81e008c60788e077fdff7fe549060b8de0a8160088e05866057fdff7fdff7f20382e028060081e01816017fdff7fdff7be037fa028060081e01816017bdef7bdef37e004b9cf8060081e01816017cdf37cdf348e0055dfb60a009de11956117d5f57d5455c5ea61dea80a5b9060d8360d7fdff7fdef7cdfe7d5fe7fe4d8de0a82e0b7fdff7fdef7cdfe7d5fe7fe0781600806017fdff7fdef7cdfe7d5fe7fe007fa00806017fdff7fdef7cdfe7d5fe7fe007e6007f2017fdfd7f5cd765fa77dfa7f6007adfd7c9fe7f9fe7f9de799fc7a9fc7fa007c9fe7da01,
  0x7e5f96260080200802008020080200802007edfb81a029361581e0e81e008c623802077fdff7be048aa0f8160a8160088e19802057fdff7bdff7fa02806028060081e05802017fdff7bdff7ce027da028060081e05802017bdef37def48def519cf8060081e05802017cdf348df355df35c5fb812009de5580211515f55c5f561ddf7d5ea80a5b9060d802dd7bdff7cdff7d5fd7fdfe7fe4d8de0b806bb7bdff7cdff7d5fd7fdfe7fe0781601806117bdff7cdff7d5fd7fdfe7fe007fa01806117bdff7cdff7d5fd7fdfe7fe007e5fc8061173dfd765fd77df77f5fa7f6007adf18060e779fe799fe7a9fa7f9fc7fa007c9f680231,
  0x7e5a57e60080200802008020080200802007edbf809d08560783a078023188e009de077fdf37fdfa83a0582a058022386600956057fdf37fdf580a0080a018020781600846017bd237bd457bdf073e018020781600846017cd577cd717cdf37ee048027795600c86117d5877d5f577df57aa0296e41b7600aa60d7fdf57fdff7f5ff7f9ff93637aee01a3e0b7fdf57fdff7f5ff7f9ff81e0584601836017fdf57fdff7f5ff7f9ff801fe84601836017fdf57fdff7f5ff7f9ff801f983201836017fdf57fdff7f5ff7f9ff801f97ee017f2017fddf7f5fd7ddfd7e9fd801eb7c600769fe7f9ea7f9fe7e9fe7f1fe801f27da0077a01,
  0x6cdf97e6008020080200802008020080200725fb80a1081e0e81e008c5e49de5b81e4d7d5ff7fe0e8120a8160088dec9564181637515ef7bdef7c1cf8060081dfc8460d8060b5c5f37cdf37cdfb812009ddbcc86dd846bb7d5f57d5df7d5ea80a5b906d0aa68f8360d7fdff7fdfd7fdfe7fe4d8deb0a3e7982a0b7fdff7fdfd7fdfe7fe07816108360b802017fdff7fdfd7fdfe7fe007fa108360b802017fdff7fdfd7fdfe7fe007e6158360b802017fdff7fdfd7fdfe7fe007e6047f20b802017fdff7fdfd7fdfe7fe007e6047bdfe8020184dfd7f5f77f5fa7f6007ae0c735d97f9e07f9fe7f9fa7f9fc7fa007ca08779e67f9ed,
  0x7e5f97e60080200802008020080200802007edfb8420283a078023188e7796e076ea077bdef7bdf475e0580223866559060573a057cdf37cdf37ee048027795721b761155a117d5f577df57aa0296e41b76a9a3e0d8020d7fdff7f5ff7f9ff93637aee8f9e60a8020b7fdff7f5ff7f9ff81e058460d82e00802017fdff7f5ff7f9ff801fe8460d82e00802017fdff7f5ff7f9ff801f98320d82e00802017fdff7f5ff7f9ff801f97edfc82e00802017fdff7f5ff7f9ff801f97edef7fa00802017fdff7f5ff7f9ff801f97edef7ce0082e017fdfd7ddfd7e9fd801eb7c5cd765fd87dfe7f9fe7e9fe7f1fe801f27d9de799fe85201,
  0x7e5cf7e60080200802008020080200802007eddd809ee9c25b9361581e0e81e07802077fdf97fe00946418de0f8160a81605802057fdf97fdfb8460d82e038020280601802017fdf97fdfb801fc82e038020280601802017fdf97fdfb801ef7fa038020280601802017fdf97fdfb801ef7cdf88020280601802017bd897bdab800df48d457c1cf80601802017cda57cdbf8012355d717cdfb81211802117d5c97d5f55417161ddf7d5ea80a0d96e0d7fdfb7fdff7c1f37d5fd7fdfe7fe0a9360b7fdfb7fdff7c1f37d5fd7fdfe7fe0081e017fdf17f5fd741d977df77f5fa7f5fd81dfe7f9f67f9fe781e67a9fa7f9fc7f9fe80201,
  0x1cf7e5dd8020080200802008020080200775fb7ba7296e4d83a0783a07802008c5f97fdfb952418de0a8120a81600802237e5ff7edff7f20b80a0080a018020081df97fdfb7fdef7fa028020280600802077e5ff7edff7bdf38360080a018020081d897bdab7bcdf48eaa7c1cf8060080207695f36fdf348d57a09f37ee04802009ddc97d5f55157161dea7d5ea80a5b802417edff7fdef7cdf57f9ff7f9ff936018ddfb7fdff7bdf37d5fe7fdfe7fe07806057fdfd7f5cd765df7e9fd7e9fd802017c1f67f9fe779e67a9fc7f9fc7fa0080201,
  0x1f97758980200802008020080200802007ede781a02936158020e81e008023181dff7edef8122a83e0082a058020088e057fdfb7bdff7fa03806028060080207805ff7edef7fdf37e20180a018020081e017bdab37def48d45805cf8060080207805f36fd237cd575c6007ee04802009de11515f55c5f561ddf801ea80a5b80241b75ef7fdf37fdf57f6007f9ff936018debb7bdff7cdff7d5fd801fe7fe0780605845ef7fdf37fdf57f6007f9ff802017fa1173dfd765fd77df7801fa7f600801f0839de7f9e67f9ea7ea007f1fe802007ca31,
  0x1dd695f9802008020080200802008020079dbf809d08560083a07802008c67788dfb7cdff7ea0f8060a8160080223956197edf37fdf580a0180a018020081e11815ab48def515ef805cf8060080207846056fd577cd717ce007ee04802009df21955f561df57d5df801ea80a5bb4241aa60d7fdf57fdff7f6007f9ff936b18de8f82dff7d5ff7fdfd801fe7fe0784605836017fdf57fdff7f6007f9ff802117fa0d805ff7d5ff7fdfd801fe7fe00801fe7f20181ddf7f5fd7de007e9fd802007adda7c9fe7a9fe7f9fa801fc7fa00801f2779f9,
  0x1b37e5f9802008020080200802008020080200725fb80a028560783a0781e009de3196e23935f57fdff8120e8160a816058025588e41866377d5ff7fdff80a0080a0180600846078360582d457bdef7bdef7c1cf806018021181e0d8160b5c5f37cdf37cdf37ee0484600c8677b7655aedf57d5f57d5df7d5ea80add96ea99068f8360d7fdff7fdff7f5ff7f9ffaea4da3e379e60b82dff7fdff7fdfd7fdfe7fe1081e0d8160b806017fdff7fdff7f5ff7f9ff7fe077f20582e01805ff7fdff7fdfd7fdfe7fdff801fc7fa0b806017fdff7fdff7f5ff7f9ff7fe007bdfe7fa01805ff7fdff7fdfd7fdfe7fdff801ef7e5fe7f20184dfd7f5fd7ddfd7e9fd7f600735eb765f2781fe7f9fe7f9fa7f9fc7f9fe801de7c9e67d9ed,
  0x1f97e5f98020080200802008020080200802007edfb80a0283a0783a079de0096e3188dba81dff7fdff8120a8120a816558024188e1973a057fdff7fdff80e0080a018460083607815f6805ef7bdef7be007c1cf806118020d81e057da017cdf37cdf3801f37ee04c8600b767795556845f57d5f57d5ea7d5eab4aa996e8f9060d8020d7fdff7fdff7f9ff7f9ff9fa4d9e63782e0082dff7fdff7fdfe7fdfe7fdfc81e0b81601802017fdff7fdff7f9ff7f9ff7be077fa0580600805ff7fdff7fdfe7fdfe7fdef801fe7fa01802017fdff7fdff7f9ff7f9ff7be007cdfe8060b805ff7fdff7fdfe7fdfe7fdef801f37e5fc82e017fdfd7f5fd7e9fd7e9fd73600765eb7c61f7f9fe7f9fe7f9fc7f9fc7f9de801e67c9f685201,
  0x7e5f97e60080200802008020080200802007edfb80a0283a0083a7796e008c64d792077fdff7fe0482e0082a559060088e377b2057fdff7fdff80e0180a118360081e0b7f2017bdef7bdef8020173e118360081e0b7f2017cdf37cdf3802007ef14b76009debb6f2117d5f57d5f57aa007a9eea3e5b9060d8020d7fdff7fdff7fa007f9ef9b24d8de0b8020b7fdff7fdff7fa007f9ef7fa0781601802017fdff7fdff7fa007f9ef7ce07815f6802017fdff7fdff7fa007f9ef7ce007f9f6802017fdff7fdff7fa007f9ef7ce007e5f6816017fdfd7f5fd7ea007e9cd766007addf835fe7f9fe7f9fe7f2007f1de79a007c9ea82201,
  0x1f97e5f980200802008020080200802007edfb80a028567083a5b802317924d81dff7fdff8120f9460a9060088dec8de057fdff7fdff80a1180a0d802077f20b805ef7bdef7bdef845cf8360081dfc82e017cdf37cdf37ce007ee00802776f2bb845f57d5f57d5df541ea8025b906008360d7fdff7fdff7f5f07f9f3936378020082dff7fdff7fdfd7c1fe7ce07816007da017fdff7fdff7f5f07f9f3801fe801f6805ff7fdff7fdfd7c1fe7ce007e6057da017fdfd7f5fd7ddd07e9d9801eb831e07f9fe7f9fe7f9fa781fc79a007ca087aa01,
  0x7e5f97e60080200802008020080200802007edfb80a029c21596e0e936008c60788e077fdff7fe049420e9060a8de0088e05866057fdff7fdff846028360282e0081e01816017fdff7fdff802027f20282e0081e01816017bdef7bdef801ef3b1cf82e0081e01816017cdf37cdf3801f348dfb84a009de11956117d5f57d5f5541df5c5ea6525b9060d8360d7fdff7fdff7c1fd7cdfe7d64d8de0a82e0b7fdff7fdff7c1fd7cdfe7d60781600806017fdff7fdff7c1fd7cdfe7d6007fa00806017fdff7fdff7c1fd7cdfe7d6007e6007f2017fdfd7f5fd741f7765fa77e007adfd7c9fe7f9fe7f9fe781fa799fc7aa007c9fe7da01,
  0x1f97e5f98020080200802008020080200802007edfb80a029de5b83a4d83a078023188e0081dff7fdff812549060a8de0a8160088e19802057fdff7fdff8420d80e0b80a018020781600805ff7fdff7fdff7f20382e028060081e05802017fdff7fdff7fdef80dfe80a018020781600805ef7bdef7bdef37e004b9cf8060081e05802017cdf37cdf37cd23801577ed828027795600845f57d5f57d5455c5ea61dea80a5b9060d8020d7fdff7fdff7bdf37f9f57f9ff9363782e0182dff7fdff7fdef7cdfe7d5fe7fe0781601806017fdff7fdff7bdf37f9f57f9ff801fe80601805ff7fdff7fdef7cdfe7d5fe7fe007e5fc806017fdfd7f5fd735d97e9df7e9fd801eb7c6017f9fe7f9fe7f9de799fc7a9fc7fa007c9f680201,
  0x7e5f97e60080200802008020080200802007edfb80a069360e81e0e81e008c600792077fdff7fe308de0b8160a8160088e007b2057fdff7fdef7fa03806028060081e007f2017fdff7fdef7ce037da028060081e007f2017bdef7bcdf48e00519cf8060081e007f2017cdf37cd2355e005c5fb812009de006f2117d5457d57161dea7d5ea80a5b906008020d7fdef7fdf37d5fe7fdfe7fe4d8de018020b7fdef7fdf37d5fe7fdfe7fe0781601802017fdef7fdf37d5fe7fdfe7fe007fa01802017fdef7fdf37d5fe7fdfe7fe007e601816017fdcd7f5d977dfa7f5fa7f6007ae00835fe7f9de7f9e67a9fc7f9fc7fa007ca0082201,
  0x1897e5a580200802008020080200802006adfb832028560083a0780231792079ddef7fdf38120f82e0a8160088dec816557bdff7cdff80a0b80a01802077f201844df7bd237bdefaadcf8060081dfc8061148df355df37ce827ee04802776f211c85717d5877d5df801ea80a5b906d0836a97cdff7d5ff7f6007f9ff93637ac20aa3df37fdf57fdfd801fe7fe07816108020d7cdff7d5ff7f6007f9ff801fe84200835f37fdf57fdfd801fe7fe007e6158020d7edfd77dfd7de007e9fd801eb831fe769e67f9ea7f9fa801fc7fa007ca087fa05,
  0x1f96cdf98020080200802008020080200802007edc980a028560783a078023188e7781e5b81dff7d5ff8120e8160a8160088e1995605906057fdf57fdff80a0080a0180207816118060d805ef515ef7bdef7c1cf8060081e0584601836017cd717cdf37cdf37ee048027795721846dd845f57d5f57d5df7d5ea80a5b906ddaa60da3e0d7fdff7fdff7f5ff7f9ff93637aee8f82a7982dff7fdff7fdfd7fdfe7fe07816118360082e017fdff7fdff7f5ff7f9ff801fe8460d8020b805ff7fdff7fdfd7fdfe7fe007e60c8360082e017fdff7fdff7f5ff7f9ff801f97edfc8020b805ff7fdff7fdfd7fdfe7fe007e5fb7be007fa017fdfd7f5fd7ddfd7e9fd801eb7c5cd7f5e47f9fe7f9fe7f9fa7f9fc7fa007c9f6779fe79a01,
  0x1f97e5f98020080200802008020080200802007edfb80a1081e0e81e008c5e49de5b9360081dff7fdff83a0482a05802237b25590637802057bdef7bdef7c1cf8060081dfc8460d82e00805f37cdf37cdf37ee04802776f321b76bb802117d5f57d5df7d5ea80a5b906d0aa68f83600835ff7fdff7f5ff7f9ff93637ac28f9e60b8060b7fdff7fdfd7fdfe7fe07816108360b80601805ff7fdff7f5ff7f9ff801fe8420d82e01806017fdff7fdfd7fdfe7fe007e6158360b80601805ff7fdff7f5ff7f9ff801f9811fc82e01806017fdff7fdfd7fdfe7fe007e6047bdfe80601805ff7fdff7f5ff7f9ff801f9811ef7cdf6806017fdfd7f5f77f5fa7f6007ae0c735d977e017f9fe7f9fe7e9fe7f1fe801f2821de799ea80201,
  0x73df9776008020080200802008020080200775fb7ba029de5b9360e8020e81e00802317e5ff7ee04956418de0a8060a81600802237e5ff7edff8420d82e028060280600802077e5ff7edff7fdfc82e028060280600802077e5ff7edff7fdef7fa028060280600802077e5ff7edff7fdef7ce0d806028060080207625ef6adef7bcdf48eaa805cf8060080207695f36fdf37cd2355e82801fb8120080277725f57d5f55157161dea801ea80a5b802417edff7fdff7bdf37d5fe801fe7fe4d806377edff7fdff7bdf37d5fe801fe7fe07806057fdfd7f5fd735d977dfa801fa7f600805f07d9fe7f9fe779e67a9fc801fc7fa0080201,
  0x7e5dd7e60080200802008020080200802007ede79ca0296e4d8560783a07802008c6077fdfb7fe048c23783e0582a058020088e057fdfb7fdff7f20b80e0080a018020081e017fdfb7fdff7bdfe80e0080a018020081e017fdfb7fdff7bdf37e20080a018020081e017bdab7bdef37d23515f073e018020081e017cdbf7cdf348d575c5f37ee04802009de117d5f5515f55c58777df57aa0296e009060d7fdff7bdff7cdf57f5ff7f9ff936018de0b7fdff7bdff7cdf57f5ff7f9ff81e01816017fdff7bdff7cdf57f5ff7f9ff802017fa017fdfd735fd765df7ddfd7e9fd802007c1fe7f9fe779fe799ea7e9fe7f1fe802007ca01,
  0x775897e6008020080200802008020079dab80a0c83a0783a078023181e237edef7fe2a82a0482a0580223816197edef7fdf38360080a0180207806056acdf7bd23aa9f073e0180207806056fd237cd57a09f37ee0480277846557d5717d5877a9f57aa0296e41b760d7fdf37fdf57f9ff7f9ff93637aea0b7fdf37fdf57f9ff7f9ff81e05842017fdf37fdf57f9ff7f9ff801fe8420181dd97f5df7e9fd7e9fd801eb839f27f9e67f9ea7f1fe7f1fe801f27f9f9,
  0x695f96ce0080200802008020080200802006fdfb7420283a0083a07802008c67788e5b7cdff7d60482e0082a058020088e55866417cdff7d5ff80e0180a018020081e118160d48def515ef8020173e018020081e118160d55df35c5f3802007ee04802009df21956dd61df57d5f57aa007aa0296ed0906a98368f7d5ff7fdff7fa007f9ff936b18de8f82e797d5ff7fdff7fa007f9ff81e118160d8060b7d5ff7fdff7fa007f9ff802117fa0d8060b7d5ff7fdff7fa007f9ff802007f9fc8060b7d5ff7fdff7fa007f9ff802007e5fc7f20b7e5fd7f5fd7ea007e9fd802007adcd7c9e47a9fe7f9fe7f2007f1fe802007c9de7da07,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560083a0781e009de3196e23936077fdff7fe0483e0182a058160095623906198de057fdff7fdff80a0180a0180600846078360582e017bdef7bdef7be0173e0180600846078360582e017cdf37cdf37ce007ee0484600c8677b7655aee117d5f57d5f577e007aa02b765baa641a3e0d8360d7fdff7fdff7f6007f9ffaea4da3e379e60b82e0b7fdff7fdff7f6007f9ff842078360582e01806017fdff7fdff7f6007f9ff7fe077f20582e01806017fdff7fdff7f6007f9ff7fe007f1fe82e01806017fdff7fdff7f6007f9ff7fe007bdfe7fa01806017fdff7fdff7f6007f9ff7fe007bdf97f9fc806017fdff7fdff7f6007f9ff7fe007bdf97cdfc7da017fdfd7f5fd7de007e9fd7f600735eb765f1781fe7f9fe7f9fe7ea007f1fe7fa00779f2799f67aa01,
  0x1f97e5f98020080200802008020080200802007edfb80a028560783a079de0096e316e9e481dff7fdff8120e8160a816558024188dce7b2057fdff7fdff80a0080a0184600836077d9fc805ef7bdef7bdef7c1cf806118020d81df67f2017cdf37cdf37cdf37ee04c8600b7677559bc845f57d5f57d5df7d5eab4aa996e8f906008020d7fdff7fdff7f5ff7f9ff9fa4d9e6378020082dff7fdff7fdfd7fdfe7fdfc81e0b81600802017fdff7fdff7f5ff7f9ff7be077fa0580200805ff7fdff7fdfd7fdfe7fdef801fe7fa00802017fdff7fdff7f5ff7f9ff7be007cdfe82e00805ff7fdff7fdfd7fdfe7fdef801f37e60b816017fdfd7f5fd7ddfd7e9fd73600765eb87a0d7f9fe7f9fe7f9fa7f9fc7f9de801e67ca1482201,
  0x7e5f97e60080200802008020080200802007edfb80a0283a0783a7796e008c5e46ea077fdff7fe0482a0482a559060088dec73a057fdff7fdff80e0080a118360081dfc7da017bdef7bdef801f073e118360081dfc7da017cdf37cdf3801f37ef14b76009ddbc55a117d5f57d5f57a9f57a9eea3e5b906008020d7fdff7fdff7f9ff7f9ef9b24d8de008020b7fdff7fdff7f9ff7f9ef7fa0781600802017fdff7fdff7f9ff7f9ef7ce078160082e017fdff7fdff7f9ff7f9ef7ce007fa0082e017fdff7fdff7f9ff7f9ef7ce007e60582e017fdfd7f5fd7e9fd7e9cd766007ae0c87dfe7f9fe7f9fe7f1fe7f1de79a007ca0885201,
  0x1f97e5f98020080200802008020080200802007edfb80a029de5b8564d83a0780231801e481dff7fdff812559060e8de0a8160088e007b2057fdff7fdff8420d80a0b80a0180207801fc805ff7fdff7fdff7f20282e028060081e007f2017fdff7fdff7fdef809fe80a0180207801fc805ef7bdef7bdef37def4b9cf8060081e007f2017cdf37cdf37cd237cd577ed8280277801bc845f57d5f57d5455c5df61dea80a5b906008020d7fdff7fdff7bdf37f5f57f9ff936378060082dff7fdff7fdef7cdfd7d5fe7fe0781601802017fdff7fdff7bdf37f5f57f9ff801fe80600805ff7fdff7fdef7cdfd7d5fe7fe007e601816017fdfd7f5fd735d97dddf7e9fd801eb8020d7f9fe7f9fe7f9de799fa7a9fc7fa007ca0082201,
  0x1f97e5f98020080200802008020080200802007edfb9ca0296e4d83a0783a07802317920781dff7fdff812308de0a8160a8160088dec816057fdff7fdff7f20b80e0180a01802077f201805ff7fdff7fdef7fa03806028060081dfc806017fdff7fdff7bdf380df680a01802077f201805ef7bdef7bcdf48e00519cf8060081dfc806017cdf37cdf348d57801717ee04802776f211845f57d5457d57161dea7d5ea80a5b906008360d7fdff7bdff7cdf57f9ff7f9ff936378020a82dff7fdef7fdf37d5fe7fdfe7fe0781600802017fdff7bdff7cdf57f9ff7f9ff801fe80200805ff7fdef7fdf37d5fe7fdfe7fe007e605802017fdfd735fd765df7e9fd7e9fd801eb831fe7f9fe7f9de7f9e67a9fc7f9fc7fa007ca087fa01,
  0x1f9625f980200802008020080200802007edab80a0c83a0083a078023181e2381dff7bdff8aa0b8020a8160088e05866057fdef7fdf380e0b80a018020780605805ef37def48e00aadcf8060081e01816017cd237cd57802827ee048027784655845f55c5f561dea801ea80a5b9060db760d7fdf37fdf57fa007f9ff9363782abb82dff7cdff7d5fe801fe7fe0781600846017fdf37fdf57fa007f9ff801fe80211805ff7cdff7d5fe801fe7fe007e600832017fdd97f5df7ea007e9fd801eb7f6027f9fe799fe7a9fc801fc7fa007c9fe7da01,
  0x695f96ce0080200802008020080200802006fdfb742028560083a0780231792778025b7cdff7d60483e0182a05802237b255802417cdff7d5ff80a0180a01802077f2118020d48def515ef7be0173e01802077f2118020d55df35c5f37ce007ee04802776f321802dd61df57d5f577e007aa0296e41b42a98028f7d5ff7fdff7f6007f9ff93637ac28f806797d5ff7fdff7f6007f9ff81e058420d8060b7d5ff7fdff7f6007f9ff801fe8420d8060b7d5ff7fdff7f6007f9ff801f98560d8060b7d5ff7fdff7f6007f9ff801f9811fc8060b7e5fd7f5fd7de007e9fd801eb831cd805e47a9fe7f9fe7ea007f1fe801f2821de80207,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560783a078023188e7796e00936077fdff7fe0483a0582a058022386655906008de057fdff7fdff80a0080a0180207816118360082e017bdef7bdef7bdf073e0180207816118360082e017cdf37cdf37cdf37ee048027795721b7600aee117d5f57d5f577df57aa0296e41b76a9a3e008360d7fdff7fdff7f5ff7f9ff93637aee8f9e60182e0b7fdff7fdff7f5ff7f9ff81e058460d82e01806017fdff7fdff7f5ff7f9ff801fe8460d82e01806017fdff7fdff7f5ff7f9ff801f98320d82e01806017fdff7fdff7f5ff7f9ff801f97edfc82e01806017fdff7fdff7f5ff7f9ff801f97edef7fa01806017fdff7fdff7f5ff7f9ff801f97edef7ce017da017fdfd7f5fd7ddfd7e9fd801eb7c5cd76600781fe7f9fe7f9fe7e9fe7f1fe801f27d9de79a007aa01,
  0x1f97e5f98020080200802008020080200802007edfb80a1081e0e81e008c5e49de5b6ea0781dff7fdff83a0482a05802237b255905ce816057bdef7bdef7c1cf8060081dfc8460d7da01805f37cdf37cdf37ee04802776f321b7556846117d5f57d5df7d5ea80a5b906d0aa68f8020d835ff7fdff7f5ff7f9ff93637ac28f9e60082a0b7fdff7fdfd7fdfe7fe07816108360b80200805ff7fdff7f5ff7f9ff801fe8420d82e00802017fdff7fdfd7fdfe7fe007e6158360b80200805ff7fdff7f5ff7f9ff801f9811fc82e00802017fdff7fdfd7fdfe7fe007e6047bdfe80200805ff7fdff7f5ff7f9ff801f9811ef7ce0b802017fdfd7f5f77f5fa7f6007ae0c735d9879fe7f9fe7f9fe7e9fe7f1fe801f2821de79a147fa01,
  0x73df9776008020080200802008020080200775fb7ba029c25b9360e81e0e81e00802317e5ff7ee04942418de0a8120a81600802237e5ff7edff8460d82e028020280600802077e5ff7edff801fc82e028020280600802077e5ff7edff801ef7fa028020280600802077e5ff7edff801ef7ce0d802028060080207625ef6adef800df48eaa7c1cf8060080207695f36fdf38012355e827cdfb8120080277725f57d5f55417161dea7d5ea80a5b802417edff7fdff7c1f37d5fe7fdfe7fe4d806377edff7fdff7c1f37d5fe7fdfe7fe07806057fdfd7f5fd741d977dfa7f5fa7f600805f07d9fe7f9fe781e67a9fc7f9fc7fa0080201,
  0x1f9775f98020080200802008020080200802007ede780a029de5b936158020e81e008023181dff7edff812549063783e0082a058020088e057fdfb7fdff8420d82e03806028060080207805ff7edff7fdff7f20b80e0180a018020081e017fdfb7fdff7fdef7fa03806028060080207805ff7edff7fdff7bdf37e20180a018020081e017bdab7bdef7bcdf48d45805cf8060080207805f36fdf37cdf348d575c6007ee04802009de117d5f57d5f55157161ddf801ea80a5b80241835ff7fdff7fdef7cdf57f6007f9ff936018de0b7fdff7fdff7bdf37d5fd801fe7fe0780605805ff7fdff7fdef7cdf57f6007f9ff802017fa017fdfd7f5fd735d977df7801fa7f600801f07f9fe7f9fe7f9de799ea7ea007f1fe802007ca01,
  0x1dd7e5f9802008020080200802008020079dfb80a069360e8020e81e008c60788dfb7fdff8c23782a0182a0580223816197edff7fdef7fa02806028060081e01815fb7fdff7bdf38360180a0180207806056adef7bcdf48eaa805cf8060081e01815bf7cdf348d57a0a007ee0480277846557d5457d57161dea801ea80a5b9060d835ff7bdff7cdf57fa007f9ff9363782a0b7fdef7fdf37d5fe801fe7fe0781600805ff7bdff7cdf57fa007f9ff801fe8020181dcd7f5d977dfa801fa7f6007adfe7c9fe779fe799ea7f2007f1fe801f27f9f9,
  0x1897e5a580200802008020080200802006adfb832028560783a078023181e239ddef7fdf3812048160a8160088e05866557bdff7cdff7e20080a018020780605844df7bd237bd457c1cf8060081e018161148df355df35c5f37ee048027784655c85717d5877d5df7d5ea80a5b906dd836a97cdff7d5ff7f5ff7f9ff93637aea0ba3df37fdf57fdfd7fdfe7fe07816108060d7cdff7d5ff7f5ff7f9ff801fe84201835f37fdf57fdfd7fdfe7fe007e6107f20d7edfd77dfd7ddfd7e9fd801eb7f5f2769e67f9ea7f9fa7f9fc7fa007c9fe7da05,
  0x1f96cdf98020080200802008020080200802007edc980a0283a0783a07802008c67788e5b81dff7d5ff8120a8120a816008022395619906057fdf57fdff80e0080a018020081e118160d805ef515ef7be007c1cf806008020784605836017cd717cdf3801f37ee04802009df21956dd845f57d5f57d5ea7d5ea80a5bb4241aa60da3e0d7fdff7fdff7f9ff7f9ff936b18de8f82e7982dff7fdff7fdfe7fdfe7fe07846058360182e017fdff7fdff7f9ff7f9ff802117fa0d8060b805ff7fdff7fdfe7fdfe7fe00801fe7f20182e017fdff7fdff7f9ff7f9ff802007e5fc7f20b805ff7fdff7fdfe7fdfe7fe00801f97bdfc7fa017fdfd7f5fd7e9fd7e9fd802007adcd7c5e47f9fe7f9fe7f9fc7f9fc7fa00801f2779f679a01,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0083a0781e009de3196e4d792077fdff7fe0482e0082a058160095623906377b2057fdff7fdff80e0180a0180600846078360b7f2017bdef7bdef8020173e0180600846078360b7f2017cdf37cdf3802007ee0484600c8677b76bb6f2117d5f57d5f57aa007aa02b765baa641a3e0d8020d7fdff7fdff7fa007f9ffaea4da3e379e60b8020b7fdff7fdff7fa007f9ff842078360582e01802017fdff7fdff7fa007f9ff7fe077f20582e01802017fdff7fdff7fa007f9ff7fe007f1fe82e01802017fdff7fdff7fa007f9ff7fe007bdfe7fa01802017fdff7fdff7fa007f9ff7fe007bdf97fa01816017fdff7fdff7fa007f9ff7fe007bdf97cdf6816017fdfd7f5fd7ea007e9fd7f600735eb765df835fe7f9fe7f9fe7f2007f1fe7fa00779f2799ea82201,
  0x1f97e5f98020080200802008020080200802007edfb80a028560083a079de0096e317924d81dff7fdff8120f8060a816558024188dec8de057fdff7fdff80a0180a0184600836077f20b805ef7bdef7bdef805cf806118020d81dfc82e017cdf37cdf37ce007ee04c8600b76776f2bb845f57d5f57d5df801eab4aa996e8f906008360d7fdff7fdff7f6007f9ff9fa4d9e6378020b82dff7fdff7fdfd801fe7fdfc81e0b81600806017fdff7fdff7f6007f9ff7be077fa0580201805ff7fdff7fdfd801fe7fdef801fe7fa00806017fdff7fdff7f6007f9ff7be007cdfe801f6805ff7fdff7fdfd801fe7fdef801f37e6057da017fdfd7f5fd7de007e9fd73600765eb831e07f9fe7f9fe7f9fa801fc7f9de801e67ca087aa01,
  0x1f97e5f98020080200802008020080200802007edfb80a029c25b8564d83a07802317920781dff7fdff812519060f8de0a8160088dec816057fdff7fdff8460d80a0b80a01802077f201805ff7fdff7fe007f20282e028060081dfc806017fdff7fdff801ef809fe80a01802077f201805ef7bdef7be0037def4b9cf8060081dfc806017cdf37cdf3801237cd577ed82802776f211845f57d5f57d5505c5df61dea80a5b906008360d7fdff7fdff7c1f37f5f57f9ff936378020a82dff7fdff7fdf07cdfd7d5fe7fe0781600802017fdff7fdff7c1f37f5f57f9ff801fe80200805ff7fdff7fdf07cdfd7d5fe7fe007e605802017fdfd7f5fd741d97dddf7e9fd801eb831fe7f9fe7f9fe7f9e0799fa7a9fc7fa007ca087fa01,
  0x1f97e5f98020080200802008020080200802007edfb80a7296e4d8560783a078023181e2381dff7fdff952418de0e8160a8160088e05866057fdff7fdff7f20b80a0180a018020780605805ff7fdff7fdef7fa02806028060081e01816017fdff7fdff7bdf3809f680a018020780605805ef7bdef7bcdf48def519cf8060081e01816017cdf37cdf348d577cd717ee048027784655845f57d5f55157161ddf7d5ea80a5b9060d8360d7fdff7fdef7cdf57f5ff7f9ff9363782a0b82dff7fdff7bdf37d5fd7fdfe7fe0781600806017fdff7fdef7cdf57f5ff7f9ff801fe80201805ff7fdff7bdf37d5fd7fdfe7fe007e6007f2017fdfd7f5cd765df7ddfd7e9fd801eb7f5f27f9fe7f9fe779e67a9fa7f9fc7fa007c9fe7da01,
  0x7e5f96260080200802008020080200802007edfb81a029360e8020e81e008c623802077fdff7be048aa0a8020a8160088e19802057fdff7bdff7fa03802028060081e05802017fdff7bdff7ce0382e028060081e05802017bdef37def48e00aadcf8060081e05802017cdf348df355e00a09fb812009de5580211515f55c5f561dea801ea80a5b9060d802dd7bdff7cdff7d5fe801fe7fe4d8de0b806bb7bdff7cdff7d5fe801fe7fe0781601806117bdff7cdff7d5fe801fe7fe007fa01806117bdff7cdff7d5fe801fe7fe007e5fc8061173dfd765fd77dfa801fa7f6007adf18060e779fe799fe7a9fc801fc7fa007c9f680231,
  0x7e5a57e60080200802008020080200802007edbf809d083a0083a078023188e009de077fdf37fdfa82e0082a058022386600956057fdf37fdf580e0180a018020781600846017bd237bd458020173e018020781600846017cd577cd71802007ee048027795600c86117d5877d5f57aa007aa0296e41b7600aa60d7fdf57fdff7fa007f9ff93637aee01a3e0b7fdf57fdff7fa007f9ff81e0584601836017fdf57fdff7fa007f9ff801fe84601836017fdf57fdff7fa007f9ff801f983201836017fdf57fdff7fa007f9ff801f97ee017f2017fddf7f5fd7ea007e9fd801eb7c600769fe7f9ea7f9fe7f2007f1fe801f27da0077a01,
  0x1b37e5f9802008020080200802008020080200725fb80a028560083a07802317927796e07935f57fdff8120f8060a8160088dec95641816377d5ff7fdff80a0180a01802077f2118360182d457bdef7bdef805cf8060081dfc8460d8060b5c5f37cdf37ce007ee04802776f321b7611aedf57d5f57d5df801ea80a5b906d0aa68f8360d7fdff7fdff7f6007f9ff93637ac28f9e60a82dff7fdff7fdfd801fe7fe07816108360b802017fdff7fdff7f6007f9ff801fe8420d82e00805ff7fdff7fdfd801fe7fe007e6158360b802017fdff7fdff7f6007f9ff801f9811fc82e00805ff7fdff7fdfd801fe7fe007e6047bdfe8020184dfd7f5fd7de007e9fd801eb831cd765fe781fe7f9fe7f9fa801fc7fa007ca08779e67f9ed,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560783a078023188e7796e076ea077fdff7fe0483a0582a0580223866559060573a057fdff7fdff80a0080a018020781611836017da017bdef7bdef7bdf073e018020781611836017da017cdf37cdf37cdf37ee048027795721b761155a117d5f57d5f577df57aa0296e41b76a9a3e0d8020d7fdff7fdff7f5ff7f9ff93637aee8f9e60a8020b7fdff7fdff7f5ff7f9ff81e058460d82e00802017fdff7fdff7f5ff7f9ff801fe8460d82e00802017fdff7fdff7f5ff7f9ff801f98320d82e00802017fdff7fdff7f5ff7f9ff801f97edfc82e00802017fdff7fdff7f5ff7f9ff801f97edef7fa00802017fdff7fdff7f5ff7f9ff801f97edef7ce0082e017fdfd7f5fd7ddfd7e9fd801eb7c5cd765fd87dfe7f9fe7f9fe7e9fe7f1fe801f27d9de799fe85201,
  0x1f9775f98020080200802008020080200802007ede780a029c25b9361581e0e81e008023181dff7edff812519063783e0582a058020088e057fdfb7fdff8460d82e03802028060080207805ff7edff7fe007f20b80e0080a018020081e017fdfb7fdff801ef7fa03802028060080207805ff7edff7fe007bdf37e20080a018020081e017bdab7bdef800df48d457c1cf8060080207805f36fdf37ce0048d575c5f37ee04802009de117d5f57d5f55417161ddf7d5ea80a5b80241835ff7fdff7fdf07cdf57f5ff7f9ff936018de0b7fdff7fdff7c1f37d5fd7fdfe7fe0780605805ff7fdff7fdf07cdf57f5ff7f9ff802017fa017fdfd7f5fd741d977df77f5fa7f600801f07f9fe7f9fe7f9e0799ea7e9fe7f1fe802007ca01,
  0x775f97e600802008020080200802008020079dfb80a7296e4d83a0783a078023181e237edff7fe549063782a0482a0580223816197edff7fdff7f20b80a0080a0180207806057edff7fdff7bdfe80a0080a0180207806057edff7fdff7bdf38360080a0180207806056adef7bdef37d23aa9f073e0180207806056fdf37cdf348d57a09f37ee0480277846557d5f57d5455c5877a9f57aa0296e418360d7fdff7fdef7cdf57f9ff7f9ff9363782a0b7fdff7fdef7cdf57f9ff7f9ff81e05802017fdff7fdef7cdf57f9ff7f9ff801fe8020181dfd7f5cd765df7e9fd7e9fd801eb7f9f27f9fe7f9de799ea7f1fe7f1fe801f27f9f9,
  0x7e5f96260080200802008020080200802007edfb81a02936158020e81e008c60788e077fdff7be048aa0f8020a8160088e05866057fdff7bdff7fa03806028060081e01816017fdff7bdff7cdf8806028060081e01816017bdef37def48d45805cf8060081e01816017cdf348df355d71801fb812009de1195611515f55c5f561ddf801ea80a5b9060d836dd7bdff7cdff7d5fd801fe7fe4d8de0a82ebb7bdff7cdff7d5fd801fe7fe0781600806117bdff7cdff7d5fd801fe7fe007fa00806117bdff7cdff7d5fd801fe7fe007e6007f21173dfd765fd77df7801fa7f6007adfd7ca0e779fe799fe7a9fa801fc7fa007c9fe7da31,
  0x7e5a57e60080200802008020080200802007edbf809d08560083a078023181e239de077fdf37fdfa83e0182a058022381619956057fdf37fdf580a0180a018020780605846017bd237bd457be0173e018020780605846017cd577cd717ce007ee048027784655c86117d5877d5f577e007aa0296e41b760daa60d7fdf57fdff7f6007f9ff93637aea0ba3e0b7fdf57fdff7f6007f9ff81e0584201836017fdf57fdff7f6007f9ff801fe84201836017fdf57fdff7f6007f9ff801f9841fc836017fdf57fdff7f6007f9ff801f97fdfc7f2017fddf7f5fd7de007e9fd801eb7f5f1769fe7f9ea7f9fe7ea007f1fe801f27f9f677a01,
  0x1b37e5f9802008020080200802008020080200725fb80a028560783a07802008c67796de4935f57fdff8120e8160a8160080223956417b2377d5ff7fdff80a0080a018020081e11835fc82d457bdef7bdef7c1cf80600802078460d7f20b5c5f37cdf37cdf37ee04802009df21b75bcaedf57d5f57d5df7d5ea80a5bb4241aa68f8020d7fdff7fdff7f5ff7f9ff936b18de8f9e60082dff7fdff7fdfd7fdfe7fe07846058360b802017fdff7fdff7f5ff7f9ff802117fa0d82e00805ff7fdff7fdfd7fdfe7fe00801fe7f20b802017fdff7fdff7f5ff7f9ff802007e5fc82e05805ff7fdff7fdfd7fdfe7fe00801f97bdfe8160184dfd7f5fd7ddfd7e9fd802007adcd7660d781fe7f9fe7f9fa7f9fc7fa00801f2779e6821ed,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0783a0781e009de3196de46ea077fdff7fe0482a0482a058160095623905ec73a057fdff7fdff80e0080a018060084607835fc7da017bdef7bdef801f073e018060084607835fc7da017cdf37cdf3801f37ee0484600c8677b75bc55a117d5f57d5f57a9f57aa02b765baa641a3e008020d7fdff7fdff7f9ff7f9ffaea4da3e379e6008020b7fdff7fdff7f9ff7f9ff842078360582e00802017fdff7fdff7f9ff7f9ff7fe077f20582e00802017fdff7fdff7f9ff7f9ff7fe007f1fe82e00802017fdff7fdff7f9ff7f9ff7fe007bdfe7fa00802017fdff7fdff7f9ff7f9ff7fe007bdf97fa05802017fdff7fdff7f9ff7f9ff7fe007bdf97ce0582e017fdfd7f5fd7e9fd7e9fd7f600735eb7660c87dfe7f9fe7f9fe7f1fe7f1fe7fa00779f279a0885201,
  0x1f97e5f98020080200802008020080200802007edfb80a029c25b83a4d83a078023181e2381dff7fdff812509060b8de0a8160088e05866057fdff7fdff8460d80e0b80a018020780605805ff7fdff7fe007f20382e028060081e01816017fdff7fdff801ef80dfe80a018020780605805ef7bdef7be0037e004b9cf8060081e01816017cdf37cdf380123801577ed828027784655845f57d5f57d5505c5ea61dea80a5b9060d8360d7fdff7fdff7c1f37f9f57f9ff9363782a0b82dff7fdff7fdf07cdfe7d5fe7fe0781600806017fdff7fdff7c1f37f9f57f9ff801fe80201805ff7fdff7fdf07cdfe7d5fe7fe007e6007f2017fdfd7f5fd741d97e9df7e9fd801eb7f5f27f9fe7f9fe7f9e0799fc7a9fc7fa007c9fe7da01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b9361581e0e81e008c623802077fdff7fe04952418de0f8160a8160088e19802057fdff7fdff8420d82e02806028060081e05802017fdff7fdff7fdfc82e02806028060081e05802017fdff7fdff7fdef7fa02806028060081e05802017fdff7fdff7fdef7ce027da028060081e05802017bdef7bdef7bcdf48def519cf8060081e05802017cdf37cdf37cd2355df35c5fb812009de55802117d5f57d5f55157161ddf7d5ea80a5b9060d8020d7fdff7fdff7bdf37d5fd7fdfe7fe4d8de0b8060b7fdff7fdff7bdf37d5fd7fdfe7fe0781601806017fdff7fdff7bdf37d5fd7fdfe7fe007fa01806017fdff7fdff7bdf37d5fd7fdfe7fe007e5fc806017fdfd7f5fd735d977df77f5fa7f6007adf1805fe7f9fe7f9fe779e67a9fa7f9fc7fa007c9f680201,
  0x7e5f97e60080200802008020080200802007edfb80a06936158020e81e008c600792077fdff7fe308de0e8020a8160088e007b2057fdff7fdef7fa02802028060081e007f2017fdff7fdef7ce0282e028060081e007f2017bdef7bcdf48defaadcf8060081e007f2017cdf37cd2355df3a09fb812009de006f2117d5457d57161ddf801ea80a5b906008020d7fdef7fdf37d5fd801fe7fe4d8de018020b7fdef7fdf37d5fd801fe7fe0781601802017fdef7fdf37d5fd801fe7fe007fa01802017fdef7fdf37d5fd801fe7fe007e601816017fdcd7f5d977df7801fa7f6007ae00835fe7f9de7f9e67a9fa801fc7fa007ca0082201,
  0x1897e5a580200802008020080200802006adfb8320283a0783a0780231792079ddef7fdf38120a7ea0a8160088dec816557bdff7cdff80df680a01802077f201844df7bd237be00519cf8060081dfc8061148df355df3801717ee04802776f211c85717d5877d5ea7d5ea80a5b906d0836a97cdff7d5ff7f9ff7f9ff93637ac20aa3df37fdf57fdfe7fdfe7fe07816108020d7cdff7d5ff7f9ff7f9ff801fe84200835f37fdf57fdfe7fdfe7fe007e6158020d7edfd77dfd7e9fd7e9fd801eb831fe769e67f9ea7f9fc7f9fc7fa007ca087fa05,
  0x1f96cdf98020080200802008020080200802007edc980a0283a0083a078023188e7781e5b81dff7d5ff8120b8020a8160088e1995605906057fdf57fdff80e0180a0180207816118060d805ef515ef7be00805cf8060081e0584601836017cd717cdf3802007ee048027795721846dd845f57d5f57d5ea801ea80a5b906ddaa60da3e0d7fdff7fdff7fa007f9ff93637aee8f82a7982dff7fdff7fdfe801fe7fe07816118360082e017fdff7fdff7fa007f9ff801fe8460d8020b805ff7fdff7fdfe801fe7fe007e60c8360082e017fdff7fdff7fa007f9ff801f97edfc8020b805ff7fdff7fdfe801fe7fe007e5fb7be007fa017fdfd7f5fd7ea007e9fd801eb7c5cd7f5e47f9fe7f9fe7f9fc801fc7fa007c9f6779fe79a01,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560083a07802317927796e4d802077fdff7fe0483e0182a05802237b25590637802057fdff7fdff80a0180a01802077f2118360b802017bdef7bdef7be0173e01802077f2118360b802017cdf37cdf37ce007ee04802776f321b76bb802117d5f57d5f577e007aa0296e41b42a9a3e0d8020d7fdff7fdff7f6007f9ff93637ac28f9e60b8060b7fdff7fdff7f6007f9ff81e058420d82e01806017fdff7fdff7f6007f9ff801fe8420d82e01806017fdff7fdff7f6007f9ff801f98560d82e01806017fdff7fdff7f6007f9ff801f9811fc82e01806017fdff7fdff7f6007f9ff801f9811ef7fa01806017fdff7fdff7f6007f9ff801f9811ef7cdf6806017fdfd7f5fd7de007e9fd801eb831cd765df805fe7f9fe7f9fe7ea007f1fe801f2821de799ea80201,
  0x1dd7e5f980200802008020080200802008020079dfb80a029de5b9360e8020e81e008c60788dfb7fdff812559063782a0182a0580223816197edff7fdff8420d82e02806028060081e01815fb7fdff7fdff7f20b80a0180a0180207806057edff7fdff7fdef7fa02806028060081e01815fb7fdff7fdff7bdf38360180a0180207806056adef7bdef7bcdf48eaa805cf8060081e01815bf7cdf37cdf348d57a0a007ee0480277846557d5f57d5f55157161dea801ea80a5b9060d835ff7fdff7fdef7cdf57fa007f9ff9363782a0b7fdff7fdff7bdf37d5fe801fe7fe0781600805ff7fdff7fdef7cdf57fa007f9ff801fe8020181dfd7f5fd735d977dfa801fa7f6007adfe7c9fe7f9fe7f9de799ea7f2007f1fe801f27f9f9,
  0x1f97e5f98020080200802008020080200802007edfb9ca0296e4d8560783a078023181e2381dff7fdff812308de0f8160a8160088e05866057fdff7fdff7f20b80e0080a018020780605805ff7fdff7fdef7fa03802028060081e01816017fdff7fdff7bdf37e20080a018020780605805ef7bdef7bcdf48d457c1cf8060081e01816017cdf37cdf348d575c5f37ee048027784655845f57d5457d57161ddf7d5ea80a5b9060d8360d7fdff7bdff7cdf57f5ff7f9ff9363782a0b82dff7fdef7fdf37d5fd7fdfe7fe0781600806017fdff7bdff7cdf57f5ff7f9ff801fe80201805ff7fdef7fdf37d5fd7fdfe7fe007e6007f2017fdfd735fd765df7ddfd7e9fd801eb7f5f27f9fe7f9de7f9e67a9fa7f9fc7fa007c9fe7da01,
  0x1f9625f980200802008020080200802007edab80a0c83a0783a078023188e0081dff7bdff8aa0a8120a8160088e19802057fdef7fdf38360080a018020781600805ef37def48eaa7c1cf8060081e05802017cd237cd57a09f37ee048027795600845f55c5f561dea7d5ea80a5b9060db420d7fdf37fdf57f9ff7f9ff9363782eb182dff7cdff7d5fe7fdfe7fe0781601846017fdf37fdf57f9ff7f9ff801fe80611805ff7cdff7d5fe7fdfe7fe007e5fc846017fdd97f5df7e9fd7e9fd801eb7c6117f9fe799fe7a9fc7f9fc7fa007c9f680201,
  0x695f96ce0080200802008020080200802006fdfb7420283a0083a078023181e777925b7cdff7d60482e0082a0580223816557b2417cdff7d5ff80e0180a0180207806117f20d48def515ef8020173e0180207806117f20d55df35c5f3802007ee0480277847216f2dd61df57d5f57aa007aa0296e41b76a98028f7d5ff7fdff7fa007f9ff93637aea8f802797d5ff7fdff7fa007f9ff81e058420d8020b7d5ff7fdff7fa007f9ff801fe8420d8020b7d5ff7fdff7fa007f9ff801f98420d8160b7d5ff7fdff7fa007f9ff801f97fdfc8160b7e5fd7f5fd7ea007e9fd801eb7f5cd835e47a9fe7f9fe7f2007f1fe801f27f9de82207,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560083a07802008c67796de4936077fdff7fe0483e0182a058020088e55905ec8de057fdff7fdff80a0180a018020081e11835fc82e017bdef7bdef7be0173e018020081e11835fc82e017cdf37cdf37ce007ee04802009df21b75bcaee117d5f57d5f577e007aa0296ed0906a9a3e008360d7fdff7fdff7f6007f9ff936b18de8f9e60082e0b7fdff7fdff7f6007f9ff81e118160d82e00806017fdff7fdff7f6007f9ff802117fa0d82e00806017fdff7fdff7f6007f9ff802007f9fc82e00806017fdff7fdff7f6007f9ff802007e5fc82e05806017fdff7fdff7f6007f9ff802007e5ef7fa05806017fdff7fdff7f6007f9ff802007e5ef7ce057da017fdfd7f5fd7de007e9fd802007adcd7660c781fe7f9fe7f9fe7ea007f1fe802007c9de79a087aa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560783a0781e009de3196dba88e077fdff7fe0483a0582a058160095623905ce866057fdff7fdff80a0080a018060084607835f6816017bdef7bdef7bdf073e018060084607835f6816017cdf37cdf37cdf37ee0484600c8677b7556956117d5f57d5f577df57aa02b765baa641a3e008360d7fdff7fdff7f5ff7f9ffaea4da3e379e60082e0b7fdff7fdff7f5ff7f9ff842078360582e00806017fdff7fdff7f5ff7f9ff7fe077f20582e00806017fdff7fdff7f5ff7f9ff7fe007f1fe82e00806017fdff7fdff7f5ff7f9ff7fe007bdfe7fa00806017fdff7fdff7f5ff7f9ff7fe007bdf97fa007f2017fdff7fdff7f5ff7f9ff7fe007bdf97ce0b7f2017fdfd7f5fd7ddfd7e9fd7f600735eb7661e7c9fe7f9fe7f9fe7e9fe7f1fe7fa00779f279a147da01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b9360e81e0e81e008c600792077fdff7fe04956418de0b8160a8160088e007b2057fdff7fdff8420d82e03806028060081e007f2017fdff7fdff7fdfc82e03806028060081e007f2017fdff7fdff7fdef7fa03806028060081e007f2017fdff7fdff7fdef7ce037da028060081e007f2017bdef7bdef7bcdf48e00519cf8060081e007f2017cdf37cdf37cd2355e005c5fb812009de006f2117d5f57d5f55157161dea7d5ea80a5b906008020d7fdff7fdff7bdf37d5fe7fdfe7fe4d8de018020b7fdff7fdff7bdf37d5fe7fdfe7fe0781601802017fdff7fdff7bdf37d5fe7fdfe7fe007fa01802017fdff7fdff7bdf37d5fe7fdfe7fe007e601816017fdfd7f5fd735d977dfa7f5fa7f6007ae00835fe7f9fe7f9fe779e67a9fc7f9fc7fa007ca0082201,
  0x1f97e5f98020080200802008020080200802007edfb9ca0296e4d8560083a07802317920781dff7fdff812308de0f8020a8160088dec816057fdff7fdff7f20b80a0080a01802077f201805ff7fdff7fdef7fa02802028060081dfc806017fdff7fdff7bdf380a0b80a01802077f201805ef7bdef7bcdf48defaadcf8060081dfc806017cdf37cdf348d577ce827ee04802776f211845f57d5457d57161ddf801ea80a5b906008360d7fdff7bdff7cdf57f6007f9ff936378020a82dff7fdef7fdf37d5fd801fe7fe0781600802017fdff7bdff7cdf57f6007f9ff801fe80200805ff7fdef7fdf37d5fd801fe7fe007e605802017fdfd735fd765df7de007e9fd801eb831fe7f9fe7f9de7f9e67a9fa801fc7fa007ca087fa01,
  0x695f96ce0080200802008020080200802006fdfb7420283a0783a0780231792778025b7cdff7d60482a0482a05802237b255802417cdff7d5ff80e0080a01802077f2118020d48def515ef801f073e01802077f2118020d55df35c5f3801f37ee04802776f321802dd61df57d5f57a9f57aa0296e41b42a98028f7d5ff7fdff7f9ff7f9ff93637ac28f806797d5ff7fdff7f9ff7f9ff81e058420d8060b7d5ff7fdff7f9ff7f9ff801fe8420d8060b7d5ff7fdff7f9ff7f9ff801f98560d8060b7d5ff7fdff7f9ff7f9ff801f9811fc8060b7e5fd7f5fd7e9fd7e9fd801eb831cd805e47a9fe7f9fe7f1fe7f1fe801f2821de80207,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0083a078023188e7796e00936077fdff7fe0482e0082a058022386655906008de057fdff7fdff80e0180a0180207816118360082e017bdef7bdef8020173e0180207816118360082e017cdf37cdf3802007ee048027795721b7600aee117d5f57d5f57aa007aa0296e41b76a9a3e008360d7fdff7fdff7fa007f9ff93637aee8f9e60182e0b7fdff7fdff7fa007f9ff81e058460d82e01806017fdff7fdff7fa007f9ff801fe8460d82e01806017fdff7fdff7fa007f9ff801f98320d82e01806017fdff7fdff7fa007f9ff801f97edfc82e01806017fdff7fdff7fa007f9ff801f97edef7fa01806017fdff7fdff7fa007f9ff801f97edef7ce017da017fdfd7f5fd7ea007e9fd801eb7c5cd76600781fe7f9fe7f9fe7f2007f1fe801f27d9de79a007aa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560083a07802317927796dba81e077fdff7fe0483e0182a05802237b255905ce816057fdff7fdff80a0180a01802077f211835f6806017bdef7bdef7be0173e01802077f211835f6806017cdf37cdf37ce007ee04802776f321b7556846117d5f57d5f577e007aa0296e41b42a9a3e008360d7fdff7fdff7f6007f9ff93637ac28f9e60082a0b7fdff7fdff7f6007f9ff81e058420d82e00802017fdff7fdff7f6007f9ff801fe8420d82e00802017fdff7fdff7f6007f9ff801f98560d82e00802017fdff7fdff7f6007f9ff801f9811fc82e00802017fdff7fdff7f6007f9ff801f9811ef7fa00802017fdff7fdff7f6007f9ff801f9811ef7ce0b802017fdfd7f5fd7de007e9fd801eb831cd7661e7f9fe7f9fe7f9fe7ea007f1fe801f2821de79a147fa01,
  0x1dd7e5f980200802008020080200802008020079dfb80a029c25b9360e81e0e81e008c60788dfb7fdff812509063782a0482a0580223816197edff7fdff8460d82e02802028060081e01815fb7fdff7fe007f20b80a0080a0180207806057edff7fdff801ef7fa02802028060081e01815fb7fdff7fe007bdf38360080a0180207806056adef7bdef800df48eaa7c1cf8060081e01815bf7cdf37ce0048d57a09f37ee0480277846557d5f57d5f55417161dea7d5ea80a5b9060d835ff7fdff7fdf07cdf57f9ff7f9ff9363782a0b7fdff7fdff7c1f37d5fe7fdfe7fe0781600805ff7fdff7fdf07cdf57f9ff7f9ff801fe8020181dfd7f5fd741d977dfa7f5fa7f6007adfe7c9fe7f9fe7f9e0799ea7f1fe7f1fe801f27f9f9,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b936158020e81e008c60788e077fdff7fe04952418de0f8020a8160088e05866057fdff7fdff8420d82e03806028060081e01816017fdff7fdff7fdfc82e03806028060081e01816017fdff7fdff7fdef7fa03806028060081e01816017fdff7fdff7fdef7cdf8806028060081e01816017bdef7bdef7bcdf48d45805cf8060081e01816017cdf37cdf37cd2355d71801fb812009de11956117d5f57d5f55157161ddf801ea80a5b9060d8360d7fdff7fdff7bdf37d5fd801fe7fe4d8de0a82e0b7fdff7fdff7bdf37d5fd801fe7fe0781600806017fdff7fdff7bdf37d5fd801fe7fe007fa00806017fdff7fdff7bdf37d5fd801fe7fe007e6007f2017fdfd7f5fd735d977df7801fa7f6007adfd7c9fe7f9fe7f9fe779e67a9fa801fc7fa007c9fe7da01,
  0x7e5f97e60080200802008020080200802007edfb80a069360e8020e81e008c623802077fdff7fe308de0a8060a8160088e19802057fdff7fdef7fa02806028060081e05802017fdff7fdef7ce0d806028060081e05802017bdef7bcdf48eaa805cf8060081e05802017cdf37cd2355e82801fb812009de55802117d5457d57161dea801ea80a5b9060d8020d7fdef7fdf37d5fe801fe7fe4d8de0b8060b7fdef7fdf37d5fe801fe7fe0781601806017fdef7fdf37d5fe801fe7fe007fa01806017fdef7fdf37d5fe801fe7fe007e5fc806017fdcd7f5d977dfa801fa7f6007adf1805fe7f9de7f9e67a9fc801fc7fa007c9f680201,
  0x1897e5a580200802008020080200802006adfb832028560783a0780231801e49ddef7fdf3812048160a8160088e007b2557bdff7cdff7e20080a0180207801fc844df7bd237bd457c1cf8060081e007f21148df355df35c5f37ee0480277801bcc85717d5877d5df7d5ea80a5b906d0802a97cdff7d5ff7f5ff7f9ff93637ac600a3df37fdf57fdfd7fdfe7fe07816118020d7cdff7d5ff7f5ff7f9ff801fe84600835f37fdf57fdfd7fdfe7fe007e6118160d7edfd77dfd7ddfd7e9fd801eb8020d769e67f9ea7f9fa7f9fc7fa007ca0082205,
  0x1f96cdf98020080200802008020080200802007edc980a0283a0783a078023181e777925b81dff7d5ff8120a8120a8160088e05955ec906057fdf57fdff80e0080a0180207806117f20d805ef515ef7be007c1cf8060081e01845fc836017cd717cdf3801f37ee0480277847216f2dd845f57d5f57d5ea7d5ea80a5b906ddaa600a3e0d7fdff7fdff7f9ff7f9ff93637aea8f8027982dff7fdff7fdfe7fdfe7fe07816108360082e017fdff7fdff7f9ff7f9ff801fe8420d8020b805ff7fdff7fdfe7fdfe7fe007e6108360582e017fdff7fdff7f9ff7f9ff801f97fdfc8160b805ff7fdff7fdfe7fdfe7fe007e5ff7be057fa017fdfd7f5fd7e9fd7e9fd801eb7f5cd831e47f9fe7f9fe7f9fc7f9fc7fa007c9fe77a0879a01,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0083a07802008c67796e4d88e077fdff7fe0482e0082a058020088e5590637866057fdff7fdff80e0180a018020081e118360b816017bdef7bdef8020173e018020081e118360b816017cdf37cdf3802007ee04802009df21b76bb956117d5f57d5f57aa007aa0296ed0906a9a3e0d8360d7fdff7fdff7fa007f9ff936b18de8f9e60b82e0b7fdff7fdff7fa007f9ff81e118160d82e01806017fdff7fdff7fa007f9ff802117fa0d82e01806017fdff7fdff7fa007f9ff802007f9fc82e01806017fdff7fdff7fa007f9ff802007e5fc82e017f2017fdff7fdff7fa007f9ff802007e5ef7fa017f2017fdff7fdff7fa007f9ff802007e5ef7cdf67f2017fdfd7f5fd7ea007e9fd802007adcd765df7c9fe7f9fe7f9fe7f2007f1fe802007c9de799ea7da01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b9360e81e0e81e008c5e481e077fdff7fe04946418de0a8160a8160088dec816057fdff7fdff8460d82e03806028060081dfc806017fdff7fdff801fc82e03806028060081dfc806017fdff7fdff801ef7fa03806028060081dfc806017fdff7fdff801ef7ce037da028060081dfc806017bdef7bdef800df48e00519cf8060081dfc806017cdf37cdf38012355e005c5fb812009ddbc846117d5f57d5f55417161dea7d5ea80a5b906008360d7fdff7fdff7c1f37d5fe7fdfe7fe4d8de0082a0b7fdff7fdff7c1f37d5fe7fdfe7fe0781600802017fdff7fdff7c1f37d5fe7fdfe7fe007fa00802017fdff7fdff7c1f37d5fe7fdfe7fe007e605802017fdfd7f5fd741d977dfa7f5fa7f6007ae0c7f9fe7f9fe7f9fe781e67a9fc7f9fc7fa007ca087fa01,
  0x1f97e5f98020080200802008020080200802007edfb80a7296e4d83a0083a078023181e2381dff7fdff952418de0b8020a8160088e05866057fdff7fdff7f20b80e0080a018020780605805ff7fdff7fdef7fa03802028060081e01816017fdff7fdff7bdf380e0b80a018020780605805ef7bdef7bcdf48e00aadcf8060081e01816017cdf37cdf348d57802827ee048027784655845f57d5f55157161dea801ea80a5b9060d8360d7fdff7fdef7cdf57fa007f9ff9363782a0b82dff7fdff7bdf37d5fe801fe7fe0781600806017fdff7fdef7cdf57fa007f9ff801fe80201805ff7fdff7bdf37d5fe801fe7fe007e6007f2017fdfd7f5cd765df7ea007e9fd801eb7f5f27f9fe7f9fe779e67a9fc801fc7fa007c9fe7da01,
  0x1b37e5f9802008020080200802008020080200725fb80a0283a0783a07802317927796e07935f57fdff8120a8120a8160088dec95641816377d5ff7fdff80e0080a01802077f2118360182d457bdef7be007c1cf8060081dfc8460d8060b5c5f37cdf3801f37ee04802776f321b7611aedf57d5f57d5ea7d5ea80a5b906d0aa68f8360d7fdff7fdff7f9ff7f9ff93637ac28f9e60a82dff7fdff7fdfe7fdfe7fe07816108360b802017fdff7fdff7f9ff7f9ff801fe8420d82e00805ff7fdff7fdfe7fdfe7fe007e6158360b802017fdff7fdff7f9ff7f9ff801f9811fc82e00805ff7fdff7fdfe7fdfe7fe007e6047bdfe8020184dfd7f5fd7e9fd7e9fd801eb831cd765fe781fe7f9fe7f9fc7f9fc7fa007ca08779e67f9ed,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0083a078023188e7796e076ea077fdff7fe0482e0082a0580223866559060573a057fdff7fdff80e0180a018020781611836017da017bdef7bdef8020173e018020781611836017da017cdf37cdf3802007ee048027795721b761155a117d5f57d5f57aa007aa0296e41b76a9a3e0d8020d7fdff7fdff7fa007f9ff93637aee8f9e60a8020b7fdff7fdff7fa007f9ff81e058460d82e00802017fdff7fdff7fa007f9ff801fe8460d82e00802017fdff7fdff7fa007f9ff801f98320d82e00802017fdff7fdff7fa007f9ff801f97edfc82e00802017fdff7fdff7fa007f9ff801f97edef7fa00802017fdff7fdff7fa007f9ff801f97edef7ce0082e017fdfd7f5fd7ea007e9fd801eb7c5cd765fd87dfe7f9fe7f9fe7f2007f1fe801f27d9de799fe85201,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b9361581e0e81e008c60788e077fdff7fe04946418de0f8160a8160088e05866057fdff7fdff8460d82e03802028060081e01816017fdff7fdff801fc82e03802028060081e01816017fdff7fdff801ef7fa03802028060081e01816017fdff7fdff801ef7cdf8802028060081e01816017bdef7bdef800df48d457c1cf8060081e01816017cdf37cdf38012355d717cdfb812009de11956117d5f57d5f55417161ddf7d5ea80a5b9060d8360d7fdff7fdff7c1f37d5fd7fdfe7fe4d8de0a82e0b7fdff7fdff7c1f37d5fd7fdfe7fe0781600806017fdff7fdff7c1f37d5fd7fdfe7fe007fa00806017fdff7fdff7c1f37d5fd7fdfe7fe007e6007f2017fdfd7f5fd741d977df77f5fa7f6007adfd7c9fe7f9fe7f9fe781e67a9fa7f9fc7fa007c9fe7da01,
  0x1f97e5f98020080200802008020080200802007edfb80a7296e4d83a0783a078023188e0081dff7fdff952418de0a8120a8160088e19802057fdff7fdff7f20b80a0080a018020781600805ff7fdff7fdef7fa02802028060081e05802017fdff7fdff7bdf38360080a018020781600805ef7bdef7bcdf48eaa7c1cf8060081e05802017cdf37cdf348d57a09f37ee048027795600845f57d5f55157161dea7d5ea80a5b9060d8020d7fdff7fdef7cdf57f9ff7f9ff9363782e0182dff7fdff7bdf37d5fe7fdfe7fe0781601806017fdff7fdef7cdf57f9ff7f9ff801fe80601805ff7fdff7bdf37d5fe7fdfe7fe007e5fc806017fdfd7f5cd765df7e9fd7e9fd801eb7c6017f9fe7f9fe779e67a9fc7f9fc7fa007c9f680201,
  0x7e5f96260080200802008020080200802007edfb81a02936158020e81e008c600792077fdff7be048aa0f8020a8160088e007b2057fdff7bdff7fa03806028060081e007f2017fdff7bdff7cdf8806028060081e007f2017bdef37def48d45805cf8060081e007f2017cdf348df355d71801fb812009de006f211515f55c5f561ddf801ea80a5b90600802dd7bdff7cdff7d5fd801fe7fe4d8de01802bb7bdff7cdff7d5fd801fe7fe0781601802117bdff7cdff7d5fd801fe7fe007fa01802117bdff7cdff7d5fd801fe7fe007e6018161173dfd765fd77df7801fa7f6007ae008360e779fe799fe7a9fa801fc7fa007ca0082231,
  0x7e5a57e60080200802008020080200802007edbf809d08560083a0780231801e49de077fdf37fdfa83e0182a0580223801ec956057fdf37fdf580a0180a0180207801fc846017bd237bd457be0173e0180207801fc846017cd577cd717ce007ee0480277801bcc86117d5877d5f577e007aa0296e41b4200aa60d7fdf57fdff7f6007f9ff93637ac600a3e0b7fdf57fdff7f6007f9ff81e0584600836017fdf57fdff7f6007f9ff801fe84600836017fdf57fdff7f6007f9ff801f984605836017fdf57fdff7f6007f9ff801f9802057f2017fddf7f5fd7de007e9fd801eb8020c769fe7f9ea7f9fe7ea007f1fe801f28020877a01,
  0x1b37e5f9802008020080200802008020080200725fb80a028560783a078023181e7796e23935f57fdff8120e8160a8160088e0595641866377d5ff7fdff80a0080a0180207806118360582d457bdef7bdef7c1cf8060081e018460d8160b5c5f37cdf37cdf37ee048027784721b7655aedf57d5f57d5df7d5ea80a5b906ddaa68f8360d7fdff7fdff7f5ff7f9ff93637aea8f9e60b82dff7fdff7fdfd7fdfe7fe07816108360b806017fdff7fdff7f5ff7f9ff801fe8420d82e01805ff7fdff7fdfd7fdfe7fe007e6108360b7f2017fdff7fdff7f5ff7f9ff801f97fdfc82dfc805ff7fdff7fdfd7fdfe7fe007e5ff7bdfe7f20184dfd7f5fd7ddfd7e9fd801eb7f5cd765f2781fe7f9fe7f9fa7f9fc7fa007c9fe779e67d9ed,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0783a07802008c67796e236ea077fdff7fe0482a0482a058020088e559061973a057fdff7fdff80e0080a018020081e11836057da017bdef7bdef801f073e018020081e11836057da017cdf37cdf3801f37ee04802009df21b765555a117d5f57d5f57a9f57aa0296ed0906a9a3e0d8020d7fdff7fdff7f9ff7f9ff936b18de8f9e60b8020b7fdff7fdff7f9ff7f9ff81e118160d82e01802017fdff7fdff7f9ff7f9ff802117fa0d82e01802017fdff7fdff7f9ff7f9ff802007f9fc82e01802017fdff7fdff7f9ff7f9ff802007e5fc82dfc802017fdff7fdff7f9ff7f9ff802007e5ef7f9fc802017fdff7fdff7f9ff7f9ff802007e5ef7cdfc82e017fdfd7f5fd7e9fd7e9fd802007adcd765f187dfe7f9fe7f9fe7f1fe7f1fe802007c9de799f685201,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b9361581e0e81e008c60788e077fdff7fe04942418de0e8160a8160088e05866057fdff7fdff8460d82e02806028060081e01816017fdff7fdff801fc82e02806028060081e01816017fdff7fdff801ef7fa02806028060081e01816017fdff7fdff801ef7ce027da028060081e01816017bdef7bdef800df48def519cf8060081e01816017cdf37cdf38012355df35c5fb812009de11956117d5f57d5f55417161ddf7d5ea80a5b9060d8360d7fdff7fdff7c1f37d5fd7fdfe7fe4d8de0a82e0b7fdff7fdff7c1f37d5fd7fdfe7fe0781600806017fdff7fdff7c1f37d5fd7fdfe7fe007fa00806017fdff7fdff7c1f37d5fd7fdfe7fe007e6007f2017fdfd7f5fd741d977df77f5fa7f6007adfd7c9fe7f9fe7f9fe781e67a9fa7f9fc7fa007c9fe7da01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b9360e8020e81e008c623802077fdff7fe04952418de0a8020a8160088e19802057fdff7fdff8420d82e03802028060081e05802017fdff7fdff7fdfc82e03802028060081e05802017fdff7fdff7fdef7fa03802028060081e05802017fdff7fdff7fdef7ce0382e028060081e05802017bdef7bdef7bcdf48e00aadcf8060081e05802017cdf37cdf37cd2355e00a09fb812009de55802117d5f57d5f55157161dea801ea80a5b9060d8020d7fdff7fdff7bdf37d5fe801fe7fe4d8de0b8060b7fdff7fdff7bdf37d5fe801fe7fe0781601806017fdff7fdff7bdf37d5fe801fe7fe007fa01806017fdff7fdff7bdf37d5fe801fe7fe007e5fc806017fdfd7f5fd735d977dfa801fa7f6007adf1805fe7f9fe7f9fe779e67a9fc801fc7fa007c9f680201,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0783a07802317927796e4d802077fdff7fe0482a0482a05802237b25590637802057fdff7fdff80e0080a01802077f2118360b802017bdef7bdef801f073e01802077f2118360b802017cdf37cdf3801f37ee04802776f321b76bb802117d5f57d5f57a9f57aa0296e41b42a9a3e0d8020d7fdff7fdff7f9ff7f9ff93637ac28f9e60b8060b7fdff7fdff7f9ff7f9ff81e058420d82e01806017fdff7fdff7f9ff7f9ff801fe8420d82e01806017fdff7fdff7f9ff7f9ff801f98560d82e01806017fdff7fdff7f9ff7f9ff801f9811fc82e01806017fdff7fdff7f9ff7f9ff801f9811ef7fa01806017fdff7fdff7f9ff7f9ff801f9811ef7cdf6806017fdfd7f5fd7e9fd7e9fd801eb831cd765df805fe7f9fe7f9fe7f1fe7f1fe801f2821de799ea80201,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b9360e8020e81e008c623802077fdff7fe04956418de0a8060a8160088e19802057fdff7fdff8420d82e02806028060081e05802017fdff7fdff7fdfc82e02806028060081e05802017fdff7fdff7fdef7fa02806028060081e05802017fdff7fdff7fdef7ce0d806028060081e05802017bdef7bdef7bcdf48eaa805cf8060081e05802017cdf37cdf37cd2355e82801fb812009de55802117d5f57d5f55157161dea801ea80a5b9060d8020d7fdff7fdff7bdf37d5fe801fe7fe4d8de0b8060b7fdff7fdff7bdf37d5fe801fe7fe0781601806017fdff7fdff7bdf37d5fe801fe7fe007fa01806017fdff7fdff7bdf37d5fe801fe7fe007e5fc806017fdfd7f5fd735d977dfa801fa7f6007adf1805fe7f9fe7f9fe779e67a9fc801fc7fa007c9f680201,
  0x1f97e5f98020080200802008020080200802007edfb9ca0296e4d8560783a0780231801e481dff7fdff812308de0f8160a8160088e007b2057fdff7fdff7f20b80e0080a0180207801fc805ff7fdff7fdef7fa03802028060081e007f2017fdff7fdff7bdf37e20080a0180207801fc805ef7bdef7bcdf48d457c1cf8060081e007f2017cdf37cdf348d575c5f37ee0480277801bc845f57d5457d57161ddf7d5ea80a5b906008020d7fdff7bdff7cdf57f5ff7f9ff936378060082dff7fdef7fdf37d5fd7fdfe7fe0781601802017fdff7bdff7cdf57f5ff7f9ff801fe80600805ff7fdef7fdf37d5fd7fdfe7fe007e601816017fdfd735fd765df7ddfd7e9fd801eb8020d7f9fe7f9de7f9e67a9fa7f9fc7fa007ca0082201,
  0x1f9625f980200802008020080200802007edab80a0c83a0783a07802317920781dff7bdff8aa0a8120a8160088dec816057fdef7fdf38360080a01802077f201805ef37def48eaa7c1cf8060081dfc806017cd237cd57a09f37ee04802776f211845f55c5f561dea7d5ea80a5b90600b760d7fdf37fdf57f9ff7f9ff93637802ba82dff7cdff7d5fe7fdfe7fe0781600842017fdf37fdf57f9ff7f9ff801fe80210805ff7cdff7d5fe7fdfe7fe007e605842017fdd97f5df7e9fd7e9fd801eb8320e7f9fe799fe7a9fc7f9fc7fa007ca087fa01,
  0x695f96ce0080200802008020080200802006fdfb7420283a0083a07802318027788e5b7cdff7d60482e0082a058022380255866417cdff7d5ff80e0180a0180207802118160d48def515ef8020173e0180207802118160d55df35c5f3802007ee048027780321956dd61df57d5f57aa007aa0296e41b42a98368f7d5ff7fdff7fa007f9ff93637ac68f82e797d5ff7fdff7fa007f9ff81e058460d8060b7d5ff7fdff7fa007f9ff801fe8460d8060b7d5ff7fdff7fa007f9ff801f98460d7f20b7d5ff7fdff7fa007f9ff801f9801fc7f20b7e5fd7f5fd7ea007e9fd801eb801cd7c9e47a9fe7f9fe7f2007f1fe801f2801de7da07,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560083a078023181e7796e23936077fdff7fe0483e0182a058022381655906198de057fdff7fdff80a0180a0180207806118360582e017bdef7bdef7be0173e0180207806118360582e017cdf37cdf37ce007ee048027784721b7655aee117d5f57d5f577e007aa0296e41b76a9a3e0d8360d7fdff7fdff7f6007f9ff93637aea8f9e60b82e0b7fdff7fdff7f6007f9ff81e058420d82e01806017fdff7fdff7f6007f9ff801fe8420d82e01806017fdff7fdff7f6007f9ff801f98420d82dfc806017fdff7fdff7f6007f9ff801f97fdfc82dfc806017fdff7fdff7f6007f9ff801f97fdef7f9fc806017fdff7fdff7f6007f9ff801f97fdef7cdfc7da017fdfd7f5fd7de007e9fd801eb7f5cd765f1781fe7f9fe7f9fe7ea007f1fe801f27f9de799f67aa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560783a07802008c67796dba792077fdff7fe0483a0582a058020088e55905ce7b2057fdff7fdff80a0080a018020081e11835f67f2017bdef7bdef7bdf073e018020081e11835f67f2017cdf37cdf37cdf37ee04802009df21b75566f2117d5f57d5f577df57aa0296ed0906a9a3e008020d7fdff7fdff7f5ff7f9ff936b18de8f9e6008020b7fdff7fdff7f5ff7f9ff81e118160d82e00802017fdff7fdff7f5ff7f9ff802117fa0d82e00802017fdff7fdff7f5ff7f9ff802007f9fc82e00802017fdff7fdff7f5ff7f9ff802007e5fc82e00816017fdff7fdff7f5ff7f9ff802007e5ef7fa00816017fdff7fdff7f5ff7f9ff802007e5ef7ce0b816017fdfd7f5fd7ddfd7e9fd802007adcd7661e835fe7f9fe7f9fe7e9fe7f1fe802007c9de79a1482201,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b936158020e81e008c600792077fdff7fe04956418de0e8020a8160088e007b2057fdff7fdff8420d82e02802028060081e007f2017fdff7fdff7fdfc82e02802028060081e007f2017fdff7fdff7fdef7fa02802028060081e007f2017fdff7fdff7fdef7ce0282e028060081e007f2017bdef7bdef7bcdf48defaadcf8060081e007f2017cdf37cdf37cd2355df3a09fb812009de006f2117d5f57d5f55157161ddf801ea80a5b906008020d7fdff7fdff7bdf37d5fd801fe7fe4d8de018020b7fdff7fdff7bdf37d5fd801fe7fe0781601802017fdff7fdff7bdf37d5fd801fe7fe007fa01802017fdff7fdff7bdf37d5fd801fe7fe007e601816017fdfd7f5fd735d977df7801fa7f6007ae00835fe7f9fe7f9fe779e67a9fa801fc7fa007ca0082201,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0783a07802317927796dba81e077fdff7fe0482a0482a05802237b255905ce816057fdff7fdff80e0080a01802077f211835f6806017bdef7bdef801f073e01802077f211835f6806017cdf37cdf3801f37ee04802776f321b7556846117d5f57d5f57a9f57aa0296e41b42a9a3e008360d7fdff7fdff7f9ff7f9ff93637ac28f9e60082a0b7fdff7fdff7f9ff7f9ff81e058420d82e00802017fdff7fdff7f9ff7f9ff801fe8420d82e00802017fdff7fdff7f9ff7f9ff801f98560d82e00802017fdff7fdff7f9ff7f9ff801f9811fc82e00802017fdff7fdff7f9ff7f9ff801f9811ef7fa00802017fdff7fdff7f9ff7f9ff801f9811ef7ce0b802017fdfd7f5fd7e9fd7e9fd801eb831cd7661e7f9fe7f9fe7f9fe7f1fe7f1fe801f2821de79a147fa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b9360e81e0e81e008c623802077fdff7fe04942418de0a8120a8160088e19802057fdff7fdff8460d82e02802028060081e05802017fdff7fdff801fc82e02802028060081e05802017fdff7fdff801ef7fa02802028060081e05802017fdff7fdff801ef7ce0d802028060081e05802017bdef7bdef800df48eaa7c1cf8060081e05802017cdf37cdf38012355e827cdfb812009de55802117d5f57d5f55417161dea7d5ea80a5b9060d8020d7fdff7fdff7c1f37d5fe7fdfe7fe4d8de0b8060b7fdff7fdff7c1f37d5fe7fdfe7fe0781601806017fdff7fdff7c1f37d5fe7fdfe7fe007fa01806017fdff7fdff7c1f37d5fe7fdfe7fe007e5fc806017fdfd7f5fd741d977dfa7f5fa7f6007adf1805fe7f9fe7f9fe781e67a9fc7f9fc7fa007c9f680201,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b936158020e81e008c600792077fdff7fe04952418de0f8020a8160088e007b2057fdff7fdff8420d82e03806028060081e007f2017fdff7fdff7fdfc82e03806028060081e007f2017fdff7fdff7fdef7fa03806028060081e007f2017fdff7fdff7fdef7cdf8806028060081e007f2017bdef7bdef7bcdf48d45805cf8060081e007f2017cdf37cdf37cd2355d71801fb812009de006f2117d5f57d5f55157161ddf801ea80a5b906008020d7fdff7fdff7bdf37d5fd801fe7fe4d8de018020b7fdff7fdff7bdf37d5fd801fe7fe0781601802017fdff7fdff7bdf37d5fd801fe7fe007fa01802017fdff7fdff7bdf37d5fd801fe7fe007e601816017fdfd7f5fd735d977df7801fa7f6007ae00835fe7f9fe7f9fe779e67a9fa801fc7fa007ca0082201,
  0x7e5f97e60080200802008020080200802007edfb80a069360e8020e81e008c5e481e077fdff7fe308de0a8060a8160088dec816057fdff7fdef7fa02806028060081dfc806017fdff7fdef7ce0d806028060081dfc806017bdef7bcdf48eaa805cf8060081dfc806017cdf37cd2355e82801fb812009ddbc846117d5457d57161dea801ea80a5b906008360d7fdef7fdf37d5fe801fe7fe4d8de0082a0b7fdef7fdf37d5fe801fe7fe0781600802017fdef7fdf37d5fe801fe7fe007fa00802017fdef7fdf37d5fe801fe7fe007e605802017fdcd7f5d977dfa801fa7f6007ae0c7f9fe7f9de7f9e67a9fc801fc7fa007ca087fa01,
  0x1f96cdf98020080200802008020080200802007edc980a0283a0783a07802318027788e5b81dff7d5ff8120a8120a8160088e0095619906057fdf57fdff80e0080a0180207802118160d805ef515ef7be007c1cf8060081e0084605836017cd717cdf3801f37ee048027780321956dd845f57d5f57d5ea7d5ea80a5b906d0aa60da3e0d7fdff7fdff7f9ff7f9ff93637ac68f82e7982dff7fdff7fdfe7fdfe7fe07816118360182e017fdff7fdff7f9ff7f9ff801fe8460d8060b805ff7fdff7fdfe7fdfe7fe007e611835fc82e017fdff7fdff7f9ff7f9ff801f9801fc7f20b805ff7fdff7fdfe7fdfe7fe007e6007bdfc7fa017fdfd7f5fd7e9fd7e9fd801eb801cd7c5e47f9fe7f9fe7f9fc7f9fc7fa007ca00779f679a01,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0083a078023181e7796e4d792077fdff7fe0482e0082a058022381655906377b2057fdff7fdff80e0180a0180207806118360b7f2017bdef7bdef8020173e0180207806118360b7f2017cdf37cdf3802007ee048027784721b76bb6f2117d5f57d5f57aa007aa0296e41b76a9a3e0d8020d7fdff7fdff7fa007f9ff93637aea8f9e60b8020b7fdff7fdff7fa007f9ff81e058420d82e01802017fdff7fdff7fa007f9ff801fe8420d82e01802017fdff7fdff7fa007f9ff801f98420d82e01816017fdff7fdff7fa007f9ff801f97fdfc82e01816017fdff7fdff7fa007f9ff801f97fdef7fa01816017fdff7fdff7fa007f9ff801f97fdef7cdf6816017fdfd7f5fd7ea007e9fd801eb7f5cd765df835fe7f9fe7f9fe7f2007f1fe801f27f9de799ea82201,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b936158020e81e008c5e481e077fdff7fe04946418de0f8020a8160088dec816057fdff7fdff8460d82e02802028060081dfc806017fdff7fdff801fc82e02802028060081dfc806017fdff7fdff801ef7fa02802028060081dfc806017fdff7fdff801ef7ce0282e028060081dfc806017bdef7bdef800df48defaadcf8060081dfc806017cdf37cdf38012355df3a09fb812009ddbc846117d5f57d5f55417161ddf801ea80a5b906008360d7fdff7fdff7c1f37d5fd801fe7fe4d8de0082a0b7fdff7fdff7c1f37d5fd801fe7fe0781600802017fdff7fdff7c1f37d5fd801fe7fe007fa00802017fdff7fdff7c1f37d5fd801fe7fe007e605802017fdfd7f5fd741d977df7801fa7f6007ae0c7f9fe7f9fe7f9fe781e67a9fa801fc7fa007ca087fa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b9361581e0e81e008c600792077fdff7fe04946418de0f8160a8160088e007b2057fdff7fdff8460d82e03802028060081e007f2017fdff7fdff801fc82e03802028060081e007f2017fdff7fdff801ef7fa03802028060081e007f2017fdff7fdff801ef7cdf8802028060081e007f2017bdef7bdef800df48d457c1cf8060081e007f2017cdf37cdf38012355d717cdfb812009de006f2117d5f57d5f55417161ddf7d5ea80a5b906008020d7fdff7fdff7c1f37d5fd7fdfe7fe4d8de018020b7fdff7fdff7c1f37d5fd7fdfe7fe0781601802017fdff7fdff7c1f37d5fd7fdfe7fe007fa01802017fdff7fdff7c1f37d5fd7fdfe7fe007e601816017fdfd7f5fd741d977df77f5fa7f6007ae00835fe7f9fe7f9fe781e67a9fa7f9fc7fa007ca0082201,
  0x1f97e5f98020080200802008020080200802007edfb80a7296e4d83a0783a07802317920781dff7fdff952418de0a8120a8160088dec816057fdff7fdff7f20b80a0080a01802077f201805ff7fdff7fdef7fa02802028060081dfc806017fdff7fdff7bdf38360080a01802077f201805ef7bdef7bcdf48eaa7c1cf8060081dfc806017cdf37cdf348d57a09f37ee04802776f211845f57d5f55157161dea7d5ea80a5b906008360d7fdff7fdef7cdf57f9ff7f9ff936378020a82dff7fdff7bdf37d5fe7fdfe7fe0781600802017fdff7fdef7cdf57f9ff7f9ff801fe80200805ff7fdff7bdf37d5fe7fdfe7fe007e605802017fdfd7f5cd765df7e9fd7e9fd801eb831fe7f9fe7f9fe779e67a9fc7f9fc7fa007ca087fa01,
  0x1b37e5f9802008020080200802008020080200725fb80a028560783a07802318027796de4935f57fdff8120e8160a8160088e00956417b2377d5ff7fdff80a0080a018020780211835fc82d457bdef7bdef7c1cf8060081e008460d7f20b5c5f37cdf37cdf37ee048027780321b75bcaedf57d5f57d5df7d5ea80a5b906d0aa68f8020d7fdff7fdff7f5ff7f9ff93637ac68f9e60082dff7fdff7fdfd7fdfe7fe07816118360b802017fdff7fdff7f5ff7f9ff801fe8460d82e00805ff7fdff7fdfd7fdfe7fe007e6118360b816017fdff7fdff7f5ff7f9ff801f9801fc82e05805ff7fdff7fdfd7fdfe7fe007e6007bdfe8160184dfd7f5fd7ddfd7e9fd801eb801cd7660d781fe7f9fe7f9fa7f9fc7fa007ca00779e6821ed,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0783a078023181e7796de46ea077fdff7fe0482a0482a058022381655905ec73a057fdff7fdff80e0080a018020780611835fc7da017bdef7bdef801f073e018020780611835fc7da017cdf37cdf3801f37ee048027784721b75bc55a117d5f57d5f57a9f57aa0296e41b76a9a3e008020d7fdff7fdff7f9ff7f9ff93637aea8f9e6008020b7fdff7fdff7f9ff7f9ff81e058420d82e00802017fdff7fdff7f9ff7f9ff801fe8420d82e00802017fdff7fdff7f9ff7f9ff801f98420d82e05802017fdff7fdff7f9ff7f9ff801f97fdfc82e05802017fdff7fdff7f9ff7f9ff801f97fdef7fa05802017fdff7fdff7f9ff7f9ff801f97fdef7ce0582e017fdfd7f5fd7e9fd7e9fd801eb7f5cd7660c87dfe7f9fe7f9fe7f1fe7f1fe801f27f9de79a0885201,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b9360e8020e81e008c60788e077fdff7fe04942418de0b8020a8160088e05866057fdff7fdff8460d82e03802028060081e01816017fdff7fdff801fc82e03802028060081e01816017fdff7fdff801ef7fa03802028060081e01816017fdff7fdff801ef7ce0382e028060081e01816017bdef7bdef800df48e00aadcf8060081e01816017cdf37cdf38012355e00a09fb812009de11956117d5f57d5f55417161dea801ea80a5b9060d8360d7fdff7fdff7c1f37d5fe801fe7fe4d8de0a82e0b7fdff7fdff7c1f37d5fe801fe7fe0781600806017fdff7fdff7c1f37d5fe801fe7fe007fa00806017fdff7fdff7c1f37d5fe801fe7fe007e6007f2017fdfd7f5fd741d977dfa801fa7f6007adfd7c9fe7f9fe7f9fe781e67a9fc801fc7fa007c9fe7da01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029de5b9360e8020e81e008c5e481e077fdff7fe04956418de0a8060a8160088dec816057fdff7fdff8420d82e02806028060081dfc806017fdff7fdff7fdfc82e02806028060081dfc806017fdff7fdff7fdef7fa02806028060081dfc806017fdff7fdff7fdef7ce0d806028060081dfc806017bdef7bdef7bcdf48eaa805cf8060081dfc806017cdf37cdf37cd2355e82801fb812009ddbc846117d5f57d5f55157161dea801ea80a5b906008360d7fdff7fdff7bdf37d5fe801fe7fe4d8de0082a0b7fdff7fdff7bdf37d5fe801fe7fe0781600802017fdff7fdff7bdf37d5fe801fe7fe007fa00802017fdff7fdff7bdf37d5fe801fe7fe007e605802017fdfd7f5fd735d977dfa801fa7f6007ae0c7f9fe7f9fe7f9fe779e67a9fc801fc7fa007ca087fa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560083a07802318027796de4936077fdff7fe0483e0182a058022380255905ec8de057fdff7fdff80a0180a018020780211835fc82e017bdef7bdef7be0173e018020780211835fc82e017cdf37cdf37ce007ee048027780321b75bcaee117d5f57d5f577e007aa0296e41b42a9a3e008360d7fdff7fdff7f6007f9ff93637ac68f9e60082e0b7fdff7fdff7f6007f9ff81e058460d82e00806017fdff7fdff7f6007f9ff801fe8460d82e00806017fdff7fdff7f6007f9ff801f98460d82e05806017fdff7fdff7f6007f9ff801f9801fc82e05806017fdff7fdff7f6007f9ff801f9801ef7fa05806017fdff7fdff7f6007f9ff801f9801ef7ce057da017fdfd7f5fd7de007e9fd801eb801cd7660c781fe7f9fe7f9fe7ea007f1fe801f2801de79a087aa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560783a078023181e7796dba88e077fdff7fe0483a0582a058022381655905ce866057fdff7fdff80a0080a018020780611835f6816017bdef7bdef7bdf073e018020780611835f6816017cdf37cdf37cdf37ee048027784721b7556956117d5f57d5f577df57aa0296e41b76a9a3e008360d7fdff7fdff7f5ff7f9ff93637aea8f9e60082e0b7fdff7fdff7f5ff7f9ff81e058420d82e00806017fdff7fdff7f5ff7f9ff801fe8420d82e00806017fdff7fdff7f5ff7f9ff801f98420d82e007f2017fdff7fdff7f5ff7f9ff801f97fdfc82e007f2017fdff7fdff7f5ff7f9ff801f97fdef7fa007f2017fdff7fdff7f5ff7f9ff801f97fdef7ce0b7f2017fdfd7f5fd7ddfd7e9fd801eb7f5cd7661e7c9fe7f9fe7f9fe7e9fe7f1fe801f27f9de79a147da01,
  0x7e5f97e6008020080200802008020080200802007edfb80a029c25b9360e81e0e81e008c5e481e077fdff7fe04942418de0a8120a8160088dec816057fdff7fdff8460d82e02802028060081dfc806017fdff7fdff801fc82e02802028060081dfc806017fdff7fdff801ef7fa02802028060081dfc806017fdff7fdff801ef7ce0d802028060081dfc806017bdef7bdef800df48eaa7c1cf8060081dfc806017cdf37cdf38012355e827cdfb812009ddbc846117d5f57d5f55417161dea7d5ea80a5b906008360d7fdff7fdff7c1f37d5fe7fdfe7fe4d8de0082a0b7fdff7fdff7c1f37d5fe7fdfe7fe0781600802017fdff7fdff7c1f37d5fe7fdfe7fe007fa00802017fdff7fdff7c1f37d5fe7fdfe7fe007e605802017fdfd7f5fd741d977dfa7f5fa7f6007ae0c7f9fe7f9fe7f9fe781e67a9fc7f9fc7fa007ca087fa01,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0083a07802318027796e4d88e077fdff7fe0482e0082a05802238025590637866057fdff7fdff80e0180a0180207802118360b816017bdef7bdef8020173e0180207802118360b816017cdf37cdf3802007ee048027780321b76bb956117d5f57d5f57aa007aa0296e41b42a9a3e0d8360d7fdff7fdff7fa007f9ff93637ac68f9e60b82e0b7fdff7fdff7fa007f9ff81e058460d82e01806017fdff7fdff7fa007f9ff801fe8460d82e01806017fdff7fdff7fa007f9ff801f98460d82e017f2017fdff7fdff7fa007f9ff801f9801fc82e017f2017fdff7fdff7fa007f9ff801f9801ef7fa017f2017fdff7fdff7fa007f9ff801f9801ef7cdf67f2017fdfd7f5fd7ea007e9fd801eb801cd765df7c9fe7f9fe7f9fe7f2007f1fe801f2801de799ea7da01,
  0x7e5f97e6008020080200802008020080200802007edfb80a0283a0783a07802318027796e236ea077fdff7fe0482a0482a0580223802559061973a057fdff7fdff80e0080a018020780211836057da017bdef7bdef801f073e018020780211836057da017cdf37cdf3801f37ee048027780321b765555a117d5f57d5f57a9f57aa0296e41b42a9a3e0d8020d7fdff7fdff7f9ff7f9ff93637ac68f9e60b8020b7fdff7fdff7f9ff7f9ff81e058460d82e01802017fdff7fdff7f9ff7f9ff801fe8460d82e01802017fdff7fdff7f9ff7f9ff801f98460d82dfc802017fdff7fdff7f9ff7f9ff801f9801fc82dfc802017fdff7fdff7f9ff7f9ff801f9801ef7f9fc802017fdff7fdff7f9ff7f9ff801f9801ef7cdfc82e017fdfd7f5fd7e9fd7e9fd801eb801cd765f187dfe7f9fe7f9fe7f1fe7f1fe801f2801de799f685201,
  0x7e5f97e6008020080200802008020080200802007edfb80a028560783a07802318027796dba792077fdff7fe0483a0582a058022380255905ce7b2057fdff7fdff80a0080a018020780211835f67f2017bdef7bdef7bdf073e018020780211835f67f2017cdf37cdf37cdf37ee048027780321b75566f2117d5f57d5f577df57aa0296e41b42a9a3e008020d7fdff7fdff7f5ff7f9ff93637ac68f9e6008020b7fdff7fdff7f5ff7f9ff81e058460d82e00802017fdff7fdff7f5ff7f9ff801fe8460d82e00802017fdff7fdff7f5ff7f9ff801f98460d82e00816017fdff7fdff7f5ff7f9ff801f9801fc82e00816017fdff7fdff7f5ff7f9ff801f9801ef7fa00816017fdff7fdff7f5ff7f9ff801f9801ef7ce0b816017fdfd7f5fd7ddfd7e9fd801eb801cd7661e835fe7f9fe7f9fe7e9fe7f1fe801f2801de79a1482201]

/-- Signed 10-bit entries, biased by 512 and packed row by row. -/
def coeff (c : Fin 198) (i j : ℕ) : ℤ :=
  if i<count c ∧ j<count c then
    (((((coreWords[c.val]?).getD 0) >>> (10*(i*count c+j))) % 1024 : ℕ) : ℤ)-512
  else 0

theorem bound (c : Fin 198) (i j : ℕ) : |coeff c i j| ≤ 512 := by
  rw [coeff]
  split
  next => have h := Nat.mod_lt (((coreWords[c.val]?).getD 0) >>> (10*(i*count c+j))) (by decide : 0<1024)
          rw [abs_le]
          omega
  next => norm_num

private def horner : ℕ → (ℕ → ℤ) → ℤ
  | 0,_ => 0
  | n+1,f => f 0 + 524288*horner n (fun i => f (i+1))

/-- Signed base-524288 representation of a catalog row. -/
def word (c : Fin 198) (i : ℕ) : ℤ := horner (count c) (coeff c i)

private lemma horner_eq (n : ℕ) (f : ℕ → ℤ) :
    horner n f = ∑ j : Fin n, f j.val*(524288:ℤ)^j.val := by
  induction n generalizing f with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

theorem word_eq (c : Fin 198) (i : ℕ) :
    word c i = ∑ j : Fin (count c), coeff c i j.val*(524288:ℤ)^j.val :=
  horner_eq _ _

end CriticalConicEvenFinite.Catalog


namespace CriticalConicEvenFinite.Field131

/-- Consecutive 8-bit entries in a compact matrix row. -/
def digit (w j : ℕ) : ℕ := (w >>> (8*j)) % 256

def fromRows (n : ℕ) (A : ℕ → ℕ) : Matrix (Fin n) (Fin n) (ZMod 131) :=
  fun i j => digit (A i.val) j.val

private def radix : ℕ := 16777216

private def encode : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,f => f 0 + radix * encode n (fun j => f (j+1))

/-- Spread the 8-bit entries into 24-bit lanes before forming dot products. -/
def widen : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,w => w % 256 + radix * widen n (w >>> 8)

private lemma widen_spec (n w : ℕ) : widen n w = encode n (digit w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [widen,encode,ih]
    congr 2
    apply congrArg (encode n)
    funext j
    simp only [digit,show 8*(j+1)=8+8*j by omega,Nat.shiftRight_add]

private def sumUp : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,f => sumUp n f + f n

private lemma sumUp_spec (n : ℕ) (f : ℕ → ℕ) : sumUp n f = ∑ j : Fin n, f j.val := by
  induction n with
  | zero => simp [sumUp]
  | succ n ih => rw [sumUp,ih,Fin.sum_univ_castSucc]; rfl

private lemma encode_weighted {n : ℕ} (k : ℕ) (a : Fin n → ℕ) (f : Fin n → ℕ → ℕ) :
    (∑ j, a j * encode k (f j)) = encode k (fun i => ∑ j, a j * f j i) := by
  induction k generalizing f with
  | zero => simp [encode]
  | succ k ih =>
    simp only [encode,Nat.mul_add,Finset.sum_add_distrib]
    congr 1
    have term (j : Fin n) : a j * (radix * encode k (fun i => f j (i+1))) =
        radix * (a j * encode k (fun i => f j (i+1))) := by ring
    simp_rw [term]
    rw [←Finset.mul_sum,ih]

/-- Check every output lane against the requested row of the identity. -/
def checkDigits (row : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0,_,_ => true
  | n+1,offset,w =>
      (w % radix % 131 == (if row=offset then 1 else 0)) &&
        checkDigits row n (offset+1) (w / radix)

private lemma checkDigits_sound (row n offset : ℕ) (f : ℕ → ℕ)
    (small : ∀ j < n, f j < radix) (checked : checkDigits row n offset (encode n f) = true) :
    ∀ j < n, f j % 131 = if row=offset+j then 1 else 0 := by
  induction n generalizing offset f with
  | zero => omega
  | succ n ih =>
    have small0 := small 0 (Nat.succ_pos n)
    rw [checkDigits,encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small0,
      Nat.add_mul_div_left _ _ (by decide : 0 < radix),Nat.div_eq_of_lt small0,zero_add] at checked
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp checked
    intro j hj
    cases j with
    | zero => simpa using beq_iff_eq.mp head
    | succ j =>
      have h := ih (offset+1) (fun i => f (i+1)) (fun i hi => small _ (by omega)) tail j (by omega)
      simpa only [show offset+1+j=offset+(j+1) by omega] using h

/-- Verify a row of A times the candidate inverse, checking all integer dot
products simultaneously by carrying sufficiently wide lanes. -/
def rowOK (n : ℕ) (A B : ℕ → ℕ) (i : ℕ) : Bool :=
  let w := sumUp n (fun j => digit (A i) j * widen n (B j))
  checkDigits i n 0 w

private lemma row_sound {n : ℕ} (bound : n ≤ 256) (A B : ℕ → ℕ) (i : Fin n)
    (h : rowOK n A B i.val = true) (k : Fin n) :
    ((fromRows n A) * (fromRows n B)) i k = (1 : Matrix (Fin n) (Fin n) (ZMod 131)) i k := by
  let f (s : ℕ) := ∑ j : Fin n, digit (A i.val) j.val * digit (B j.val) s
  have w : sumUp n (fun j => digit (A i.val) j * widen n (B j)) = encode n f := by
    rw [sumUp_spec]
    simp_rw [widen_spec]
    exact encode_weighted n _ _
  have small (s : ℕ) (_hs : s < n) : f s < radix := by
    have le (j : Fin n) : digit (A i.val) j.val * digit (B j.val) s ≤ 65025 :=
      Nat.mul_le_mul (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0<256)))
        (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0<256)))
    have total := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => le j)
    change (∑ j : Fin n, digit (A i.val) j.val * digit (B j.val) s) < radix
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
    apply lt_of_le_of_lt total
    change n*65025 < 16777216
    omega
  unfold rowOK at h
  rw [w] at h
  have hn := checkDigits_sound i.val n 0 f small h k.val k.isLt
  simp only [zero_add] at hn
  have hz := congrArg (fun t : ℕ => (t : ZMod 131)) hn
  simp only [ZMod.natCast_mod,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at hz
  simpa only [f,Nat.cast_sum,Nat.cast_mul,fromRows,Matrix.mul_apply,Matrix.one_apply,Fin.ext_iff] using hz

/-- One true row check per selected row supplies a right inverse over F₁₃₁. -/
theorem injective_of_rows {n : ℕ} (bound : n ≤ 256) (A B : ℕ → ℕ)
    (checks : ∀ i : Fin n, rowOK n A B i.val = true) :
    Function.Injective (fromRows n A).mulVec := by
  let _ : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  have prod : fromRows n A * fromRows n B = 1 :=
    Matrix.ext fun i k => row_sound bound A B i (checks i) k
  have det := congrArg Matrix.det prod
  rw [Matrix.det_mul,Matrix.det_one] at det
  have regular : (fromRows n A).det ≠ 0 := by
    intro h
    rw [h,zero_mul] at det
    exact (zero_ne_one : (0 : ZMod 131) ≠ 1) det
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr regular))

def batch (n : ℕ) (A B : ℕ → ℕ) (offset : ℕ) : ℕ → Bool
  | 0 => true
  | count+1 => batch n A B offset count && rowOK n A B (offset+count)

theorem batch_sound {n : ℕ} (A B : ℕ → ℕ) (offset count : ℕ) (check : batch n A B offset count=true) :
    ∀ j, offset ≤ j → j < offset+count → rowOK n A B j=true := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨prior,last⟩ := Bool.and_eq_true_iff.mp check
    intro j low high
    by_cases h : j < offset+count
    · exact ih prior j low h
    · have : j=offset+count := by omega
      exact this ▸ last

end CriticalConicEvenFinite.Field131


namespace CriticalConicEvenFinite.Catalog

def packDigits : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,f => f 0 + 256 * packDigits n (fun j => f (j+1))

lemma readDigit (n : ℕ) (f : ℕ → ℕ) (small : ∀ j < n, f j < 256) (j : ℕ) (hj : j < n) :
    (packDigits n f >>> (8*j)) % 256 = f j := by
  induction n generalizing f j with
  | zero => omega
  | succ n ih =>
    have small0 := small 0 (Nat.succ_pos _)
    cases j with
    | zero => simp [packDigits,Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt small0]
    | succ j =>
      have first : (packDigits (n+1) f >>> 8) = packDigits n (fun k => f (k+1)) := by
        rw [Nat.shiftRight_eq_div_pow,show (2:ℕ)^8=256 by decide,packDigits,Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt small0,zero_add]
      rw [show 8*(j+1)=8+8*j by omega,Nat.shiftRight_add,first]
      exact ih _ (fun k hk => small _ (by omega)) j (by omega)


end CriticalConicEvenFinite.Catalog


namespace CriticalConicEvenFinite.Catalog

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1500000 in
private def inverseWords : Array ℕ := #[
  0x506227240d730e402411385d4d504b075f0000000008684f00380024384241820000007b1b344b00005f517d1a2b790041,
  0x453c463f025e4676473d4481253d13047e722d5235707222350a4d58132c3774686d357f12734b722f1c3e541d0d2a0913,
  0x132130c4263311081700a4f5c2e07202d093b10821a1d2f14702c4b0a0f000000007358,
  0x1f281c5c2a390b4f2e6e451c053f1c30563a81107626632724501d6a1477743f6e3c5b1f281c5c0b3e2b542d612650255e,
  0x7c6a54154f317f734d3b527c1e611d781d07016c3d40001a000353050000000b536607000000001a6c57000000006c7a19,
  0x45334c1f3b355669281c1b5d2055133e4e37153f65735549102016410766152b42694e0f7d2d301a5e0d0000000f61004b,
  0x303f65232a250a6404610a28014152571f7c58322b2e6c24192923827857527c194e3519,
  0x3e7920297818730f24826c7a0c514d434b075f00000000000045714b7a41007e003e1200414200054b4142010000000000457100285b007e2b51242707720070,
  0x3a2b1f10076e285765815864737c155b2c1e206e25047d6c47465017421750231a452a704b7a27630223701e0c6c416c692a693e591338095c20677a1365777634641e1440722d135d787f4a1053367c0f,
  0x5a7d2e08272219701459147a684c594356127c6b0e1d387c78223f0547695512375c4f75156f4b2a0b612a153c1a2e715e1f556c040829260000000000007937,
  0x38517c4b594e0f14546946453b37205c6d4f340f782b411d3d7d0143237624541773123d5940755e036b2677470c1c2f291572775d7b763f633d461b436f786946241a55305e245411372f721413312f35,
  0x7d396359761581237b0a324972700542765a0b0f230856432e721b0f001c79171764501f78004b0b106f2e46712500690e7d3d01366b0000000000646b165400000000000032757f0000000000006c7a19,
  0x81561290472424539755c61406462402f140f790a2352750a7e415a0c78773a3d21727c5f0073002b5643005039237670697e7e051b102a3f52084625066f6e7d7a073730444a73000000000069180001,
  0x3e55047a722a6a664e224f3508097200045e7510630d135935504c305c43674b7a7d1d17642a7802460333315f60475c257046275c357632022d6e50442e1146,
  0x268021430d33084f020563715a3b76003017540c56210a3d61713966663a2d4b37064111462c7425434a670b70094d294c7d427273210f5e0e7b586846581426,
  0x2c6d5411167a25054428754d224023260475338038187774313d631d6b0c0f485020662a6e5125234b295857242d386551,
  0xd0d105b335d7328125d367f7b654d044b075f00000000006a44611f417a0054193f222c7a09002f3842418200000000193f222c1172002f4c3c7c082752006c,
  0x7d0538195f660027703e7e4b6a241d005c135d33596e6b623e5c4e5835552c5257458178237c7206310e00435f6007117d053f00402458355546385745817803320a7102765408543b6c80011e2e002173,
  0x224162744d820d78726c4709266c5024633a176a352433517e691b7862583d17016d75683722554d0e0c815e034c612e2c7f770225807862722317016d7568256f51310600625868000000000000007937,
  0x70166e292a02073011268147661a75487d172032787a560d5a170f1c822c29657a1c0e7e79282b2b0c7b15042b82167f7d1f77086e084c016d04066425383805331838422a623f022581806f5a64434681177319200e314032615e6261044480373b087a,
  0x2f3d2f5522300025570a7f026b24077143786d3f6d0f5208767f2c72610e2a00575d4f5c0b7a024803006f640476120874744500406d390626342f1612000b4a1a6f15060e390000000000007367473d0000000000000002632f000000000000006c7a19,
  0x3e153a5150520a61353c4611196b190679697f43350b297636717e5548097f114615014b6e4a0c56231d28044e743952160a480c3837394c071975543f73192e120d2b6669592a3f7180751354102335042e5d4941505a317c2a741f1d211466526c550b413d653017060c106f1a000000000000005b2f003e,
  0x575d04636e4910361c2e25607f5d3b21043313780d226400467f0313585f118050714d364118205868554f426e54604f36201b62025933327d475a5e6931327c414808182d12315443774a0b086a1569052e475735547c214d390a5c0b2b6a255b5a1773,
  0x69501f6800487d41804200704b70796b01173017520f767a3230015219510e56666e0e825b292f5444717423690141412d180107187f79796d20305e1a33641b0045665b4561192c4c1f005d190e157b69501f68003e68603e224f1d3e4d006f593e7c44,
  0xd2f6e3d6b7e7000424d731c74183e633b503e6574025a207642632572785567787d2e1146701c7f25260c2462751e4919780280131c0e653a6a0b493b7067545256702a2f5d11270d2f6e3d4e3408684f,
  0x6a201c7e545b494f722e80075f2b280d6116282c605a78553b0b38540d74086b665b7c8163145332804a285a68206f305139035b291b7f447d701946532c32631453324a76325a684a346f0e6a7455671f,
  0x42620a397321304f49227d11656f5a63763e08176a1b4b110a7e3f110c42218179054468814162020a7e3f1b0e362181446113661e1429206053167836245149,
  0x3a2b1f177c752857658158646c070e5b2c1e206e258106664746504b7a27658125701e0c17421773603d452a706c416c1059103e591338095c041c5e136577763464326f54722d135d787f5a7363367c0f,
  0x356d6d41353707497d163e12192f143140225238384f4f6a1e8258715d0c430b331f006511201f403a4c081d57151d53534a49377b19796e663030393a4c086a001f1d53534a4078367e001e726364430b25807c002a0154261a00000000000000007937,
  0x811f2d2e01007f825e0b38710c0b0142177c216204073a6456558200040125784b2e482c60817d0f49375c123c8266081a3f135059065b47011d71734470332a7d283c8266121c33135059065b1d173b2f4b1e3a5e477c0d6e46505e1f2a09143f68571a7946397600340d4e3c05333d61062800665b5c1b2b,
  0x673a407879157d0371152e5e20437d2e13781a7c2e0f487634260a087c111f002c701851776563815700636d13033e2b242a2400323609700c73716481004680744c4876057f00000000000079620e74000000000000005e4471000000000000006c7a19,
  0x21604e4a394279332c311035826c731071471e78446b6f2a7112717c320456062c363e212e552a0a330b54205b0b7b3c4750542640816c6f0d0e34500f090f1e517e677b4863202d3b5f5c3d5f371d82245f6e0b30195a7b423d191172016f3b1b6c4566827a3e4549707f501810000000000000000f61004b,
  0x495b6f187f1a263469085d8058016f4156262609665b1c696552202043572c04101764582f666a190037711927335b2d2c413944063d4d58522d310a3510714d494517445c2804515a0814551a6d48271834027e11542a0257187d3a114e1530637f815134371e0f550f826e7b8241350d7049644931626f200402324f4c65743a68011531582c3423647e25793d1646,
  0x204d3c59822e69677a80080d3647032a28694477220c3447105c385e3f544f58654a7d1959743b072e085e76645e0d4d57657248541f5a5859731a4942335b5670762f54251b71418217505d1b0807163c630f1f1d7b26347e630c246755675b6336472a01551a26691c3a13463e2179067519262b1d5630204d3c59822e695d651c49704017782f815c4f2a53390f5d,
  0x1374126b0207416f37303a6526294a57594a7d1c3c017a25002e22077d6a5a5d66333a1d112d28511e76607a514263485a2469501c2e5d781827465f1f477e65705d8169052575484c3e4e6130352240026d36462c7673184e614381164d3d1f45106b327e067b582e73660f406e6a448004576c7d677c6368,
  0x2b067e4e79820a5a027267393a1580155750557c663b5c3829682e5e47257575494b53802b6647786c6809512a2c62097d060c5f2f5a041640222e3a1d6a5a80773d7c3f0d211a6b0134356f170744766269184a044e146c6967431d036f326c4b262f7c3f0d211a6b39654f6f171c0a4f821b463a12305028,
  0x24214e7b431611091033367464375d6076657415290a7d405b017c042a2d161b422d695e5f3a29224105775c7b4734781b3a446a3c0e162c0c397f743f1947756d1f2c4a040f446a3c0e16640a037f74357d5d3d0c7b7976140929724314645173540d10,
  0x4c4a5604113a5e59276e4141664d366d05114f304229706814776234307a2d82030f3a316626220f6a7533214c402534535f190e50626d0d5e4f30246a753321166c2f34535f4d6a3f3f3c2e3d214071190e50626d1760433024496d183c4c0734435d25,
  0x6c4d463f09226c2a770b293d421f062e45154510370405523129740f157f4602525a0f6a78043d81525a0f6a6c103d816d0b1c49421f062e631040052b2e6878,
  0x3257562c1c03081961646b566c404b8168447d6c251b6c685a1307470371806d527238754773286174151065693f4c202d5d0f6e73546744376356267415102f12494c202d5d806d6c58387547732861164a7d611a3b6236554400000000000000007937,
  0x377f001c2c79587068513442146f08772e73072256703d2901040067570a2b131b324f41597b0f3b5872215f550d6724265007176525752b5573123d5d337c1f6b5e0e582e107146265007640e2f752b5573123d5d337c1f756002582e107146392b656c3826345d59195580614459122d70067867606b204734001d538223745974330668660048397c721a63605f32,
  0x5f017d1b357e80664670320c1a180b39710a79062d32190f225c3028245f4a1f316b0032505a19363c4d123f5800731a727111347a5c275800730e7e7111347a5c273b00193c344b292c74413d0400235463191d0c2f164a0000000000000079555b0700000000000000001a6c5700000000000000006c7a19,
  0x26141e2b08476900587740084617546c2a093b425569292f1d5a0c4c09453d6f15752c2a382d516781691324125723447f09595f2c7061180a6f5a2e42265b1f2e5d27483b1c3c15212f3b2b086b4d321c391f22065142804c283c56100b4f1f14354b285a0480247b0e4708154800000000000000151f0069,
  0x825a216d60211916362246124a0f3b42796f803a4c6f6b7207675645471818197c4b70752456412d306142493e6f5234414612436b5b4158504812206c19490e7c5c1f2c1a046436430f196a51807d4249413c654f5f0d230e0d693c557576807972442a2b44771563583f4b171a1b71131b50787d4f682a0a113f59583f0c6e16354438813142573d42325348444110,
  0xd57085e250a6a2d3626592b5f30315a21623f076a7048606a56413d420380447950297e5652823c4f15255e592d2209502a502b082d0f6b183773586b323c5c6d5e504e71135a7811726850125f5965555a295757800e437a1a46584b22483b6c5c2d39566742761b5a43226133454e024d2d353f6829406122503e290b75004e4f6829406122503e350a2a564e441b5a43226133455a78593835342e4277790a74672a5a4a386481,
  0x54005c2c384f0d6975247d1d613864273a1d73465d331c123f4b5f033764523c6c1f02631c005c4e6d816f45192f415a7300652f637f571e6f372669630047276b381f1d406d1e270d00087d656e6e81210b750243000b55016633501d5052787c002428273077176d41365107005f5b5c530c6c617a4d321c0076666a46302968602e0d750048504e606b1f66126c57,
  0x3400534939393e38132778421f16382b01481d350c603b23412a714b0539022d103f10216b003a67004f3e092b082044801a005a1f00796358366d30146c70002349005f1d2d0b6331083475000c1b00754542316b0127195900244300311551515576563e4a00691c00558247477264713508007f67002e013c3c111f5d037b00041c005582474772711a1673007e1c00558247477264266622007f130035046d6d4462030e610011,
  0xc6f762254244e73465c263909733580751310652e263d81386e431d132b217e1836192b5502647d490f631a03691d5f2b09171c31493b69792b41250b0a63117c10445c11470e4f416e064b3e36387b5966176350555834246d6c5a6c637722332e2b4f5f1617744f200c6150555834246d6c0f1a7d7722358213296d1c2871813d33750974175b3f1b0b346c706e7d,
  0x7a06210b5b2025590761054e77532d1e3f5d7b7270526d235a5e257b074543016d10137a63566a3a0f483d54753b826d323760385b4b5803411f4a4265146e7c4b3b4f2651050f7923405a1e0a3c473e4b7d3036604329657947047d3806534d23405a1e0a3c7f6f657d3036246b82571d733d213c7d710c60432965794704145453534d340973524714244536536945,
  0x1a4a5061505673543155745621260c1f1b3c4e6f430f4d468264064b742e052e1325225476094608592936136449565b78753863193e14155a7321620928291d594a6e2910622142105a662a39155a7321624126761d594a6e29106221425d03702a3978094d5f3f25290e1e161830383926356675085c232c,
  0x87d4e37545e3e4e0840370746073d562836565d5c572617274761573823472d3c27653653342a351871671b79562006583d6b121c68407a637d2b461871671b43822a06583d3b36547b2c5b150a81741871671b43821e12583d234870265b316636295d,
  0xf29193255766d22373e0d624e0949363713731e534c6136295a6a512e0d16614c4576215625584509523347234b405155407e50441e6d7c0c2b5d112e430569096516077758267255407e1a70286d7c0c2b5d112e43056913670a07775826727959262212484d252b2f735d37190b4480293b6631761668437a44054a261852476522724c4453237d042532687a6b14,
  0x3617223d46394369442f7968421a2e0c45133c2456384237240f571141105533647b1c4338004a7752607c156835606d3c0031597e34084a26552b4d470052200f4f7b395d2e583647005220035b7b395d2e58363d00345145212b2c4647680d2100633d121455077f738121000000000000000079555b070000000000000000001a6c570000000000000000006c7a19,
  0x357a0213036d09546456503b3703307e75134f181a7e3e4e4607584e15202c10638010503f5b464f2a0a097a2842047442680278800e7868463f2a7d411b81177a750b1b3d44590667111e484a7572290b2a5a2e31254a2649147644313d586801742f7705070f826b4f431f6a710426065712257e461c0b29285d204a195b6b82097f4a00000000000000004d46007b,
  0x543925481646497b417a37767a457a0405031d593f164e78301d182e3d82204470225749816560693d18556732466c0c163b353519741d012b5d665a3b013f0b3a2e5f542c184b3f6b3d064637645e444c32796e572d2b706b07590b5b48646d343668524c570e252022781a81087f11762a46342b7a4c114f4d1b31372c755e162b0b694281015e2437301a75157022,
  0x20613c4f1f371c5f4b5820341f20423c33536a5609293406136e442c58371e2c305912520b771a1e493f253a06353678267d757e573e721a4a142e0c7d3e62183f0f516e5f2e4e19814d0d0b060b6c4b0608040f382e4a02157a2c266b68662d083245485b72473d624c1446363e353a1f53203b2f5b6c38417d5f6048236055087421376f3d4d454e495a3a63485428174b420624233b606e667b0f0f196e7b234f5f787a4a0a8043,
  0x5c006b344f502174077a691e242b3861571a100e636e3c22371d4d4b172e676c536b757460393563002d7c067e1412380a3c137e1c0076344f3652800a05487e0c3300700e762e7b36535256523b4b001a295a4f6b7c26592d022c4b001a1f6458614b2b622708675a00050b781b4b725a27493e2d80006d047f753f240522385e320300167f040e445f7e290025515a00050b781b4b724e33493e2d40007802817c61663d2d732f3c,
  0x3d00623955352940490e1f427e7238325a4c763b752a715b417d0c4b7273655b1f51100409000b4200410a1b3d7e1376077200341b00432c506f5d264c024600470b00250a2515641e490b7b003f56003f024512564a216744003642005b516b60156e597b71006d350053474c590c40016451001b4e00303c372a77434a57320068350053474c590c4d2d4539001a350053474c590c4039126b001b32003d6d5925536f3a58430018,
  0x3b007f821249442418367f7a42625d381b2408696a3b6a20813d4152234b6c6069545824012d064f005206001258277d522c360d3c0400224e00301b767e59083b210c1b00210d0008512d29117c27375c4c007a3500531b5a052a7b4862776800623b007f506d127f7c6c520246004742005b79314b195831140935007b190060185c5247356e0a5836007d6a00236b27313c4e1541634d0006190060185c5247356e420650007d4e00300c2e29655c7f1b5e0f003e3800693b75103167324c3e4a0012,
  0x400c6c27312482627241746c151f4d2d2c3528095e1c2f5d49255c2a6d301d377b467813355149815b4411534b42657f63427a551b526a36601c764f56164b19390167467534001d7711304e210a4a111d79036f387b0f5a227d4e155e3c6d64140414794f2a434e427f5f7647772c3a2c6b35755b4104240d3c0c57491f504e0e28017b3b690b6b58393f0a0267744104240d3c0c57491f6a340e288208481a78182b024a1e191c50,
  0x804c5a5e76454f445d143f1d15360c630d1564446f2d6e3639625d4710131439153314635d706b351e07647754497a786682374029795570814622780c0b472f5b594d5c0711133a4b416c083f632b4a5c37116e41640f676b4d722f5a210637421f741c1836111c61627d4c421f741c1836111c7b487d4c5a4e333e801a17403a426301350b7156375b787565021327,
  0x26196e1547160e0257466767292c5877110a3f5e31650c1e27593a37163651470072703c5b7b1c711d5a2208490a153e504201726569296c3934802651140c671e3e1b0e751e4d494b35056c13263004463d45255130794c495f55537f3d463e5e7d080a373a242e3004463d45250661104c495f55537f3d463e5e7d2226013a242e166f2b58305a595a74063331623004463d452506615d78535f554f534d365936532c506327271d,
  0x4364377c06190311823a172514576b3a5045077f55306c0a644b64502d2579762f1900542f020e733e322b454959070c803e1504096f1a3c2342566f68223a7e4f393f544139776f1b61490534127c2f424a0c1468223a7e4f713d1e4139776f1b6149053412465b4c4a0c1468223a7e4f713d28432d776f386d01582c4b7e3b594e3618496b0d601011134051122f7a,
  0x39171359546066387d04665b0f6b1a801c7b33200e8064237e5f690f5e7f4c6959815e627e71504a00503a693e38083f6d0f2c7178005e6b43537b044105300d3c0b00254e0a30087f427e53764778005e356f5d7b044105300d3c78005e356f5104044105300d3c09004228401d8039610b755214410028380b5d161a377b7f484500000000000000000079555b07000000000000000000001a6c57000000000000000000006c7a19,
  0x76155d6c743514152e4d4d323f67001d6d77087e5c784678270b036e612e63160f791f5800467a69247a20155450210d0b5d0a5d602a7636442e6f824b4317634423590d434955140138406c203f602a764046226f824b431763440b3d5b4a7b5103205e6c716119116b7a32257b5726204a2b2524162318316a014d231756301125692a3755656a282a5c7f3b637b747d432c17290d7d2b60792a0100000000000000000069180001,
  0x1759792832647c226e548242010c012070713437751b45034e7c396c475a343d5d782b114916032958473c7639727215821e7b4678593b69394105146705736f6e6f0801426b4982541a3f29264664372a76695e3e3d276032223a1e674b5d611a547c2f0b410244056f3b043a2a5e168204050a5b5c207455,
  0x461f300a792235435042687b4848064d1d660106520e3673776b682c4b6a190712562a583f03210927501c67117a012644647b0810773a41420a3980004e72496b166a2d4e364b2b6d103c732056421b1c671c4226053c2e1541283f2911097a534d2e675d05596a801763255e15344f7d210602651c5b7c047f427e1b383148195c036c205e256e4f343c2c7d811e6728077f044105684b1a736a277f76015d261c71786c747e5a12,
  0x30005a6943266e017f045b74773d7538480932771a29057b80391d095c4b027908544f550f7748121f4f15008024626b163134287c700b567f003a1a2f492c1454293521770300000052324627255b2b74406c631500170f5d18640832030351130d56003f083c4f3d523a51633428594d00803e4879287e77470e0a30025f008155302572130f486f7d201f360003453b0a5b050246757953812400022e535e117074034c0663644d00803e4879287e813d1a81300267000d2551572d5f7755637d363f,
  0x7f003a09401a003e4d1b302a42177238325c66697b78756c2410414d4d4b171e60000850447f2f49001f7600615a4a5f74362756674400361900602c7a010f392936568000280b00255a05400f5d1c40220b001c02006647596d6e025721261400273900196505586422811f7f7a007810001e5f061b005b240b645e000d76007b3e4d1300553a82305f000f0d0008453670002e494c0824007410001e5f061b005b1817645e000d76007b3e4d1300553a376179000f7d00574f60270029626a8260004a,
  0x4b001a2f51096014686e3342542a382e58422b8132000772414a464b3b7f734f253d1b0e6100685a006e35446d1a1f6b1024002c28004b355343662c187645008077002b2c31234512542e26003d78005e0538690d121a077200345f00814d185a361f056581007222001f33152e364b7867370044610064506e554d3856544c003f22001f33152e364b2d155100441100515b4c171b2c52245100631d00266d447c6418081147003a,
  0x5c006b5c027878220d461b15422e7a3841221545703b0375127c417d684b5a056c491e26734b5675005b0900281f17714f7f145e682c006b6d00397c643e60822e1f8237006510001e5f0d25035825154504006916004a3d6c4523015564014c001e54005c227f097b2d70116124001c16004a16671717261f52573e00790d00080d2b5b5b4c820f4c29002776007b7658282837013c6f5a005c1a00101a5633331546054f6d000c76007b7658282837013c0640005c690073692d50506e78015c310035,
  0x445101301c5c325d652626064246270e6d6b501b1d155750130341445024156b170c34114a0d4a7a007c2b1a5755494c613e6f457e0d00702977263a67583554351c605b00815040084f42374a384b135c3100095a0c5d3f262b4e2f4e67232800027c255954652b3f6a0c3e4e2100712b397a5c0a594a4637391a0b007d1a04595003427f187c6605100005697f2a338041046b07683373007e697f2a338041046b07684d59007e68105e3a0c0273607460057600136a6b792c71801876107c62700066,
  0x15820377053504516946238023010a4d770268416e294513237f125d81555c0d460e7343233f21270941218082572e42695261821d050b624c4658084e1f1553654419821f4304356e424178162f0c13633d780d0a2481205101265d2120036155784a735f57324e1837610576622a331068487f5f6b4c227e0d2159503b533b0424215c7538406619225772343c0f1837610576622a334816627f5f232a056f34015e20814867100e,
  0x446d407b51516e5f5a7d56122a5f003e487919824f266f70360b3b1a0e7a3c210d532d802b5180393e501d481726451379385a322169741a5b640e760b083c33327361357c21670d5a787b476b480c68130e160c78603f16223a177b121f4e1d1d651c6e771e05410871643566661e2f4d0c657e420871643566661e2f6775657e427b121f4e1d1d65541c446b0541266f52581a1a445d031a40093323556e13565608687561073c7d,
  0x2c6a3436026c60153e50435a427777541e03744e7b0f3f01680941421848314a0d4c2b5f06325b20004d3f33181454784d436276595600237e2902391c0b27136a0a7b55005e0c11266e3e403e7444821b39002b4d785b1d456a6c675a24450c0036360b28663e196254295f3e77004d4d785b1d456a21157424450c0036360b28663e19626e45293e77004d4d785b1d456a21153e504f0c003626202182616d1d12806a1473001b360b28663e19626e4533406b004d4e2d743c4b7d0806824f5e520035,
  0x3d5d61150a0a727a5d5b401c61185c30481908592977540d1d0e493e316009338034725a7b2f06424c09480f6b17634a6c7e1e0a4b5d5e603879302839017d7f584c1957222a45654a8206042b821f2c61593e1e39017d7f58011721222a45654a8206042b826c586b593e1e4a8206042b826c585f653e1e337d24180971085929776e300c0e2f4b1b261e2779563169,
  0x47174e233d691d7f29494a4d816f1a461f0c6463390d35232a15430f792111622a3049567e7d8024006b3b770a4b26684b6a3f5f3f00458277517b0a401d29657f44003e375932087943665a1e043f00454c205b7b0a401d29657f3f00454c204f040a401d29657f08000f2d517280404a27570a787400153f3d51163e3105554c4e00000000000000000079555b07000000000000000000001a6c57000000000000000000006c7a19,
  0xa4f03314a736d2e3a2a38020f3f563b416d7d1f3c442d5b79600a6363204269633d7e02146b0e702e1e31157b3b5203067039274245087f115c220936212e78223c1e093c627227612d1762550b6147657a4721115c2256622b2e78223c1e093c627227612d2164490b6147657a47217864760f22785d0118705c405806425e3813692b0e5179621e2043586858052624110721353c33362e25141b06621163575c745455281d7b48474a75232a192b4d77666934010000000000000000000069180001,
  0xc058217826e273e625153077d015e0582211e103a4702453013237c3631122957525d37673a2b0c2d1f0d68194c1e7f7d371a764d29623930292a807d371a6a5929623930292a800a68123a3e7d1b5e48526c7135745e614d7d335725223c441380355b35411d6e5e190c7846331019104a1f3806433a4a52380f300f3546764915267621701e601e6a096978424c6a,
  0x7a805b3f7b0038067b6c681a3c66551f1d216c7f512254447c05464d5a4e75224611035b626f502e686f44020b5421044773305053615b0453126918474873674e2f14423e1f7560091b5e7a2a742e100c3c5d711633196c05005656202f012550724f5f2a00633a730457151a6065507d002a04417f190833113424590020495b342c6e7f56371c0b0036604c0d6b80,
  0x204d3c3f4c51117d65065532015a417a280b226e64470c03753a1970626b2e5820587d2312447a1d7115143f4d1a33135c36307f104947363373701e32022a57390c4f48090c3d02624c2e3a2a147f181e18305a675b0d4500750c3b650b2809583e44313e34607b6c5d7f42455280100355160a59453f5331356d2e4b7c1e40596468236a6e0a6141025f2f802e6d792a3e443005181655380765432a1f1b601915796d7a8124540355160a59453f537e6b63384b7c1a26102b1d4a165e43361e717e0b,
  0x17007d196a546c6f007e570f62426a0a38753f4405636d8105602f5d410b174b142b582a372a02004f4547000e37001c2261554d3d1f003a314d004181001d2261554d80500028581a005a5d001b2361554d561200142c0d002d68004031520c801172000000000000520079810209217760007f604c007a2e007732512555765600645941005e55000c51325e2e002f5564045a002655000c51325e2e0d230a1f2a4200252e007732512555005479577f29005d2e007732512555766079704d41005e55000c51325e2e002f0a2c6d740026000000000000001a6b005115210080,
  0x460021687d6e1d770d04555d42306e386c33676c534c4174375b414b074b796b222c1343350b7a4e000814004d2a0c44187e1b6d126a00736d003903471a4d2c21363f6d004b08000f225378340b6612155000192e00777f10521c1040337d34003119006070363a65270755792b00261e0059525b7a6a6149667768006221006f40576c260242112c560004620014432c175d81413a0c2d007f21006f40576c260242495d70000465002a312809192246110c1b00217d005724081c053b795234750038,
  0x4b001a073f0a487d2f134442442a382e710552475a34812d4131464b3b0b3f27772f207212000e790077827c79540336014c001e31000a243c3c0e10237d4400524100286711651508200361005a06002c771f275006497212000e81001d21237a333914443b004b6a0023556e546b316e234500771900602e152f185260153e000c510046275925532740802200291900602e152f1852602f24000c32003d5c2a5e3014492b7c0018,
  0x7f003a7c824c458141612967421d81381d7101803b5a317d253d41543e4b2c19003a032b11283562001273004b33151f654c6a495675005b140067324d622439251f640200760000004f51381641041c654e00116f001c0400215f4a5e641f81000d4700546b4c252e3a144a5c3100092400023f09662208753282370065250035202a53735440710a0300185e004e635930102f435d2e80006b5e004e635930102f435d4866006b110051802546434a07091942005f28004b460a1a6014723a443b0077,
  0x390003062b15480d282e5f73423608386c2a38522e7d0422302b416e7a4b1453201c0d7c5733776800625f005951482f0f0a0b0b7079002e03001770116143176e3f3b64004048004e391f5e78597e4d2d03005b80006c097c22406c1544481f00437f007929656630094808322f00485100572b44557b692f53723c0075470034680366450729393f6000593c004f1b801d3e7c5a127c23002a470034680366450736652048005847003468036645072971707a00596d00366c77747567486069070026,
  0x6b56722b356f20062a481f6f7578145c808046593709671c3f3b7151555220432749126b1e66217919266e376553045b7b4e205031172f7421013201272e6162136d101446450930394c55276a62216f5641340f62825d765c5522217016736f3d154b310d0759712e657d093569110001331c5b246e4c3b424e6e501f00665d697004557e152822812629001d261a137f2e056e2316025d5a00665d697004557e1560531826290019602d307282367381748223780071821441077418581e2c630127,
  0x707714358792c087e273b1e196d1b74397a4d2064161e2c50560d485b393f325a766163082c501f44034257281f0b708108453165236c1b28767b1c43594c0c3b761831144b0a653c5c1673742b731c27251a10327d550d4a287a5842350d2a6e0a434347054b365d6e462e240026061f1f46106d44784210093e6d2b4f64643d73163f0b413b2f451658341f1f46106d447842483a586d2b4f6767487d2928565062667200211364643d73163f0b413b49616358344c4c682301744273687d01300432,
  0x71003480373b74351c44754724113238104c3c5d476a153337566e7f494b4358792c5e6140766332124f3b0005560d702845031a401f3e732b007e762e4452303e396449200d1400300d062a5a245e745462072a6c0051123f1d3f6d512f1933523771003480373b466e797f5a081e3712004f034c483d604204297b654c12004f034c483d605c6d297b654c71003480373b4623274c24081e3712004f034c483d605c375502654c3300474a80492f6a47041e232e427e001d15086f7d40544959523446,
  0x336960092c387a4d094b4701426780407c14271c663d63277e114153085d2a66302f267c17114171004c140180805853276846676563006a12133573236e263339520d4b0078317c2e4e162931085612263a00775d6362012204714a49455f3e003726202182617f5d713a3e2445004c5d6362012204267b63455f3e003726202182617f5d0856082445004c5d6362012204267b2d71693e0037552c1d0f7549223e4d4a627a00265d6362012204267b2d715d4a0037256b08635b6c761712130b03004b,
  0x39137972095a1378641b4f17431f1624312c393f601d6f45222c7e3f6b7a3c66747c5f46280e4c3e63345e46271b0c460753004a6c5e72713e7963580e717b7d45490270603d450a20613f1208063e3a811323463e7963223a7b7b7d45490270603d450a206149147f063e3a8113234655235e0d38510b4e1d1d26413922725b1871273c05590e1e08377a715f771b3b0f1377457b230259594772266f611231266d45360052023b60203b3d5b7c204e410b3a6370550000000000000000000069180001,
  0x291a3a78233b4c624a0d4a2c5364211e6c3e44577e72411e241c5b5846147a3d7015397e6424725f120f0b0e3b081640516f46777745777d4a1c063580163b32770c3e0c7f43677d4e036d48510c0c3e0c7f37737d4e036d48510c5300764e515a167830790a00817d1300500b175d34726f306717363f463b6e11212e810e037216826c782d5f685e047e38301b2528032f228220276645267e631a50065e4481404e4907320e4335,
  0x4143327b7b100950470d2f4f4d5b225441596c56761c7b6f29636028222b716a056b03116f7a1c24501d5c0621467f55220c5226374b1e3a301909112d46107e764c386555476a7a72563d73050d4f07660a75050a5b616c3911264c235c3f6c5b20076b2a715522800926535360364d6947564e3f4240510808737a3346536d7656385e216e6e2a284f567b3674034143327b7b1009503d7b4e0d2d4d1f1d353519377d7a2e5e5e0d,
  0x320c0924564f4f3b1b48207d50390e715144056f520d6e03384d71143a4d7f407f50592c3f5828603e3e3c091639076328793a19755a13531d68075d41724776176556803651483447732b8248496f59053c423c257916073e2931631d78573731274437274f06155c40303d1648482809135b51497546764f412e2e4e743a0a1301274353466d3b3b5b422528323a0e3d0d34425555350f7f43708278374a22176f6f423a74612b71,
  0xf006e8216637c7e6c268135696c23823850386c015f304205201747145f174b14562b5971073865793154662c6000174a216b2b0f467b6b1c6a221b4600212939246b291f5c075915404a43000b5f1a5d632d55625a5802478067000d492d2a3e07287d5252610a067100826a1a754d022577731c613d12390019650558340048260756402f4a5700726331182611447082018178664a006a1e7e2b4f0071277c2d4354392c001120526b5d723f5e3982020b1d3900196505583400125c8060402f4a570072633118261144254a6a1878663f004516283117433e512e40447219,
  0x740015146f3d12423622127b5842476e386c551c173d744955453b1a41705c4b021a7b2f3450040c2c5011004f790077334f36786529270c8158005d6d00394b3827316b564114546700184600214c385b5667303b812c1d003206002c0281137835746365052a005f5300294043265e5f233876187b003f150017671c62013f27293f374500802f00277013017f804e522b280a000d6e006c1c672182445264444c3e000354005c1370820403357c0d5b7900762f00277013017f804e07760e24000d6e006c1c67218244526438583e00034f006371123f0a0149302d3a440062,
  0x2d004442416000787009352042281a3810453e6d081569544268417c744b2f7f04397b792d260c7e00626f0002374c380f334160334d0059390019077c0a0f0672127427004a44003e2a5a770f57346a823700652f00272c57646e350e450854006d0b0025562d06643e11614865004076007b4d3670002e5540225f00672700181f643900582e6d001d00755c006b641f4a002b55613866000e0d0008364d1300553a376124001c5c006b641f4a002b5561524c000e340020552e4c00066b592328002e,
  0x4000782e821d5b5d152967421d593855420909780f6d6e6b412f224b39137b5d3317016f34003773004b1e24134981790a6900261300346d23121051506a4100240b00254a5c6256400c187900413c002f512d1f617a11253d003e4f00636e09016d1258823700653f0045212a5c6c431e0a03001844003e62592717402d2e80006b44003e62592717402d4866006b79000e01256a2713461942005f0f006e400a67076020443b0077,
  0x27001844027878225540760342134738542e391a72584a077c5341394d4b171148741c09673c142d00373b00654f7c3d5f0e6e3153170082750048584e3456121f503515007117007d3e0f1a7b7a56584c28004e0e003b61824f2d7164334e6e001275004817612b1a3b203c7b71006d530029073a4a4a3b2a517e570013150017577a73736d236b194c00326e006c2c0910101660631f370051150017577a73736d30147d340031150017577a73736d23204a6600322f00272d24404058601b7e57003f,
  0x1b00434b4679367d596e7a826042086b38566f025168795e15774e6e4128354b6d4c3b3c68104f001536380053420041806c0d050616712b531700821e0059185f59491d5c422b2574004565002a1e712a3a662741585e0f003e6d00392957100f22576307306c00011e0059650863491d5c422b257400455e004e0f7b1414084808186581007208000f5f2d1f10475e7b2d2737000907005f22176d0e0d5b0b511017003a7c0024616c16757628787d286c004907005f22176d0e0d5b0b064131003a450071114d7807486f0c803a41005e6e006c1d3e42595c78557d10240058,
  0x7f212082357468351313736d7427606234322b5a061669000f0b51545f002f52233815380770010b41082672203d61052c4a0709274c067c32383504305a0e12646b3882415624325b406c1835027a494e782c54514b4e08472975711f184b01422d81443f023f31122e340904426b70383e4c0e2c4f74224e0a220956582d78212c1a05091a802003631b55560b6257697e7a69032b3520682e5a6d4258340a12344227405e3668560b6257697e7a69032b4f06682e2916412b4f79714f7c626b404d5c,
  0x2c0c6911757f64074046270c1c514c2a7527226734361379110d01313d826a35530717266f722b007b5a0d58440515611a070a240f6d245c27564d6027700a5d7d6f6d552b4f716f2a3c184d5d60042f705e3122264a020a2b69074f5d7e6358646e092b0c68710433025370552b68665a6c3a3f21508130132e581b1d744f494462508130132e581b1d74692f446279217d0e1b780d57355d14391f60326e311d1b6f520d1b67030d,
  0x16624a14475d2e5a73581d4309107c6a432341597a66795e60735519261b2f52413381060b141e23102e6d5a67432474786b2c0f1c150b147b5a7e23645f7a5b621b1567230341692a0563455f714d7a043d6727042b090e050f6c81063d4a810c0d5e1969595d7c511d16264a284503775d6930077f4d460e6e3b6c4553417432436056257b72751548173e30420f1978232d5e08110e6e3b6c455341746a747a56257b72751548173e30420f190f3f7a5e08113d696273306d4458717e6e576428540e6e3b6c455341746a7444822f7b725e794e0e593406173e4e766e4e604a,
  0x4500134d490e4114552617055b423102386f4420204c3a1b6734117e4150744b01751a5579351379386d2d00020f0067231f433576274c2e0a33000b2100351d3e1c4a01184d77757000252d002227610b67225b5a14437700713500077614470a0f08717f2751003826005e322c154745237c02500c006b5d002551576e3c06150781337700185d002551576e3c062f70813377001826005e322c15477d54494f500c006b5d002551576e3c062f3a2a3d77001826005e322c15477d5449595200006b0f002c446b3c4521454a1f3a3c005a1900751a5b64714d576316710d0081,
  0x8115344a5d195a3b5c4171080a5941554e705821746124597d58316b01065f055825081d7e7f694c51746858485d57347b61737317561678174d7a486e29773c171b587a344c6c360971625a0c476c682b094f37174d7a121733773c171b587a344c174d7a121727003c171b587a344c18415568684662405b60815431670e3d1a6f09514c5a055d1c37307c6a427e0831744d116652555f52612039557e547c016864081c382f481e4e06452e125b203d496e4455433c190c075c2433407a0f3f1d2704,
  0x5c5f263f7d1b3a0e6f0360205f662e26130d1c2a65820e2b00580e437f6c810380195c7a512c233461576f036a014b2b155d031765074a6061793b3163076266314901393b4c220a48482a7c211d523a824a483761793b3b657e6266314901393b4c7134370c0c251260582877673c1957800a191a597f66710a7c80393443523b3565041c4615265f810e0c27245d44066849751407007c663d6755220f24642d2f7872445158265c5f263f7d1b3a0e6f7c4b3f1d46353b4c7e7736741c5b681f7f3a09,
  0x81524c0505284c312d713a78616b3f75391d2d193956052978817952365d22747445120d6552595e2f5358425f1e476c58102e15650d07117360310c3939560042780249583b131b2f2453522a3e497d226f0c7065335c4b4b4c525a28681174160f514c4c545173730405806d743237372f32105b347e035f233a5a5a413a1b801463712c1e1f1515251f54721b0a32,
  0x73037b6e153e543053003249692d71095b5b2811274f41540c5e7a716d4f19582b50344f1b282f3c67086636463c4726082c4320084b0f7478574d057e3b474c4b632e332e74505026691b7e0a6171391e445f74173730166d12137b676e3b0c08151d65504f342343426a0d1d514f1f34171a651e7e78430557072065054624230a79595b1c513f463c0a784f6c691e65050b4046647c631e7e3d5f60790a2a2867327a0747790b34171a651e7e78433d1f703a65053e671f414278025c0a7d452c4155,
  0x6c0006077614512168347e653b1a426f4e38307066277620755d0559385a4154014b4d0c2a483f4229750048100f00430600127e762e44536e3a004c2e7d004e08000f551f11660072010033371b002a0e003b814b5c5417806300474a3500616a00231d43401c4548730065255c007243000b7a817c4979735e004e3d3100121c00765e322c15265708000f2f55004a4c004d447552392208002e074843007f67000d2551576e5d62450074542e00393700363f0e314a617b4b0a7c3b4000041c00765e322c1526213e79192f55004a4c004d4475523922083879706243007f67000d2551576e5d62450a6a602200392300523480373b08320c0058053e0018,
  0x17007d70192f171857057f596a42530a3875403f7e2068117e6378494181174b14562b594c031b00243553003237001c44222e3673810039493700650200663f61554d002f00042352007a2600683e61554d37610082182d00231b004371520c80223a003a310a004231000a770209215a160052806d000c55000c265125553966002e4b1a005d2e00775d325e2e261655254b1a00472e00775d325e2e4a130a553869002655000c265125555d6d79133869003c2e00775d325e2e4a130a494469002655000c265125555d6d7913524f003c000000000000003b06004e5d1b0041,
  0x3e00125c2747086c2c69401142407438154d2433357238618022413f094b5c5d380946281f3c46500004160030344e744170395d2b7c006f030016810270530a1564492e005e3e00122b590a17581d0e3c6a006180006d0e756c2a1824473d33007f3c002f335012134328181c20003648000423604a3c3422375675005b64007a552e1e7f6d13586912007b1f00092e556504167076527100081f00092e5565041670766c57000848000423604a3c3416435675005b380069641f2b03727d170576003f,
  0x3300706a517a57376e124b426742256c3806004f2f0e601c213b4268417c1c4b0d19665d1e6f7c50808237006551002c0063273b31766d123f480038460021636580757c6144570f5c00393d0062566b030e07223f2c7427004a64007a062c2f725f271e50247400204600212d0e07757c6144570f5c003937003636260e1a0c4446313a550025480004582d7e5c10165c0c415d007472003234680366450729393f65002a1100514f1b801d3e7c5a127c1e0059610064684d0649070e1759356200121100514f1b801d3e7c5a121304005922001f1b367d3a7c752430763c002f,
  0x6d6d72233f742763056b44253d4228273e4424454a4c545167291025416d275b503c8248104f2d34164e2100715e274c0426314431593b1c4a7a007c681557574f195079646e6e172d00231b6e2c223e6a330a1f15156c5600600478245b79096e393504353562001268155761510d5079646e6e172d00237e2409561d3e704866150f823700654343164e58042a1a4c01312328000207073b66696a41223403152f4000567c7c481d1a1942614f80360943002d7c7c481d1a1942614f80362329002d1c1c690f1b1f81054d19222a3000515959272b1913033a5157566c560009,
  0x71171f7e017442621d122f512851740709823b2b38043f2a0d1c07657072103c7881225a195b085b4063283b31154f2569565d557c7c284b36671d2c38544c2976354b2a01760e546e380a6b4266165039004b764c2e4e28131240461b192262662725036c541d2c492d810d4c2726210452435c523a560276375c5d624769402731546f1e432746552a05337f3d4f492d810d4c2726213c005d5c526552084f596a6e682e1d7b1942,
  0x580a144d226d238250153337380a50117e216710390b37266f704207014654250a600d185b430d20233b512b0a7405423f8178787b475c4d5d148282025c47556b0b083c7a461b591582704322456d787b4720610221525f555e12406e3d5c231f7f6c30601d06681b5518145679394f3b6343447f1213254c5f78675d734820403f0471705e825c0b1c26104820403f0471705e8276741c26103b6343447f121325010d45315d7350152a46136f086e7f6b360c730a3509121e5355611a19446d614446,
  0x4500714a4b0a7d737b7b2d715d2b420a1a38101c45161e25780e5561012741825c4b021d76636b6e137d01342531007a6700765b347f1f1236555f5d6d46003e05007c593100322764187f36724200243600031a6770090f6f7444821b39002b5800224a174a4553183b0c64334000177e00072c5062243675786f082e440031580022402153371439555d3d311c001b2b00614362304c6f126626465267006858002240215337147103773d311c001b2b00614362304c6f12804210526700685800224021533714710341693b1c001b06002c34235c66795e7618456680002e2b00614362304c6f1280421a545b006821006f187f71253c262052481558005c,
  0xa00495973284881113c39015742791f38643326110c282b432c5f0c41720f4b597a6d4a2f5d47041e2320001b31003f801d48274c3f16227f2d005340006d385b150f56454a1f3a44002925001c7d056e7243105f7b4e6900136b00717f751922571770363f6e00654700567960162a71425734332500453c002d0a236d595d792c4f505e003e3c002d0a236d595d10124f505e003e4700567960162a26732481332500453c002d0a236d595d105f7b5a5e003e3c002d0a236d595d105f7b4e6a003e4c003964582a750150525b8001005f79003a2a105b704a4627607032004e,
  0x66472e550f4c68143c5c7d3158303e1410793358376d2604156e000976500b0e7e07353776506d77223e823d1517813b66242937193a30471567240f1f6a0d6a1762107a7c526e1c5f272e1976196c21730907311567245c4b740d6a1762107a7c521567245c4b68196a1762107a7c52263981404c62107502613e162f291f2a373a46602e2c75614e6c4c6b602433507a2179775f5c6812092b472b3251165e2749586462376d492a72602325270c5d113d3d6c5e1b54613d464a4e1837227a606d3937,
  0x4d368076144e4f62390624322d7c3270744f207900016c0a196131740d694a1501731e352f11180003621e49501d290c4c46237361430842576d4e02114c516b1e572a7f473a056c1204497237324e2f2c59043c497e17717f3a114c51354a612a7f473a056c1204497237324e392e4d043c497e17717f3a20383c2813361f777d57127001413e31300a295c573e6f213f702d6925467b087442648002611714487f3f1c0e364d030d6f3534214a7d692e6f49713e45124e0b383243335f2f52032d584d368076144e4f6239061a1d4c3a12176c7d6928191b41720c2746167424,
  0x343c1d342b0758265779640b73587a7e79464c232873316e270465667a0c6c14312069012d254c577a534e600513154e30714b1b706179734459527a353a1e416e706179675059527a353a1e416e14626c4b696a201c1073140d624052040a4c29231c374f423b081d683b1d5c522775357b195e2a537e4a533336506a5a4110813430053930504d3319290a28024f3d14613d3a2e496423121e088123791123666c1d51220e337f1d,
  0x5e7d220a756430375159026470754d5f2d824c640e761601724a540c3136634b793a1017583e821f4b09197228633e7f7b2b46784b5c02477a5c117e606a1a106068332d590572270b1b3371645c391c0c1f4f564040242e496064361e5c5146180c6f40541e1c577541706e6c34046d030c8011310e421315174f7f16482c0372525b243a475437691a347f2456347541706e6c34046d3b3d171131744f782b6125175b0a5802415c,
  0x67500d7d820b431f626c764372540416274a567026722736570d025c4721680f5a6c4f5f78405e72012a35341a307240203408195f474b0a174606440406493035646749557248213a152e670d0d55716b074a0c4802372e6f65232a5211237d1930406d7b780910411e4059646823604559723725725d08695d735866396d19564d576f72811d5f1c810b6f591e67316341086362451a26102b1d4a166a786e2c1411026624670278142a651c52560c7b20213e695d735866396d190b153d0672811d5f1c810b6f591e67312d77816d62453a734c6a6918272a4f100b207f4b7e,
  0x20003c0c774d6f274e0f62786619420c32383d4e350356781c173d2b29454155694b0a295a334167195d6763772500223000400f7469765018330a691747002c21006f8102743b425280735e4460007100000052324608411e4439097633000f63004781022d2278390f5036352c005a3b007f681b3823104655682c521f0075610064146f29362b2166144f2e0b005805007c3350622e36576a273c4412004a22001f6f145a4d58156a6f345578002b7e0007503321554d2c6411473f710039610064146f29362b6e190a592e0b005822001f6f145a4d58156a792a616c002b7e0007503321554d2c641161257100394900370b7810453f017075737d54003d,
  0x7100826c1854390723407b3230423b42385b35765f7a7d61562221724143084b2965785353828270693064000541000e22537865275c00000000000021006f42554b240e6d371b3d0700142f00273e1f452b077224016d6b00196d00390b3f327f5d173643625f00677c00242a35781c24336a530868006e2c001181740d4f612065153e14000178005e42665f0d263a55363c2f0000570072020f76342259286e456f00820b0025411d24765d497902475400000b0025411d24765d497902613a00002c001181740d4f612a5b2132140001150017056721820d20643d636c0080,
  0x32003d214f651f710521601f81427a78385e206910012a825e1b0d474113114b6b424e0e636b7f0408573e007961004a027f2f401e6300170361005a7a0041771a181f795114253562001209004242336b640a326f5e4e2100717200320c1c765d4546105d253d003e7a00414146221f7951142535620012720032730100807f770e027427004a4a006a604b08721f4c0c3b595300327f003a3758510865346218255a00300400494c2b327b1e4f2133132900530400494c2b327b1e4f21332d0f0053730065595a3e200b4d0c2e0215003c18002d3f7f265331512944253d006a,
  0x8000482b557573285c7c3c3a8242742d3812441b5c01684868100165414f0e4b291413350f76622237481f00433c001c1d11452d4f6863300a58005d39006c0662617e533b4a7a391e007c4a0017732b2205304839094a6500077400800c3d061651027a49285a006e39006c1064557e533b4a7a391e007c3a0062033b1a326340475a7522001b2c007b446b763c70267d60596600514f0045034c3f48526e387d215e004834003e8037443b31154b511725003b4f0045034c3f48526e4526024600474f0045034c3f48526e3832527800484d007577590a6941540c565e0f006a,
  0x160726251928291b3946792b66701a2a581e81221c0a28554d4b74562769083244414962020e322f123220534b5b57130e7a6f4b24515a2f6a7a641e63423d61823c1673424c3452166e707639800668543a0a596a7a64126f423d61823c1673424c810b42784b1435230c4411475e600a1b357c3b2a66266a2b052c407c670323487b5c37316334374e6d5f1c80603b08274c52201701351624670323487b5c3731636c68686d5f77140f5722023d156f4e7d341c5752265e7e751e81351c33306c1b44,
  0x30737e582b56317155187f2c0a485c66031f642303591e11136b5f217a00612162722b28311113064117324530176c3603807d3c795a2d0c5132400182804a4f0310297b2c4b4d561a10743c4b7560196932276e2c626c43402d7c8171367a6a51741d221b4b387042436c7f580377657704226d162c56073b6f2d280e790c7f61166d572d7c104c565b750a7704226d162c5607731d47280e79464014295a314235001f684b5d240c7f61166d572d7c10667225750a486b3a018281084c6c2567452f3c,
  0x6f001c787206741c127d4f0345094b113851556012691b296b360c0e3321804b04245b2f3c3a175a7d560d703b5500752d64721d1903250f2f21107d6300473f801d482a2b697c0d250c486d0039537b81394c7e12197a37330b490037606f5724331346276070411d78005e42665f5043391770363f71646f001c78720674714b57076b0603711400670b117d0f1200647c187d80121400670b117d0f12007e62187d80126f001c7872067471000557350603711400670b117d0f12007e2c440480120d00083546726c4e6050525b8039780900424d775969562f3c7f65606e39,
  0x4f0063752e4c212367581d4319304215093842634f4303097c46205c05734104634b612e06775f57236846676563006a71006803173e463c0237645b206800726c00061568336200246c71707880006406002c03551f6e1714812c3d3833000329007e1078343845554536392109005d750048615d5b0e793b1029244c74006b43000b0d6b175b59091111277709004b40007876186c282a4227725c0c7a003843000b0d6b175b5941422b277709004b40007876186c282a42410b260c7a003843000b0d6b175b59414278538109004b58002240215337262e7c17114171004c43000b0d6b175b59414278537515004b5300296c71326508280d6b3e1d7f005a,
  0x357e5380017e212f495d18630872625c776b40715e2d1e5e0577434c59414341254c593b0441700d245a056065103704211c406c0b63463644097f094b6c1a6c6f5d1710061074583a740e3817694d61266c737d730f2b490f754b6c1a3618671710061074583a740e3817694d6b2860737d730f2b490f754142281a7540567c0a2c304f04647e01043329286a60275c4f780b000e56036a1674056a2268673e0c6e096d7b4e053003820562543a2675801153414b1e1a127d1e406f566177325e693e357e5380017e212f495d0e4e2730426a79237d0279425e0f370f254f6001,
  0x1c0004513d76307e7d62301b1a581c384435542837790d7d1c6d2f4d134b2b420419622311287d1255070d003769124165795425496a3d510e00227c5a7439823c6a1374117d75006180330f4a014719700f720675006180271b4a014719700f72062d0013472d750d5000654459323d2000705d4b322e3e2d650768610242006758615b3923206b6e0c78645500571a730c7f37426452215f572e002c691077044c411f7c17242c35002d1b4053102a817e515d0d7827002b3463187b6e013630553b63,
  0x71182c1c0c5b307d1116672f151b690d125e674101037f050f6d17401d623a5d4e5b691f54722f5b7140034124055e20712f3e11083a5b3661157b18006b7d283f6166386c58226e08777718065b44221d4b172b0b153c320c460a1d0746013a6c2b6537601e52133f25560e7f2d4d520a4a5c82255f11253a3c4929190d667e64103f3479227b72502b7c4d1d051f73444f0a61085c6b5807360c733a197b726304291509171e44667e64103f3479227b2781457c4d78663877335c4928530861522662,
  0x330726154839392f3454764719306e0b4e4870127c5b075c0943680010707f5b2c662250771e1b6a40532f2d52092834575f3324686c5c70086f020f720d2f094c26682f3d6a552339202b1f0b7f201e5e273981337f632b78462f0d201a3943756273503c6d5d5a505e1663417d1225340243063a23235127045b24076e4f81407d496060322434285f7c150760481a216c6c3a360e4e134a7b340243063a2323515f357524076e7c233b69621717494d756b3a39084e03230957767624237f807d4c5f,
  0x811663045409060e003800155c3c70460160301382355c384b006e27471353137d2769210c1059003b390e573752566213221041101200011b67700972461429315233245f008120662a3380197a4053594e1531000a817b003d5c1d1040700b3e583c002f7f58035d7404462d1d320f0d40007876186c280a64005c546d104e3b007f1f684b5663142f4d4647713f43000b0d6b175b796a38272f167335480004641b382d206f07003d3c12443b007f1f684b5663147c003c51713f43000b0d6b175b796a3841151673355e004e74442c1a164b02190a77590a,
  0x5e004e5d26027e4b2f6e05274a7e4277473854066b67331618777e704c414158164b6420751a55223c21006f70470037760061374b286e657b5700724550000e4e00301d6645671d426e006c183e00602600684b391d2d472328004b685e001765002a3251716677393b007f6577000b7a00410c77595f686b030016224200055e004e5d26027e46193800694335000616004a3a493b3140822d2e4b3a80004f250035265d81053d1d15001a404e007d6d0039493a485243011e0a38490300345e004e5d26027e46666e7973433500066d0039493a485243011e0a522f0300345e004e5d26027e46666e79733741000676007b3d46726c77387100823a80000e,
  0x7e000765556b65674b313a3b224256143867676b6b7128715b135d2e4146294b153a463030774a7a366e33006a7f002064244d56826d706665810072120001052e697977574b0976450080710082311f1a0a0c2c387a0d3e00035a000559592a4b6f473c782f49001f120001525a737977574b09764500807200324a2f0d7b78164c39220b001c7500482f6b5a2f69452e2676450080580022044c6c047e7942035e02004c2b00617f37177f050a41485d810037580022044c6c047e794f2f3f6d004b580022044c6c047e79423b0c1c004c29007e73595c73142867327079005a,
  0x7a00417344337e3a365b13317808422e6a38232b060b5a16205c703d584341025a4b1f6839452e332d4f00153638005362007d205b692a40010a04580c1b00214d0080695038094e4d051d094f0e007736000350804b7a35367e667a3475000c4d0080337c42094e4d051d094f0e007754005c4308021620786d162c142d003736000350074d6e35367e667a3475000c0c00585f0a314b2e3e2d2e587808004429007e661975513810728265465c007f55000c7a475678310e2b63827d27003f2e0077093c2d0b527558204c3e5c004455000c7a475678310e2b63372b41003f6c00063d652b3c5a075738572f49001f07005f1b310421735902536d52770049,
  0xc1f1d4062720533750f81016d141656350e42817a54702274002757160e31356213047f2152118272183f1a533b5b1d415c662851275b0f4f0f1c65672f004064217c05760425267e1f526a215d1b426a3f027c4f0f1c59732f004064217c0576045a122c064327465a6b0b127e3f255e5a7615456b3d3e10426450355c7f4d22420b5d2a72084d2a04490404366141782659117b810e7f3a7f7b1744011637546158810b230f4904366141782659117b8128653a7f086c3f826d4c2f2266081d7b747b,
  0x1c78511417557c0245250f080d177429347c2021397b2c20625b6b4c20792962397c7a3177716b4874826d761b0c5d00430d753b22756726243b2e7c031e81530b79400365691968042d520c330d3603192c30614f5b4429061d31560d47185066220331333152755c144f2f71246c7b4525366a60276f3454125f170806134d1923276f3454125f1708062d3319234d443b3760464f6a2223552e58496b0a7f4a7250530c56031e10,
  0x3957192d56222460300e5561592b3d65022a6d16797155554d094b40078043162542414c1f1141384e7e7c0b6753530f6a19130c3250384e7e295e570f536e146f0d44320705152c1c5e30195360473d324832567b2d71825e5c1e29597013724d3d1f6c71702a4e7c5d491b651e1561735e4362761e3b704867047013690b60370854754c213e3b1c7f13701a782314302f0e3762454867047013690b606f396e754c213e3b1c7f13701a7823144a4b5b37624521096f5f24824c39581c273f2461524867047013690b606f39381e56213e354a5361223282010200000003802b,
  0x5007c65254066025d3e3964494742131d38260d505d72775b58405724694172164b64110e692e0a4e700a4b165600813200237c673b6535453c7f656012001b4800045e21181304667b12045c32004b3e0012670b82781a777d4f03456700598200501023532e05028069436475006e39001933377f0068232278720273006b490037567960162a714257343371003e3a004c2d0a236d595d792c4f501200453a004c2d0a236d595d10124f50120045490037567960162a267324813371003e3a004c2d0a236d595d105f7b5a120045490037567960162a267324083565003e73006560411f773d09407663327c00371100511d15086f3825235530384c001b,
  0x5300297029051d227a5e130a4866142e3877130a6d6e1a6c1a694f815b79774b454c2f800742441c3e02233629100004764e515a1678306937204c560b0025235d6a827b0f726972366e7178005e137319010874111a114d15120b0025700674827b0f726972366e710b00257006680b7b0f726972366e7149003772801467697d3628254a702849003758006680145c51681e5e33774a006a026a603b183f7605725a70340400494e494c4a13630e346b3e2d317f003a353a37397020754f637d56527300655165596137804b38706c520a08000f190f151126431c59620c5a17,
  0x47188181100f73032d3778240f42797c554a795e3f090c3e7c39796d41107b163b0c153507741853556907007d172f072e545b3c28547f003f6d004b765c63021f39060f107363658100720d2720776e4a7d747310201e020011765c630c212d060f107363658100720c4f3814386d1475817810555d004600177d7f14345500411b25285a006e5e294949472a3c577459026a2a005f081709093b8148347d2775011600737b6c7a7a48023b4f065c59376d0010081709093b8148347d341e65810072081709093b8148347d272a3230007363275f5f1a0869361850765b290041,
  0x6f597119427d6f393752160b2559700f010349034f712f134b1a4f6719590e4b3d13253f106124040c102401007050335c29390c103d0f01124410234825671777715c494239123a6d3a78506830365c6b4d362f2b47455959393b1627596634145d75035f5f69034f547e4a525d260e8024241a80347a3d3931265d75035f5f69034f092c64525d1b4816818173166b6d813d796b4b452009094820034b6f562d69,
  0x2942563e45360e563360396c3957495247681b29767d6866682e041951750b542f7b4412612c4e17630e31176d0f74603901220e3a77650a044c1352313219322a3523477b3f19214c295b1c0477500918691f14430e462f542c32197b31080f2106372f5d4043627f1b1151438240046936760f744447290b4703240f811a4d0d740f3f3c5a4074805f7402420421671c27701e30471c19671f417f621c675c1365533c1a341c641a4d0d740f3f3c5a400b665f74024c54264340217d281f2b74484301,
  0x460021687d6e7625187060322600423d17387d3158792c4e0b293d03663141455e4b686d311f6410606d694e7a5200017e00703d590a1b675823597e384800347b00743260305a2952273a580a45001c020066465b114b15683e6d424913001564007a414b5c59443c1f7821664b004c0400496b52197c2d788151131743000c120001176b2f4f5c010181250b24005764007a3755654b1b26513c52336700267100826c185434274a37025e785f002c1f00094c2e1e38685d681131501c005d64007a3755654b1b261b72483d6700267100826c185434274a371c44785f002c1f00094c2e1e38685d68113b5210005d690073197a222e6b3b4b2908782a0076,
  0x300161a532e337e763c2813200242561438676b223d3b016b200e1842144111214b06810e18150425274d58216d001c0000691c804c72233d256e6b7a0600286e006c52482601461c6a55298258001367000d0e6979380c19207f59114c00462300525f555b55796d4b07080381004a7f003a09401a354e1306204a7e2f005f64007a2567058041817075737d0400720a00752b6642273b550d435c5065005b1f00095e1c7e034238600e10067f001179000e581d415c482e3e7827331e002864007a25670580414b236b7d7d04007264007a25670580414b236b7d711000720a00752b6642273b55450b426a65005b2a002e6672783b0e49361a0b561e0071,
  0x30005a7577590a6941546b59725342246a3823298149730b80795c230681411b214b06680e64060f45393f070b3200446e00527e1d3765256d0e6968102500573500533c13717943182b6d4c014c001e4e00307d3a120a406b58163782370065350053063f7b7943182b6d4c014c001e4b001a41590333242e762d43465000044e00307d441481406b58163782370065350053140b573f6f0c083f786270003a7200324125407a66077c194e306f00827300655c040e5460166737602f40005610001e277f752f236d1c4c6e0943002d63004735081c253d2c4b33241518006a10001e277f752f236d1c4c6e2329002d20003c4e7b675e46573808651303005a,
  0x3d5f600571267e573939494719420c4c7842364343430b737a2d13034144322f6448521a45215a530d29670033115859167e677b1b6c3478443b004b63662100382b3c7a2b1f115675005b201d6279555847095864722d0e00287c691426702a3f64212367123a0010201d6279496447095864722d0e00285c8238321d32224c7a1606486500406a3e35561f332d03013a047a66007b3a471d34656b4f0e5f07493c040053493c664f1e183475247c027f7f0030493c664f1e183475247c02166500306516744d0b23363876296f5e4600452d625851310d322f553f241e35001b,
  0x73752a7c4d3b156b7a356e275d063504333e316e7e3f1b5526171a7c2b2829566b573b6a200d453b72414d6e4f590f473814643b1f241060173b79134f716f796c520c5a6f817f794875412f6f0829446d61466d786d143737000d4a4182234217121c5a7b2d1d7e751b105f5112195619473165442f5a207d2d24801b176a3c521e3f542963510b5f03686c6a3c521e3f54296351254503686c19473165442f5a20325e744a1b172d173e4d46061f653a113c396536264240211e282061597b12043e0e,
  0x2400024f34672b430e2d3a033219421870384f03800d501e476c717078654109274b3231520f08222e6d5b105c0500626d001f572c2b81725240210d2a2d00600e003b285b3a78405e5134545a3b00387d00572f551f6e1714812c3d383c00803f00453251497a82807702684a6200717500485d2628611d7b3f376d464b001d3f0045285b526c431e0e5341483e007544003e5b283117402d2a30423b45000e3f0045285b526c43563f6d41483e007544003e5b283117402d444c0c3b45000e3f0045285b526c43563f376d523e00752b00616221533714710341692f29004644003e5b283117402d444c163d39000e28004b0f74816a5e4d786f082e44005d,
  0x79000e3c39033a4a043331280382420e0e383b676420466e6b7a3546261f4155344b3a636960034e14591d155a65002026004e4177735c34422b432c5f0c005c7e0007205c227d4a32031a401f4d006e2500357a5848030d50235530381900113400205b0836354030536c181c4e004a18002d76631308037d1456792021007a3c002f2133712d1e4d7c1617272900384700546250125665813f6d6c5c5a004b47005462501256658159536c5c5a004b3c002f2133712d1e022a666427290038470054625012566581591d15665a004b470054625012566581591d155a66004b3700363f0e314a6a63184d77755c005e0a0075474a80496e442432716e070036,
  0x1900600623317f2d456d35602e3d2406382c2c417f6a21607239761e812d384b003916152d04537f4739025a256c006f484d052a415c17157d48587080006d204e5571554f563b4378491603001616822e122e342d48400b3a6d80006d6d7a5f71554f563b4378491680006d6d7a537d554f563b437849167b00746a585f0e5b79175c827739677b0074505b2e27065832197b087f335700725911321c4e290d1d240a064776007b4108742c1d1b6f474e5667040d0008427b0f576668143c80651c7f34002002633c560f17506f610c703b690073821065583a365b7f283c4b40,
  0x78005e717910444b093c52157a0c421e5e384e70628263554a17061c6f154136684b5a252b745f6630302b521d62002f4300746931561f7a5d5260690b7b003f4d0080552a6d6e2f4a1b587a216b003a360003642316155439682b09621800494d00801f56776e2f4a1b587a216b003a360003642d18095439682b09621800496000317f116f2764110c564d142d00372500352f156110515773613a0f01004a4a006a026747074f821b560d6f56004c730065512d3b5779197b72680765004210001e3256482c0a6a081166311e0041730065512d3b5779197b7f116b4d0041730065512d3b5779197b721d387f004240007845521a2d281f202a2743760082,
  0x63545d632224611b35727808624f5e08547f5066197d05170d3e1c517d275524117c096e497d813d056679006b706d4106425e498260001e3e824e41482f4e190c4307723e4b3e824e35542f4e190c4307723e4b4c526d006f2b1a4f6f6e0f011916140132615a19151062182a1d451b49360d494e6235814d60465c3a4071507e7165351e07450b7d271239123305121e4e657c3e403e5c714a71507e7165351e0745432b4112397a283f7a745c0f45295d2f49091c36160f365a67296e2a4952774d5b,
  0x2d19210266143e5a26663c5e262c331801711d2e252b0d7951283f2c565882167f514e2f0d1630801b136902365a4f3916658245684f203130037931736b4c41822910193c625639030c5d0e6f4437381c1c393866486d3d793d356b4a3d5f812135333c2e75685769664d5c6b036570137f31456a1a1d362718801e13383c523e19371054115127032e6e662b6f4f1a1d362718801e133856383e191b0f2e6a230c0b24742d000e58,
  0x81761d251c555968394b28237b56265e724e40157a366a6139297373060548451e2d030e67283754210a356e26093928214a1c7b58356d45617f037d132634626934190b4e2f4e1048020c0d53082f3f02522d0b0a6a1f635e5e5a4805713350010913010f003d794d7e21071b461010357e4e3a39313209371e366010566b3a0b1e49800c69414c654d23732d1849401a3a03771a427d5c576f547c05234a0f7a10553c2506272c142f077e6039743f3d2e475e4c654d23732d184940342003771a427d5c576f547c05234a0f443c5f3c256f011c6c124068014e5a0c73204565,
  0x680040275c1542003b5918176e5842262e38770b786c170a733e7350801b4127254b4f5132022a79586f7b1c181000365b001e7112392a6f43523b79550d005d4500714d3658665f761a59107e54005765002a265e067d130016234a1a3d007c32003d7f0436516a08014f331968005957007231526b5318625d0b1b626d00187d005760235c667926695f6c547200284f00632e5537621a0c620d145c69004c06002c2360271d0a255224172f11005b340020552e4c21697757406f271a00374f00632e5537621a0c2c430a6669004c340020552e4c216977574079290e00377d005760235c66795e314503547200282700181f64397b4862797f0e0c080047,
  0x75004871620842632f043b556b0a422c0e383b1d724f3f0b47547663362b4146384b0078322c02150d2b554e654e00116b003c166c4d547d3551275a334d005930005a717a16385329772c41253d003e53002948566d4b305a0c57425e46004530005a3b2320385329772c41253d003e44003e377b7936507367236e2474002053002948606f3f305a0c57425e46004544003e506916101712616c281942005f7e00071f233b3d1a6555281b3c6a0061400078654c396e227a5e365d786e003143000b1e374a156109254d714315005243000b1e374a156109254d715d7e00527d00570b2a612f055f72623c486500400900423144337e3a365b2b2f3f480064,
  0x140053044e275a632927566702424c6f38584e4f6e098145143e0a174147384b5b3169712022154872126a00732d0010731e08431170390d0b7b003f50001b53255b653f71015c0935007b3300682668281e441282277a4e000827004e636f72640e4f2d322b400014330068265c341e441282277a4e00084d00555b5d445c691d2f170b7b003f3800317423537978001240543a0064290055712a15770d0c6f081b0f00795a002e12596e0c767714431d74000a290055712a15770d0c7c347f7a0078290055712a15770d0c6f404c290079620035485e2f304f53361e76450029,
  0x7e00075e2540664416454a1f3a39017b38741859280c03495a7d560d6b11774b45791c2a2d234e446d610434674b000019690e2c7a337c72450f6c377b0074641f11666a805e74546273063c002f0282585e784e235530388271330070493a624a24535b5a14432f181e00595b2809215921610b118157147e00075e254066164f1f02047e332705007c255e431d6d7f19817f05505c05007c255e431d6d7f33677f05505c7e00075e25406616045052517e332705007c255e431d6d7f3331280f505c24000253302568342940766332341823005280034c4844133b1f242a2433,
  0x610064146f29366c4b5c484c2c4d420f5d381b2d56560a7f2d384e7e044f4119804b04424104431b0b72703c536a005b7c000a6d164b05331d6d5b105c25002179000e1f6421043c4a0940350a6200340e003b780c1e20467c3a22414f5d002c3400205f24432f1361564980512200020b0025562d0641377a076c72421200374500714b38790644232050285c5500763e0012384b0a7d3f2818335b272e000d4500714b387906445b516a285c5500763e0012384b0a7d3f28324f25272e000d4500714b387906445b5134546655007676007b4d36705a742b573320354a00424500714b387906445b5134545a610076130034592a3a46197d39381e6b350018,
  0x240002520364202b59717f10106542426d38396e438259356923506a4b4741562a4b48463d200a2344723709285a006e50007c6a5e346132016c0666024600470a007528522d64092631231a7808004479000e0e7e561f7a5d5260690b7b003f0a0075757e3764092631231a7808004479000e0e0558137a5d5260690b7b003f3700364c6a15731651027a49285a006e81001d380d05120a44201d33322f00487f003a1457120b445c7b5182322f004864007a18344a76033a516c3d5b1c00231f00096b4f390d804932170e6067006064007a18344a76033a5179693c04002264007a18344a76033a516c75093600237c002423366134771e4542507c11007b,
  0xf004d141c6e070251801c674442204438371373731e27625c48792b413c684b825c77255e5a532a1f261400271a00712333490b72805a610d3e0003820058683e0632806e5d243352002a01002b114f7d510315265f5031005901002b114306510315265f503100590900461704736531787339441600382800393c374129623e1f201f25007613007345123446140e29161f2500762100752c726f5e5315676e0928000662000e57111425306e1c602f5b007d2100752c726f5e531567233a42000652007c1639792f6b4c3a4d7808004420002a82333c6f0d44472625740071,
  0x4f71626e7a1e5f46811d6a81430e1650773f478004136d7e7b230c803b3a485a3a721929750e4f34393d1e1d655e4c5c29387e717c1e5d1914507a475f60703a69382f36702c6f330948182313491a4b544d13574748582c67747031231a390d7f1f1f3d6b2555094b654e380e72215d0c733a197b72637d22610e751e273d060b0703790c40047406055706467d787c800a77437f5a327e2c7d267c09653e6375640e76582b5f3a467d787c800a77437f5a4c642c7d5d077a1e45200e1f2d1353732407,
  0x565e05146a49495e711b3d1a0243540a6e455342290359791406237d392606007d7531812867481b430b16270c7a804e716d53452b5c477d2f2f55555c486a0d33666e2c630e184e7a1e6f3f2b6b62172a030b4b141475731e614a0c55097c2446482a342719437c720f386e757933083307261548393940470b50825a18507c5d6e3b4a4a43042d3301296b02793a656757573f0a822b0c6045507c5d6e3b4a4a4304471901296b810a491e1c2c2c4479010b41233e17100c304712123f795e390d3807,
  0xf006e8216637c7e0f332a241b6c23823850386c015f30473747255e145f174b14562b5971071a277a5b02662c6000174a216b2b0f3e04046303221b4600212939246b297b604a636e404a43000b5f1a5d632d342f75395a478067000d492d2a3e072221684c300a067100826a1a754d02190c00677d3d1257007263311826113100136f8278662c001120526b5d721a387014010b1d39001965055834006e5d002d132f4a4a006a1e7e2b4f001526362070543939001965055834006e5d4d591d2f4a570072633118261169312d6f8278663f004516283117430c6e477f017219,
  0x42005b2b582e10076c4e456e043542166d383982723e581821427d5e2b8141380c4b72593c171b647976443a545000352c007a6e142c640d813d540a13440068010033582b3b8076332c346a125c00020a0075196b4942146510076e4e5d0060630047097a3c266a2b4c42402b10003f020066295a35366e356a1e295b2b00703700360e7552394b51056282605b004432003d6c170f1c50421e5f6c301b00314c004d750e314a387d3321012328003f510046176c746733411871175368005232003d6c170f1c50426b12623a1b00313700360e7552394b06504819605b004432003d6c170f1c50426b12622e2700313400201271445c53761352106d04001b,
  0x7c0024161f2b7f59692d050f150e422f4b381a611b5011414b610e1a52364107774b450c4908766c5278705a1c3f004d52005f0a5f750e39312321631147000e1300341d252d6a6a7b305b4e7a4e000870004f1928561919085328350935007b1300346a51376a6a7b305b4e7a4e00084e00304e1d3765256d0e69681024002c70004f1932580d19085328350935007b4700547d2a823b4575352007081200163b007f7271440f5c20745065400d002d610064203903123a757d0200035c003722001f634a8071490e06814b3527004c610064203903123a757d0f2c67440036610064203903123a757d02383476003705007c0322773b1e3818613e5317002b,
  0x7d00571b823f0c772d7f0c33335242142738185879166943242518295b29412b174b14100b2e0e4c32625f27780800445b001e46641b007e3e04304b49420025010033640f403d4b033f04365d6f005c820050553e43463880447f4d261400270100332e3b4a3d4b033f04365d6f005c1a00104c3d7e4b33726e0b15658100720100332e3b3e494b033f04365d6f005c5a0005625d08382d3a3622676d10000547005408796a780b39513c79232e00810d000807183c691a636005524e61002076007b7c6b471a6920237e7c6d2200630d000807183c691a636005077f7b0020480004450c1e760d7330093f596600515c006b6e3b524e356069677a5c4c0023,
  0x6002c7b081c3d0c7b65020f537a421e0f386e254c3c5d0a7a54495952824156234b6c662f2b6c6d114d381b610a000f39008231513d7b015d48645f594a006f22001f2c575205110a520c5a694d003216004a097b813913620634803e1c002a1900604043401c037f5e74546202000310001e42411f6d577307113e74780031090042770c2a1a391b3b4679427c000d7a00410c7759694a30803d0a410700767a00410c7759694a3017230a41070076090042770c2a1a39536c1343427c000d7a00410c7759694a301770364b070076090042770c2a1a39536c134d4470000d07005f4e35785d1d2c2c206d1276002e630047820145185a08591d155a42000c,
  0x1c00761676087d02266271670e6142522f3827683d803f81645f281c5031416f704b6905537e4a007c456d002574004540005e06254c3d77815526314a650007740015344d052a415c1779491f2500760f006e02007e5942276c0a3a645e000d74001581790f2a415c1779491f25007674001581790336415c1779491f2500765300292f724f1a572d5949056b4d0041570072633b6a7d156f826646441600381200015901504714763516753a41005e7200327f32460d530506460d3182007411005104513d76307e7d3d3e0701000f7200327f32460d530506464562190074390019811923486b44036b5e0935007b3300700c70345c0d74712743306c002d,
  0x3d1c55556a531945760851812c425d1e2c0130171550384326151d2b413e603b2d81021b1a064d551d682c006b212b335a7d1713690b662d0a6900266b2c6706821b2609394d737851003f18571c730b685d7a4a36100b3200446b2c6710010f2609394d737851003f41540160673f68037a353a3562001266574c4e135c56083622676617002f3f01787858112b5229653b64020076434e3b3b34104f6c3058372a4d0043403548484f733417532b140e3600400319767668201b556075550b320044403548484f733417532b14281c0040806a0d0d1b63682e2349341d6c0080,
  0x807b7249493c721e161303264d0a065e074e424c66750f5c153214257a462a80234655770581790558454819264446315c312e515739545926212d077c8022032818641e11537d4d19225529587704600e7c540504396b05764a261159091717358223151b5773497e4a3b4e4e643b5d77110b806805394835351f4826572778031b05394835351f482657415e031b630225505074255c4f6f3407091e50273838372747161a0b1220,
  0x73037b6e153e54305332517b692d71095b5b2811274f4160776a7a716d4f19582b50344f1b57546b67086636463c4726082c43287b530f7478574d057e3b474c4b0e55612e74505026691b7e0a61715765625f74173730166d12137b6726484708151d65504f342343426a2a666e4f1f34171a651e7e7843055e7c2765054f6c691e65050b40465d075c1e7e4624230a79595b1c51023d820a783d5f60790a2a286732817c4e790b34171a651e7e78433d0c132765053e671f414278025c0a3f3e714155,
  0x6c000607761451211960722f1d1a426f4e383070662776204f5e4b620e5a4154014b4d0c2a483f421b484975580f00430600127e762e4453254c803a7a7d004e08000f551f11660073334f016a1b002a0e003b814b5c541760475c630e3500616a00231d43401c4538652e73075c007243000b7a817c49794e4e5a5e083100124c004d447552392208354e2e4f43007f3700363f0e314a6143033555344000041c00765e322c15265f0f6c083e55004a67000d2551576e5d24744d45452e00391c00765e322c15265f0f36344855004a4c004d44755239224066682e4f43007f67000d2551576e5d24744d4f472200392300523480373b083e581f0c5d3e0018,
  0x3c002f7f5803673341187e6b5f804244093842634f43031219241d475f7c415e764b12245f3d193e29476b54480a0064540042655e36652b30404e781c21004420003c3d0a1574640c6d6039695b007c77002b6d6f11421a2370474f3119007707005f1b090b021f1a42695b4e780015820050231048686146155717013e00604b001a7e6e66602c2e205c355d0600266a0023590761631162014f33196d002a38006905151d23571d18274e267d005d1900602a7c222072213581506a1600596a00235907616311624e0229236d002a6a00235907616311624e02291779002a38006905151d23571d184134267d005d4500714a4b0a7d36083a804c0922007a,
  0x81001d391c160b6a261974665f5042795d381b22551547380880047e394b4174604b4b2812583164556d0b226e6b00196600431f0c1754690f6d471d80220029820050020714037e5f356b63605b008101003334466f8005244e1820232800028200504f331e037e5f356b63605b00814c004d7b805766202c1022497427004a8200504f33120f7e5f356b63605b008155000c6f4312604c232d1d0d3b1e00431c00767701556c587b211e1b34160077580022704e5028341f4f34306141000e2b00611335335b4f64344f1b5a4200752d00445d191d50683e1b2d47791a005d2b00611335335b4f64344f1b7428007556003f266a66331b45680e4232010067,
  0x450071275c3c705016161078098042562538355f12770b3726771b060755416a514b60801553087f477958057331004653000f3a485f266c153965254116007d64007a572c80154d3b364b68224c000f2e00776c186e27115c673f0e3c6f004108000f2b5848083b218146011724000e2c0011740f7658296c0b083c464000366e006c1c6721727d6424594303350011150017671c6211066a142a40804e0072150017671c6211066a2e1040804e00726e006c1c6721727d1955260d03350011150017671c6211066a2e5d6c074e0072150017671c6211066a2e5d6c7e5a00724f006371123f274900763e485467005b3e00125c274713683241532168090071,
  0x4f00638120472d746c333e60347542791a38104b5d0981457d2c4e0b0369413f524b103a0633584d1d247a184c28004e6d001f431a75595d64554a2e543a006454005c795f040a20786d162c142d00372f002740717f79630b166d576f56004c54005c43080e0a20786d162c142d003754005c4308021620786d162c142d003721006f205d666b3c384c7b11621800493f0045760707651d01817e511b1c006b0400496f3a373970206b242f2d03005b45007130128263621c567332362b00613e00125371012021672d10190258002245007130128263621c56736a6745006164007a18094173310e2b402f4d4b0030370036764d0360632f042357216b0066,
  0x2300525d085c81471353200a7468426079380e313f374b1428666c6a2c0441771f4b23783c733a28484d7a0f6617002f59003b0a45361a674b5d04397851003f0c00583e660d5f79143c4a6d6270003a77002b7b6a76240a6f473916211300490c0058080f175f79143c4a6d6270003a77002b7b7478180a6f4739162113004905007c79651d127d14200e556f34003743000b6c546521437a822b407427004a22001f0813161c367f071b05144f004c20003c64290d5814511050235a3900426300471f5a762b6f32733328614a004140007845521a2d281f20652d6b0a00426300471f5a762b6f327333287b30004143000b3e3169565b6463595c40110082,
  0x3c27683c64811f401f063d33067d2c29294d543c151c5962253d4e245333757d4e494f270b1b21132f65047f097e2d52462e64052c4575660d0d1c102235745f30473a556f000d0d1c042e35745f30473a556f00286f635f3312565d2c0a71493d332634377378677a091e4d0d47336f732a7073111272451e5351821017644156647b54083f3305575b1f351f422d1f082f7b4450466428644e1f422d1f082f7b4450467e0e644e07815207634a2079566547197c50370308373014530f3d3382374c4c,
  0x67500d7d820b431f625f0d3672540416274a56702672273664760f5c4721680f5a6c4f5f78405e73822b35341a307240203408195f47557921460644040649303564674955373b693a152e670d0d55716b074a0c4a81392e6f65232a5211237d1930406508700910411e4059646823604559264c5c725d08695d735866396d1956212c4372811d1a26102b1d4a166a781757401102665f1c810b6f591e673121424963624524670278142a651c5262770420213e695d735866396d190b52464372811d5f1c810b6f591e6731210c756d62453a734c6a6918272a4f1b782b7f4b7e,
  0x20003c0c774d6f275d571d715b19420c32383d4e350356783368045454454155694b0a295a33416776476241572500223000400f746976504b73603d8047002c21006f8102743b424f4e38701f60007100000052324608416242807d7f33000f63004781022d22784803715f6b2c005a3b007f681b38231018111d3a7e1f007505007c3350622e363e63390e8012004a7e0007503321554d0d584a7503710039610064146f29362b04633d7a7d0b005822001f6f145a4d587f207c560678002b610064146f29362b04630723040b005822001f6f145a4d587f207c60086c002b7e0007503321554d0d723075037100394900370b7810453f716531626d54003d,
  0x2a002e0c7c30542f35670e4f204a421510381e587b406f6e771664373f48414e814b371f0f1343695a0611802474002037001c0125773b4d3d1481185e46004504004973243347416a102249580700147f003a4629503c421973613a2b7c006f0400493d503d47416a102249580700144500713f430a037b6a033978063f00310400493d503153416a102249580700147c00246c651c5b0a5b5608681a0b007d0f006e173f5c1e652f6f34515036002a460021142050097a01806e537e2a00623d00626f63337a098203157b3d5900213d00626f63337a098203157b573f002112000150803a245f04773c14605b00816800400b462c4d367d12646b1b570044,
  0x12000129433210576e7a4b4e264742720b38254c252f1f1001541c29447d41351b4b5d0e1b22541c14381c0c1942005f7000354d3527091e335c7411225f0067600031036f333c77190655234b430017230052336150470c6a7d2e603840006c60003150183d3c77190655234b430017230052336b523b0c6a7d2e603840006c28004b1448173a0f214b5f4c1942005f0c00587524492d2208191c16401100560a0075516e56265c20745065401100567d00571e411b5266070316387444003c06002c654268311d7c806d13473f004777002b3c823621490e0674571c20003606002c654268311d7c806d13612500470c005847014d623a757d4a320c7e000b,
  0x62000e57111425306e04628237424f213832100621654e287e3b54604135384b431c6c4e7c05700169306f0082710058141e38682f646b0c2c45000a260000191e1e2a6b6f45195c3100095d0000606f655918143e6a2752007a5d00006063715918143e6a2752007a3d002805051003152253564f6d000c38004e7d0f5f1f27600133735e002c230005036d523c5c300b29735e002c4c00430e484d125060064747360014370040753b367133237d04744d006f370040753b367133237d040b33006f2a0006381a2e483a7a25670708004f44007a2f5c3e172c4f45305f0f000c,
  0x8116677f5809060e003800155c3c7046010d534382355c384b006e2747135313215c0d210c1059003b390e573752567570351041101200011b67700972463d5a5a5233245f008120662a338019374310594e1531000a817b003d5c1d50432d0b3e583c002f7f58035d740473564a320f0d40007876186c280a645c272d6d104e43000b0d6b175b796a5f5c561673353b007f1f684b5663147c361047713f480004641b382d206f07003d3c12443b007f1f684b5663147c003c51713f43000b0d6b175b796a7942561673355e004e74442c1a164b1b6a2377590a,
  0x5e004e5d26027e4b1a2c6c73717e4277473854066b6733160c6b247239414158164b6420751a55225d6f76215c470037760061374b286e654f723d573450000e4e00301d6645671d2d6c2c6e013e00602600684b391d2d474b4b1028305e001765002a3251716677747f4c3b6177000b7a00410c77595f686e166a033842000516004a3a493b31402c79605b0280004f6d0039493a4852431f422328810300345e004e5d26027e465169653829350006250035265d81053d321a54155a4e007d5e004e5d26027e4651692f64333500066d0039493a4852431f5c0928810300345e004e5d26027e4651692f642741000676007b3d46726c77268213713980000e,
  0x76007b6050777d610f22604a523542334f38636970577277775a6f624901410f794b283d4638172e8007375a6b4d0041780044146d2c0f3f4174764c1713006040007828673a163b71783008232e008143000b0e69496d48120b537b60550002400078751044163b71783008232e00817300651d335c2744056f091e08120016400078751038223b71783008232e00814100281747600423035620663352002a10001e215d2d583e2a3b636d8260001e7c00245c21361b16816d333e3871002507005f27624d686d0216500d0012005e7c00245c21361b16816d406a195900247c00245c21361b16816d3376690800251c007619822e172b0858204c02460073,
  0x6c00060a0657217835747a207212427b3d38627378013c82770d7e116b0a4158124b1b06052b260c5a020e5229670033070045080c29780c3d526e52524b006610001e4356461a726a42067c5b68006e730065767a3d691119417d07281b001510001e0d82501a726a42067c5b68006e10001e0d824426726a42067c5b68006e3b007f6745106a686a057c0c4504006918002d73795849525b6a1748014c001e4c004d294d0360632f7d806f8022002931000a680a0e3745016a1c5c582400065200791b79754c3e82196772635f007d5200791b79754c3e821967727d45007d410028172838590e041f7d384b4300176300471f472f3f6e7d1344357c7b0060,
  0x460021687d6e7625184d230f2600423d17387d3158792c4e0b664640663141455e4b686d311f641060531a347a5200017e00703d590a1b67587c2a54384800347b00743260305a295261490f0a45001c020066465b114b156828162c4913001564007a414b5c59443c140b16664b004c0400496b52197c2d784f32641743000c120001176b2f4f5c018202230b2400577100826c185434274a398160785f002c64007a3755654b1b260a470b336700261f00094c2e1e38685d797242501c005d64007a3755654b1b260a11373d6700267100826c185434274a536760785f002c1f00094c2e1e38685d79724c5210005d690073197a222e6b3b745a31782a0076,
  0x300161a532e337e2f3b0c64330242561438676b223d3b0108263d2e5a144111214b06810e1815044c223a74796d001c0000691c804c722362560810620600286e006c5248260146037e1e3c2858001367000d0e6979380c39550e1c6a4c00462300525f555b5579350f29520b81004a7f003a09401a354e196a1326452f005f0a00752b6642273b621c5a502965005b79000e581d415c486c1c29335a1e002864007a25670580416e6531626d0400721f00095e1c7e0342151e056e167f001164007a25670580416e657e0b7704007264007a25670580416e657e0b6b1000720a00752b6642273b174d74502965005b2a002e6672783b0e7f252850611e0071,
  0x5a00054a7e7c261f414e7539802242132738180a5518552862404a39144f41623a4b662f3372083c637847117212000e3000406e7c61685805663b797e0d00703900197d1f7c333e230770761e3500724a006a3c2e075045607c130d654e0011390019474b03333e230770761e350072390019474b7a3f3e230770761e3500724700546878233b4c624a2827102500571400674768262d043253333f6a4100246b0056782d3f3372464a2a110215003c130034244f206b0815826b5a1813003370004f5f3463187b6e0118742070005070004f5f3463187b6e0118743a5600504c004d0d36802320547f3030518200481100512e32460d5305067641735e0058,
  0x680040275c1542003b716b2f6e5842262e38770b786c170a732e1040801b4127254b4f5132022a7958670814181000365b001e7112392a6f430a4831550d005d4500714d3658665f76732a697e54005765002a265e067d130039606d1a3d007c32003d7f0436516a085034821968005957007231526b531862687826626d00187d005760235c6679264524485472002806002c2360271d0a25765f3b2f11005b4f00632e5537621a0c6f76215c69004c340020552e4c21697714432c271a00374f00632e5537621a0c6f404d6669004c340020552e4c216977144336290e00377d005760235c66795e763e48547200282700181f64397b486275040a0c080047,
  0x42005b2b582e10076c103e30043542166d383982723e5818213c06582b8141380c4b72593c171b6479373f7e545000352c007a6e142c640d810e2f5e13440068010033582b3b807633604f1b125c00020a0075196b49421465177c754e5d0060630047097a3c266a2b0b41822b10003f020066295a35366e350565475b2b00703700360e7552394b51672161605b00444c004d750e314a387d5462222328003f32003d6c170f1c50427d2448301b0031510046176c746733410612055368005232003d6c170f1c50427d71743a1b00313700360e7552394b06153b61605b004432003d6c170f1c50427d71742e2700313400201271445c53766531626d04001b,
  0x3c002f7f58036733411305665f804244093842634f430312194166645f7c415e764b12245f3d193e292f183c480a0064540042655e36652b300b35431c21004420003c3d0a1574640c4a2316695b007c77002b6d6f11421a23343c133119007707005f1b090b021f1a281a414e7800158200502310486861466c2c6e013e00604b001a7e6e66602c2e7c270e5d06002638006905151d23571d3f5c75267d005d6a0023590761631162503482196d002a1900602a7c2220722133024e6a1600596a002359076163116250812b236d002a6a002359076163116250812b1779002a38006905151d23571d594275267d005d4500714a4b0a7d36083703490922007a]

private def inverseRow (c : Fin 198) (i : ℕ) : ℕ :=
  (((inverseWords[c.val]?).getD 0) >>> (8*(i*count c))) % (1 <<< (8*count c))

end CriticalConicEvenFinite.Catalog


namespace CriticalConicEvenFinite.Catalog

private def reduced (c : Fin 198) (i : ℕ) : ℕ :=
  packDigits (count c) (fun j => ((coeff c i j : ℤ) : ZMod 131).val)

private lemma reduced_entry (c : Fin 198) (i j : Fin (count c)) :
    Field131.fromRows (count c) (reduced c) i j = (coeff c i.val j.val : ZMod 131) := by
  change (((packDigits (count c) (fun j => ((coeff c i.val j : ℤ) : ZMod 131).val) >>> (8*j.val)) % 256 : ℕ) : ZMod 131) = _
  rw [readDigit]
  · exact ZMod.natCast_zmod_val _
  · intro t _
    exact (ZMod.val_lt _).trans (by decide)
  · exact j.isLt

private def rankCheck (c : Fin 198) : Bool :=
  Field131.batch (count c) (reduced c) (inverseRow c) 0 (count c)

private theorem regular_of_check (c : Fin 198) (ok : rankCheck c = true) :
    Function.Injective (Matrix.mulVec (fun i j : Fin (count c) => (coeff c i.val j.val : ℂ))) := by
  let _ : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  have small : count c ≤ 256 := by
    unfold count
    apply (Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 32))).trans
    decide
  have hn := Field131.injective_of_rows small (reduced c) (inverseRow c)
    (fun i => Field131.batch_sound _ _ 0 (count c) ok i.val (Nat.zero_le _) (by simpa only [zero_add] using i.isLt))
  let M : Matrix (Fin (count c)) (Fin (count c)) ℤ := fun i j => coeff c i.val j.val
  have eq : Field131.fromRows (count c) (reduced c) = M.map (fun z : ℤ => (z : ZMod 131)) :=
    Matrix.ext (reduced_entry c)
  rw [eq] at hn
  have nonzero := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hn))
  have integer : M.det ≠ 0 := by
    intro h
    apply nonzero
    rw [←Int.cast_det,h,Int.cast_zero]
  apply Matrix.mulVec_injective_of_isUnit
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  change (M.map (fun z : ℤ => (z : ℂ))).det ≠ 0
  rw [←Int.cast_det]
  exact_mod_cast integer

end CriticalConicEvenFinite.Catalog


namespace CriticalConicEvenFinite.Catalog

private def test (i : ℕ) : Bool := if h : i<198 then rankCheck ⟨i,h⟩ else false

private def checks (offset : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => checks offset n && test (offset+n)

private theorem inChecks {offset n : ℕ} (pass : checks offset n = true) :
    ∀ i, offset ≤ i → i < offset+n → test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨old,last⟩ := Bool.and_eq_true_iff.mp pass
    intro i low high
    by_cases h : i < offset+n
    · exact ih old i low h
    · have h' : i=offset+n := by omega
      exact h' ▸ last

private structure Certified (n : ℕ) : Type where
  ok : ∀ i, i<n → test i=true

private def grow {offset : ℕ} (proof : Certified offset) (len : ℕ)
    (pass : checks offset len=true) : Certified (offset+len) := by
  refine ⟨fun i hi => ?_⟩
  by_cases h : i<offset
  · exact proof.ok i h
  · exact inChecks pass i (by omega) hi

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
private def checked : Certified 198 := by
  let p : Certified 0 := ⟨by intro i h; omega⟩
  iterate 49 let p := grow p 4 (by decide +kernel)
  exact grow p 2 (by decide +kernel)

/-- Every signed catalog core is invertible over the complex numbers. -/
theorem regular (c : Fin 198) :
    Function.Injective (Matrix.mulVec (fun i j : Fin (count c) => (coeff c i.val j.val : ℂ))) := by
  apply regular_of_check c
  simpa only [test,dif_pos c.isLt] using checked.ok c.val c.isLt

end CriticalConicEvenFinite.Catalog

namespace CriticalConicEvenFinite.TightReps

/-- Sixteen entries fit in each word and sixteen words fit in an outer page. -/
def packedLookup (pages : Array (Array ℕ)) (bits i : ℕ) : ℕ :=
  let page := (pages[i/256]?).getD #[]
  let word := (page[i/16%16]?).getD 0
  (word >>> (bits*(i%16))) % (2^bits)

private def indexPages : Array (Array ℕ) := #[
  #[0x9080f09070e09060d09050c09040b09030a090209090108090007070606070505070404070303070202070101070000, 0xd041e0d031d0d021c0d011b0d00070b0a1a0b09190b08180b07170b06160b05150b04140b03130b02120b01110b0010, 0xf072c0f062b0f052a0f04290f03280f02270f01110f00100d0c260d0b250d0a240d09230d08220d07210d06200d051f, 0x11083811073711063611053511043411033311021c11011b1100070f0e1a0f0d320f0c310f0b300f0a2f0f092e0f082d, 0x13074213064113054013043f130328130227130111130010111026110f25110e3e110d3d110c3c110b3b110a3a110939, 0x15054d15044c15033315021c15011b13121a13113213104b130f4a130e49130d48130c47130b46130a45130944130843, 0x17011115142615132515123e151159151058150f57150e56150d55150c54150b53150a5215095115085015074f15064e, 0x171166171065170f64170e63170d62170c61170b60170a5f17095e17085d17075c17065b17055a17043f170328170227, 0x190c6e190b6d190a6c19096b19086a19076919066819054d19044c19033319021c17161a17153217144b17134a171267, 0x1b06751b055a1b043f1b032819182619172519163e191559191474191373191272191171191070190f6f190e3a190d39, 0x1b16671b15811b14801b137f1b127e1b117d1b107c1b0f461b0e451b0d441b0c7b1b0b7a1b0a791b09781b08771b0776, 0x1d0e521d0d511d0c871d0b861d0a851d09841d08831d07821d06681d054d1d044c1d03331b1a1a1b19321b184b1b174a, 0x1f055a1f043f1d1c261d1b251d1a3e1d19591d18741d17731d168d1d158c1d148b1d138a1d12891d11881d10541d0f53, 0x1f15481f14951f13941f12631f11621f10611f0f601f0e5f1f0d931f0c921f0b911f0a901f098f1f088e1f07761f0675, 0x210c9d210b9c210a9b21099a21089921078221066821054d1f1d321f1c4b1f1b4a1f1a671f19811f18981f17971f1696, 0x211c74211b73211a8d2119a22118a12117572116562115a021149f21136f21123a21113921106e210f6d210e6c210d9e],
  #[0x23124523114423107b230f7a230ea8230da7230ca6230ba5230aa42309a323088e23077623067523055a211e3e211d59, 0x25078225066823204b231f4a231e67231d81231c98231b97231aab2319662318652317642316aa2315a923147c231346, 0x2517b2251689251588251454251353251252251151251087250fb1250eb0250daf250cae250bad250aac25099a250899, 0x270cb6270bb5270ab42709a327088e270776252159252074251f73251e8d251da2251cb3251b73251a72251971251870, 0x271c80271b7f271a7e27197d2718b927179427166327156227146127136027125f271193271092270fb8270eb7270d78, 0x2910bd290fbc290e85290d84290cbb290bba290aac29099a290899290782272267272181272098271f97271eab271d81, 0x2920b3291f73291e8d291d8c291c8b291b8a291a892919be29189f29176f29163a29153929146e29136d29126c29119e, 0x2b137a2b12a82b11c12b10c02b0f912b0e902b0d8f2b0cbf2b0bb52b0ab42b09a32b088e29247429237329228d2921a2, 0x2b23972b22ab2b21812b20982b1f972b1e962b1d482b1c952b1b942b1aaa2b19a92b187c2b17462b16452b15442b147b, 0x2d16522d15512d14872d13b12d12b02d11c32d109d2d0f9c2d0e9b2d0d9a2d0cc22d0bba2d0aac2d099a2b25812b2498, 0x2d268d2d25a22d24b32d23732d228d2d21a22d20a12d1f572d1e562d1da02d1c9f2d1bb22d1a892d19882d18542d1753, 0x2f1a632f17602f165f2f15932f14922f13b82f12c42f11a72f10a62f0fa52f0ea42f0da32f0cbf2f0bb52f0ab42f09a3, 0x310bba310aac2f28982f27972f26ab2f25812f24982f23972f22ab2f21662f20652f1f642f1eaa2f1da92f1cb92f1b94, 0x311dbe311c9f311b6f31186e31176d31166c31159e3114bd3113c53112b03111af3110ae310fad310eac310d9a310cc2, 0x330eb4330da3330cbf330bb53129a23128b331277331268d3125a23124b3312373312272312171312070311fb2311e89, 0x3320b9331f94331eaa331da9331c7c33194433187b33177a3316a83315c13314c03313b83312b73311783310b6330fb5],
  #[0x3510bb350fba350eac350d9a350cc2350bba332aab3329813328983327973326ab33258133248033237f33227e33217d, 0x35248b35238a3522893521be35209f351fb2351e893519513518873517b13516b03515c33514bd3513bc351285351184, 0x37139137129037118f3710bf370fb5370eb4370da3370cbf352cb3352b73352a8d3529a23528b335277335268d35258c, 0x3727973726963725483724953723943722aa3721a93720b9371f94371a5f3719933718923717b83716c43715c13714c0, 0x3916b03915c339149d39139c39129b39119a3910c2390fba390eac390d9a372d81372c98372b97372aab372981372898, 0x392a8d3929a23928a13927573926563925a039249f3923b23922893921be39209f391b6d391a6c39199e3918bd3917c5, 0x3b18c03b17b83b16c43b15a73b14a63b13a53b12a43b11a33b10bf3b0fb53b0eb43b0da3392e8d392da2392cb3392b73, 0x3b2eab3b2d813b2c983b2b973b2aab3b29663b28653b27643b26aa3b25a93b24b93b23943b22aa3b1b7a3b1aa83b19c1, 0x3d1bb13d1ab03d19c33d18bd3d17c53d16b03d15af3d14ae3d13ad3d12ac3d119a3d10c23d0fba3d0eac3b30983b2f97, 0x3d31a23d30b33d2f733d2e8d3d2da23d2cb33d2b733d2a723d29713d28703d27b23d26893d25be3d249f3d23b23d1c87, 0x3f24b93f1d933f1c923f1bb83f1ac43f19c13f18c03f17b83f16b73f15783f14b63f13b53f12b43f11a33f10bf3f0fb5, 0x4110c2410fba3f32ab3f31813f30983f2f973f2eab3f2d813f2c803f2b7f3f2a7e3f297d3f28b93f27943f26aa3f25a9, 0x41289f4127b2412689411d9e411cbd411bc5411ab04119c34118bd4117bc4116854115844114bb4113ba4112ac41119a, 0x4313b54312b44311a34310bf4134b341337341328d4131a24130b3412f73412e8d412d8c412c8b412b8a412a894129be, 0x432c95432b94432aaa4329a94328b9432794431ea8431dc1431cc0431bb8431ac44319c14318c043169043158f4314bf, 0x451ab04519c345169b45159a4514c24513ba4512ac45119a4335814334984333974332ab433181433098432f97432d48],
  #[0x4534b345337345328d4531a2452e56452da0452c9f452bb2452a894529be45289f451fb1451eb0451dc3451cbd451bc5, 0x472b94472aaa471fb8471ec4471dc1471cc0471bb8471ac44716a44715a34714bf4713b54712b44711a345368d4535a2, 0x491bc54916ac49159a4914c24913ba4912ac4738984737974736ab473581473498473397472f64472eaa472da9472cb9, 0x4939a24938b349377349368d4935a2493070492fb2492e89492dbe492c9f492bb24920bd491fc5491eb0491dc3491cbd, 0x4b317d4b30b94b2f944b2eaa4b2da94b2cb94b21c14b20c04b1fb84b1ec44b1dc14b1cc04b16b44b15a34b14bf4b13b5, 0x4d309f4d2fb24d2e894d21c34d20bd4d1fc54d1eb04d1dc34d16ac4d159a4d14c24d13ba4b3aab4b39814b38984b3797, 0x4f30b94f2f944f22c44f21c14f20c04f1fb84f1ec44f16b44f15a34f14bf4d3cb34d3b734d3a8d4d39a24d32894d31be, 0x5132895131be51309f5123c55122b05121c35120bd511fc55116ac51159a4f3d814f3c984f3b974f33944f32aa4f31a9, 0x534098533f975335a95334b95333945332aa5323b85322c45321c15320c05316b45315a3513e8d513da251349f5133b2, 0x5735a95734b95725c15724c05723b85722c45541a25536895535be55349f5533b25524bd5523c55522b05521c35516ac, 0x5d26b05d25c35b39a95b38b95b37945b26c45b25c15b24c059389f5937b25936895925c35924bd5923c55737945736aa, 0x633da9633cb96329c16328c0613c9f613bb26128bd6127c55f3b945f3aaa5f27b85f26c45d3a895d39be5d389f5d27c5, 0x69409f692bc5673f94672ac4653e896529c3]]

private def item (i : ℕ) : ℕ := packedLookup indexPages 24 i

def L (i : ℕ) : ℕ := item i >>> 16

def a (i : ℕ) : ℕ := (item i >>> 8) % 256

def core (i : ℕ) : Fin 198 := Fin.ofNat 198 (item i % 256)

end CriticalConicEvenFinite.TightReps

namespace CriticalConicEvenFinite.TightCoverage

/-- Each width record stores its first catalogue index in the low twelve bits,
and a bit for each residue occurring in that width in its remaining bits. -/
private def widthRecords : Array (Array ℕ) := #[
  #[0x7f000, 0x1ff007, 0x7ff010, 0x1fff01b, 0x7fff028, 0x1ffff037, 0x7ffff048, 0x1ffffe05b, 0x7ffffe06f, 0x1fffffc085, 0x7fffff809c, 0x1ffffff80b4],
  #[0x3ffffff00ce, 0x7fffffe00e8, 0x1ffffffe0102, 0x3ffffffc011e, 0x7ffffff8013a, 0x1fffffff80156, 0x3fffffff00174, 0x7ffffffe00192, 0x1fffcfffe001b0, 0x3fff9fffc001ce, 0x7fff3fff8001ec, 0x1fffc3fff80020a],
  #[0x3fff87fff000228, 0x7fff0fffe000246, 0x1fffc0fffe000264, 0x3fff81fffc000282, 0x7fff03fff80002a0, 0x1fffc03fff80002be, 0x3fbf807f7f00002dc, 0x7e7f00fe7e00002f8, 0x1f8fc00fc7e0000312, 0x3e1f801f87c000032a, 0x783f003f0780000340, 0x1e07c003e0780000354],
  #[0x380f8007c0700000366, 0x601f000f80600000376, 0x1803c000f00600000384, 0x20078001e00400000390, 0xf0003c0000000039a, 0x1c00038000000003a2, 0x3800070000000003a8, 0x70000e0000000003ae, 0xc0000c0000000003b4, 0x18000180000000003b8, 0x30000300000000003bc, 0x40000200000000003c0],
  #[0x80000400000000003c2, 0x100000800000000003c4]]

private def selectCase (width residue : ℕ) : ℕ :=
  let g := (width-7)/2
  let group := (widthRecords[g/12]?).getD #[]
  let record := (group[g%12]?).getD 0
  let below := (record >>> 12) % (2^residue)
  let pairs := below - ((below >>> 1) &&& 0x555555555555555555555555555555555555555555555555555555)
  let fours := (pairs &&& 0x333333333333333333333333333333333333333333333333333333) + ((pairs >>> 2) &&& 0x333333333333333333333333333333333333333333333333333333)
  let bytes := (fours + (fours >>> 4)) &&& 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
  record % 4096 + ((bytes*0x10101010101010101010101010101010101010101010101010101) >>> 208) % 256

private def chamberWidth (c x y : ℕ) : ℕ :=
  match c with
  | 0 => 3*x+y
  | 1 => 3*x+2*y
  | 2 => 2*x+3*y
  | _ => x+3*y

private def chamberResidue (c x y : ℕ) : ℕ :=
  match c with
  | 0 => x
  | 1 => 2*x+y
  | 2 => x+y
  | _ => x+2*y

/-- The arithmetic in selectCase supplies only a candidate. The test itself
reads the two coordinates back from the same catalogue used by the rank proof. -/
private def caseOK (c x y : ℕ) : Bool :=
  let m := chamberWidth c x y
  let v := chamberResidue c x y
  if 9 ≤ m ∧ m%2=1 ∧ v < m-2 then
    let i := selectCase (m-2) v
    decide (i < 966 ∧ TightReps.L i=m-2 ∧ TightReps.a i=v)
  else true

private def every (f : ℕ→Bool) : ℕ→Bool
  | 0 => true
  | n+1 => every f n && f n

private theorem every_iff {f : ℕ→Bool} (n : ℕ) :
    every f n=true ↔ ∀ i, i<n → f i=true := by
  induction n with
  | zero => simp [every]
  | succ n ih =>
    rw [every,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨prev,last⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with low | rfl
      · exact prev i low
      · exact last
    · intro all
      exact ⟨fun i hi => all i (Nat.lt_succ_of_lt hi),all n (Nat.lt_succ_self n)⟩

private def rowOK (i : ℕ) := every (caseOK (i/23) (i%23)) 23

private def window (off len : ℕ) := every (fun j => rowOK (off+j)) len

private def Before (n : ℕ) := ∀ i, i<n → rowOK i=true

private theorem before_zero : Before 0 := fun _ h => False.elim (Nat.not_lt_zero _ h)

private theorem next {off len : ℕ} (prev : Before off) (checked : window off len=true) :
    Before (off+len) := by
  intro i hi
  by_cases earlier : i<off
  · exact prev i earlier
  · have localTest := (every_iff len).1 checked (i-off) (by omega)
    simpa only [Nat.add_sub_of_le (by omega : off ≤ i)] using localTest

private structure Cursor (n : ℕ) : Type where
  done : Before n

private def first : Cursor 0 := ⟨before_zero⟩

private def advance {off : ℕ} (prev : Cursor off) (len : ℕ) (checked : window off len=true) :
    Cursor (off+len) := ⟨next prev.done checked⟩

end CriticalConicEvenFinite.TightCoverage

namespace CriticalConicEvenFinite.TightCoverage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked4 : Cursor 4 :=
  advance first 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked8 : Cursor 8 :=
  advance checked4 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked12 : Cursor 12 :=
  advance checked8 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked16 : Cursor 16 :=
  advance checked12 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked20 : Cursor 20 :=
  advance checked16 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked24 : Cursor 24 :=
  advance checked20 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked28 : Cursor 28 :=
  advance checked24 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked32 : Cursor 32 :=
  advance checked28 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked36 : Cursor 36 :=
  advance checked32 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked40 : Cursor 40 :=
  advance checked36 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked44 : Cursor 44 :=
  advance checked40 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked48 : Cursor 48 :=
  advance checked44 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked52 : Cursor 52 :=
  advance checked48 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked56 : Cursor 56 :=
  advance checked52 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked60 : Cursor 60 :=
  advance checked56 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked64 : Cursor 64 :=
  advance checked60 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked68 : Cursor 68 :=
  advance checked64 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked72 : Cursor 72 :=
  advance checked68 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked76 : Cursor 76 :=
  advance checked72 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked80 : Cursor 80 :=
  advance checked76 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked84 : Cursor 84 :=
  advance checked80 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked88 : Cursor 88 :=
  advance checked84 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private def checked92 : Cursor 92 :=
  advance checked88 4 (by decide +kernel)

end CriticalConicEvenFinite.TightCoverage

namespace CriticalConicEvenFinite.TightCoverage

/-- Every physical block in the four bounded chambers reads back at its proper
index in the finite catalogue. -/
theorem _root_.CriticalConicEvenFinite.representative_kernel_tight_of_cases
    (all : ∀ i : Fin 966, CriticalConicEvenSparse.Good (TightReps.L i.val) (TightReps.a i.val)) :
    ∀ L a x y : ℕ, 7 ≤ L → Odd L → a < L → x ≤ 22 → y ≤ 22 →
      ((L+2=3*x+y ∧ a=x) ∨ (L+2=3*x+2*y ∧ a=2*x+y) ∨
       (L+2=2*x+3*y ∧ a=x+y) ∨ (L+2=x+3*y ∧ a=x+2*y)) → CriticalConicEvenSparse.Good L a := by
  intro L a x y large odd inside hx hy chambers
  have pick (c : ℕ) (hc : c < 4) (m : chamberWidth c x y=L+2) (v : chamberResidue c x y=a) :
      CriticalConicEvenSparse.Good L a := by
    have line := checked92.done (23*c+x) (by omega)
    change every (caseOK ((23*c+x)/23) ((23*c+x)%23)) 23=true at line
    have q : (23*c+x)/23=c := by omega
    have r : (23*c+x)%23=x := by omega
    rw [q,r] at line
    have tested := (every_iff 23).1 line y (by omega)
    have parity := Nat.odd_iff.mp odd
    have gate : 9≤L+2 ∧ (L+2)%2=1 ∧ a<(L+2)-2 := by omega
    dsimp only [caseOK] at tested
    rw [m,v,if_pos gate] at tested
    simp only [Nat.add_sub_cancel] at tested
    have eq := of_decide_eq_true tested
    have cert := all ⟨selectCase L a,eq.1⟩
    simpa only [eq.2.1,eq.2.2] using cert
  rcases chambers with ⟨m,v⟩ | ⟨m,v⟩ | ⟨m,v⟩ | ⟨m,v⟩
  · exact pick 0 (by decide) m.symm v.symm
  · exact pick 1 (by decide) m.symm v.symm
  · exact pick 2 (by decide) m.symm v.symm
  · exact pick 3 (by decide) m.symm v.symm

end CriticalConicEvenFinite.TightCoverage

namespace CriticalConicEvenFinite
open CriticalConicEvenSparse

def maskUp (L a : ℕ) : ℕ → ℕ
  | 0 => 0
  | v+1 =>
    let mask := maskUp L a v
    if allowed (L+2) a v ∧ ¬ordinary (L+2) a v then mask ||| (1 <<< v) else mask

def missMask (L a : ℕ) : ℕ :=
  (if 2 ≤ a then 1 <<< (a-2) else 0) ||| (if a ≤ 2 then 1 <<< (a+L-2) else 0)

def tagsUp (freeMask badMask : ℕ) : ℕ → ℕ
  | 0 => 0
  | v+1 =>
    let state := tagsUp freeMask badMask v
    let w := state >>> 5
    let n := state % 32
    if badMask.testBit v then ((w <<< 6) <<< 5) + n
    else if freeMask.testBit v then ((w <<< 6) + 2*(n+1)) * 32 + n+1
    else
      let old := (w >>> 6)%64
      let next := if old=0 then 0 else old ^^^ 1
      ((w <<< 6) + next)*32+n

def flatCode (L packed v : ℕ) : ℤ :=
  let d := (packed >>> (6*(L-v)))%64
  if d%2=0 then ((d/2:ℕ):ℤ) else -((d/2:ℕ):ℤ)

def clearBits (start : ℕ) : ℕ → ℕ
  | 0 => start
  | j+1 => let v := clearBits start j; v &&& (v-1)

def bitAt (start i : ℕ) : ℕ :=
  let v := clearBits start i
  (v-(v &&& (v-1))).log2

def flatChoices (L a k freeMask packed v : ℕ) : Bool :=
  let c := flatCode L packed v
  decide (c.natAbs ≤ k ∧
    (if ¬allowed (L+2) a v then c=0 else
     if freeMask.testBit v then 0<c ∧ bitAt freeMask (c.natAbs-1)=v else
       v < L ∧ ordinary (L+2) a v ∧ c = -flatCode L packed (v-2)))

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite

def offset : ℕ := 1 <<< 319
def widePrefix (f : ℕ → ℤ) : ℕ → ℕ
  | 0 => offset
  | n+1 => let old := widePrefix f n
           let val := (((old % (1 <<< 320) : ℕ):ℤ) + f n).toNat
           (old <<< 320) + val

def atPrefix (endAt word i : ℕ) : ℤ :=
  (((word >>> (320*(endAt-i))) % (1 <<< 320) : ℕ):ℤ) - offset

def fastPrefix (L a : ℕ) (code : ℕ → ℤ) : ℕ → ℕ → ℤ :=
  let f (i j : ℕ) := channel L a i j*tagPower (code j)
  let A := widePrefix (f 0) (L+1)
  let B := widePrefix (f 1) (L+1)
  let C := widePrefix (f 2) (L+1)
  fun i => atPrefix (L+1) (if i=0 then A else if i=1 then B else C)

def testPrefix (L a : ℕ) (code : ℕ → ℤ) (p : ℕ → ℕ → ℤ) (i : ℕ) : Bool :=
  decide (p i 0=0) && allN (fun j => decide (p i (j+1)=p i j+channel L a i j*tagPower (code j))) (L+1)

def fastEvaluate (L a k : ℕ) (code : ℕ → ℤ) (roots rows : ℕ → ℕ) (wanted : ℕ → ℤ) : Bool :=
  let p := fastPrefix L a code
  (allN (labelCheck L a k code roots) (L+1) && allN (testPrefix L a code p) 3) &&
    allN (fun i => let s := rows i; decide (s < L ∧ foldedRow L a code p s=wanted i)) k

lemma allN_complete {f : ℕ → Bool} {n : ℕ} (yes : ∀ i < n,f i=true) : allN f n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact Bool.and_eq_true_iff.mpr ⟨ih fun i lt => yes i (by omega),yes n (by omega)⟩

lemma evaluate_of_fast {L a k : ℕ} (code : ℕ → ℤ) (roots rows : ℕ → ℕ) (wanted : ℕ → ℤ)
    (fast : fastEvaluate L a k code roots rows wanted=true) : evaluate L a k code roots rows wanted=true := by
  let p := fastPrefix L a code
  let slow (i : ℕ) := intSum (fun j => channel L a i j*tagPower (code j))
  have test : (allN (labelCheck L a k code roots) (L+1) && allN (testPrefix L a code p) 3) &&
    allN (fun i => decide (rows i < L ∧ foldedRow L a code p (rows i)=wanted i)) k := fast
  obtain ⟨prior,after⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨shape,good⟩ := Bool.and_eq_true_iff.mp prior
  have pSpec (i : ℕ) (hi : i < 3) : p i 0=0 ∧ ∀ j < L+1,
      p i (j+1)=p i j+channel L a i j*tagPower (code j) := by
    obtain ⟨zero,rest⟩ := Bool.and_eq_true_iff.mp (allN_true good i hi)
    exact ⟨of_decide_eq_true zero,fun j hj => of_decide_eq_true (allN_true rest j hj)⟩
  have sSpec : ∀ i < 3, slow i 0=0 ∧ ∀ j < L+1,slow i (j+1)=slow i j+channel L a i j*tagPower (code j) :=
    fun _ _ => ⟨rfl,fun _ _ => rfl⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨shape,allN_complete fun j hj => ?_⟩
  have both : rows j < L ∧ foldedRow L a code p (rows j)=wanted j :=
    of_decide_eq_true (allN_true after j hj)
  apply decide_eq_true
  refine ⟨both.1,?_⟩
  let s : Fin L := ⟨rows j,both.1⟩
  exact (foldedRow_eq code slow sSpec s).symm.trans ((foldedRow_eq code p pSpec s).trans both.2)

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite

def maskCertificate (L a : ℕ) (c : Fin 198) (bits : ℕ) : Bool :=
  let absent := missMask L a
  let tags := tagsUp bits absent (L+1) >>> 5
  let rows := (absent ||| bits) &&& ((1 <<< L)-1)
  fastEvaluate L a (Catalog.count c) (flatCode L tags) (bitAt bits) (bitAt rows) (Catalog.word c)

theorem good_of_mask {L a : ℕ} (size : L ≤ 213) (c : Fin 198) (bits : ℕ)
    (checked : maskCertificate L a c bits=true) : CriticalConicEvenSparse.Good L a := by
  let absent := missMask L a
  let tags := tagsUp bits absent (L+1) >>> 5
  let rows := (absent ||| bits) &&& ((1 <<< L)-1)
  exact good_of_evaluate size (flatCode L tags) (bitAt bits) (bitAt rows) (Catalog.word c)
    (fun i j : Fin (Catalog.count c) => Catalog.coeff c i.val j.val)
    (fun i j => abs_le.mp (Catalog.bound c i.val j.val)) (fun i => Catalog.word_eq c i.val) (Catalog.regular c)
    (evaluate_of_fast _ _ _ _ checked)

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite

structure CheckedRange (f : ℕ → Bool) (start stop : ℕ) : Type where
  get : ∀ t, start ≤ t → t < stop → f t=true

def CheckedRange.begin (f : ℕ → Bool) (start : ℕ) : CheckedRange f start start := ⟨by intro t a b;omega⟩

def CheckedRange.advance {f : ℕ → Bool} {start stop : ℕ} (old : CheckedRange f start stop) (size : ℕ)
    (done : allN (fun j => f (stop+j)) size=true) : CheckedRange f start (stop+size) := by
  refine ⟨fun t lower upper => ?_⟩
  by_cases prior : t < stop
  · exact old.get t lower prior
  · simpa [Nat.add_sub_of_le (by omega : stop ≤ t)] using allN_true done (t-stop) (by omega)

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite

def autoCheck (i : ℕ) : Bool :=
  let L := TightReps.L i
  let a := TightReps.a i
  maskCertificate L a (TightReps.core i) (maskUp L a (L+1))

set_option maxRecDepth 16000 in
private theorem tight_lengths : ∀ i : Fin 966,TightReps.L i.val ≤ 213 := by decide +kernel

theorem auto_good {i : Fin 966} (check : autoCheck i.val=true) :
    CriticalConicEvenSparse.Good (TightReps.L i.val) (TightReps.a i.val) :=
  good_of_mask (tight_lengths i) _ _ check

end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
namespace AutoWindow0
private abbrev Cursor (i : ℕ) := CheckedRange autoCheck 0 i
private def p0 : Cursor 0 := CheckedRange.begin _ _
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p6 : Cursor 6 := by
  let p := p0
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p12 : Cursor 12 := by
  let p := p6
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p18 : Cursor 18 := by
  let p := p12
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p24 : Cursor 24 := by
  let p := p18
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p30 : Cursor 30 := by
  let p := p24
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p36 : Cursor 36 := by
  let p := p30
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p42 : Cursor 42 := by
  let p := p36
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p48 : Cursor 48 := by
  let p := p42
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p54 : Cursor 54 := by
  let p := p48
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p60 : Cursor 60 := by
  let p := p54
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p66 : Cursor 66 := by
  let p := p60
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p72 : Cursor 72 := by
  let p := p66
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p78 : Cursor 78 := by
  let p := p72
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p84 : Cursor 84 := by
  let p := p78
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p90 : Cursor 90 := by
  let p := p84
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p96 : Cursor 96 := by
  let p := p90
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p102 : Cursor 102 := by
  let p := p96
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p108 : Cursor 108 := by
  let p := p102
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p114 : Cursor 114 := by
  let p := p108
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p120 : Cursor 120 := by
  let p := p114
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p126 : Cursor 126 := by
  let p := p120
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p132 : Cursor 132 := by
  let p := p126
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p138 : Cursor 138 := by
  let p := p132
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
theorem passed : ∀ j, 0 ≤ j → j < 138 → autoCheck j=true := p138.get
end AutoWindow0
end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
namespace AutoWindow138
private abbrev Cursor (i : ℕ) := CheckedRange autoCheck 138 i
private def p138 : Cursor 138 := CheckedRange.begin _ _
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p144 : Cursor 144 := by
  let p := p138
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p150 : Cursor 150 := by
  let p := p144
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p156 : Cursor 156 := by
  let p := p150
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p162 : Cursor 162 := by
  let p := p156
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p168 : Cursor 168 := by
  let p := p162
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p174 : Cursor 174 := by
  let p := p168
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p180 : Cursor 180 := by
  let p := p174
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p186 : Cursor 186 := by
  let p := p180
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p192 : Cursor 192 := by
  let p := p186
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p198 : Cursor 198 := by
  let p := p192
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p204 : Cursor 204 := by
  let p := p198
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p210 : Cursor 210 := by
  let p := p204
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p216 : Cursor 216 := by
  let p := p210
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p222 : Cursor 222 := by
  let p := p216
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p228 : Cursor 228 := by
  let p := p222
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p234 : Cursor 234 := by
  let p := p228
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p240 : Cursor 240 := by
  let p := p234
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p246 : Cursor 246 := by
  let p := p240
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p252 : Cursor 252 := by
  let p := p246
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p258 : Cursor 258 := by
  let p := p252
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p264 : Cursor 264 := by
  let p := p258
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p270 : Cursor 270 := by
  let p := p264
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p276 : Cursor 276 := by
  let p := p270
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
theorem passed : ∀ j, 138 ≤ j → j < 276 → autoCheck j=true := p276.get
end AutoWindow138
end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
namespace AutoWindow276
private abbrev Cursor (i : ℕ) := CheckedRange autoCheck 276 i
private def p276 : Cursor 276 := CheckedRange.begin _ _
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p282 : Cursor 282 := by
  let p := p276
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p288 : Cursor 288 := by
  let p := p282
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p294 : Cursor 294 := by
  let p := p288
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p300 : Cursor 300 := by
  let p := p294
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p306 : Cursor 306 := by
  let p := p300
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p312 : Cursor 312 := by
  let p := p306
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p318 : Cursor 318 := by
  let p := p312
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p324 : Cursor 324 := by
  let p := p318
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p330 : Cursor 330 := by
  let p := p324
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p336 : Cursor 336 := by
  let p := p330
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p342 : Cursor 342 := by
  let p := p336
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p348 : Cursor 348 := by
  let p := p342
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p354 : Cursor 354 := by
  let p := p348
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p360 : Cursor 360 := by
  let p := p354
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p366 : Cursor 366 := by
  let p := p360
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p372 : Cursor 372 := by
  let p := p366
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p378 : Cursor 378 := by
  let p := p372
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p384 : Cursor 384 := by
  let p := p378
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p390 : Cursor 390 := by
  let p := p384
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p396 : Cursor 396 := by
  let p := p390
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p402 : Cursor 402 := by
  let p := p396
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p408 : Cursor 408 := by
  let p := p402
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p414 : Cursor 414 := by
  let p := p408
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
theorem passed : ∀ j, 276 ≤ j → j < 414 → autoCheck j=true := p414.get
end AutoWindow276
end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
namespace AutoWindow414
private abbrev Cursor (i : ℕ) := CheckedRange autoCheck 414 i
private def p414 : Cursor 414 := CheckedRange.begin _ _
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p420 : Cursor 420 := by
  let p := p414
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p426 : Cursor 426 := by
  let p := p420
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p432 : Cursor 432 := by
  let p := p426
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p438 : Cursor 438 := by
  let p := p432
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p444 : Cursor 444 := by
  let p := p438
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p450 : Cursor 450 := by
  let p := p444
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p456 : Cursor 456 := by
  let p := p450
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p462 : Cursor 462 := by
  let p := p456
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p468 : Cursor 468 := by
  let p := p462
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p474 : Cursor 474 := by
  let p := p468
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p480 : Cursor 480 := by
  let p := p474
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p486 : Cursor 486 := by
  let p := p480
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p492 : Cursor 492 := by
  let p := p486
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p498 : Cursor 498 := by
  let p := p492
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p504 : Cursor 504 := by
  let p := p498
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p510 : Cursor 510 := by
  let p := p504
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p516 : Cursor 516 := by
  let p := p510
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p522 : Cursor 522 := by
  let p := p516
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p528 : Cursor 528 := by
  let p := p522
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p534 : Cursor 534 := by
  let p := p528
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p540 : Cursor 540 := by
  let p := p534
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p546 : Cursor 546 := by
  let p := p540
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p552 : Cursor 552 := by
  let p := p546
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
theorem passed : ∀ j, 414 ≤ j → j < 552 → autoCheck j=true := p552.get
end AutoWindow414
end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
namespace AutoWindow552
private abbrev Cursor (i : ℕ) := CheckedRange autoCheck 552 i
private def p552 : Cursor 552 := CheckedRange.begin _ _
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p558 : Cursor 558 := by
  let p := p552
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p564 : Cursor 564 := by
  let p := p558
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p570 : Cursor 570 := by
  let p := p564
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p576 : Cursor 576 := by
  let p := p570
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p582 : Cursor 582 := by
  let p := p576
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p588 : Cursor 588 := by
  let p := p582
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p594 : Cursor 594 := by
  let p := p588
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p600 : Cursor 600 := by
  let p := p594
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p606 : Cursor 606 := by
  let p := p600
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p612 : Cursor 612 := by
  let p := p606
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p618 : Cursor 618 := by
  let p := p612
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p624 : Cursor 624 := by
  let p := p618
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p630 : Cursor 630 := by
  let p := p624
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p636 : Cursor 636 := by
  let p := p630
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p642 : Cursor 642 := by
  let p := p636
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p648 : Cursor 648 := by
  let p := p642
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p654 : Cursor 654 := by
  let p := p648
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p660 : Cursor 660 := by
  let p := p654
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p666 : Cursor 666 := by
  let p := p660
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p672 : Cursor 672 := by
  let p := p666
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p678 : Cursor 678 := by
  let p := p672
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p684 : Cursor 684 := by
  let p := p678
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p690 : Cursor 690 := by
  let p := p684
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
theorem passed : ∀ j, 552 ≤ j → j < 690 → autoCheck j=true := p690.get
end AutoWindow552
end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
namespace AutoWindow690
private abbrev Cursor (i : ℕ) := CheckedRange autoCheck 690 i
private def p690 : Cursor 690 := CheckedRange.begin _ _
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p696 : Cursor 696 := by
  let p := p690
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p702 : Cursor 702 := by
  let p := p696
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p708 : Cursor 708 := by
  let p := p702
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p714 : Cursor 714 := by
  let p := p708
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p720 : Cursor 720 := by
  let p := p714
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p726 : Cursor 726 := by
  let p := p720
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p732 : Cursor 732 := by
  let p := p726
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p738 : Cursor 738 := by
  let p := p732
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p744 : Cursor 744 := by
  let p := p738
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p750 : Cursor 750 := by
  let p := p744
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p756 : Cursor 756 := by
  let p := p750
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p762 : Cursor 762 := by
  let p := p756
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p768 : Cursor 768 := by
  let p := p762
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p774 : Cursor 774 := by
  let p := p768
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p780 : Cursor 780 := by
  let p := p774
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p786 : Cursor 786 := by
  let p := p780
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p792 : Cursor 792 := by
  let p := p786
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p798 : Cursor 798 := by
  let p := p792
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p804 : Cursor 804 := by
  let p := p798
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p810 : Cursor 810 := by
  let p := p804
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p816 : Cursor 816 := by
  let p := p810
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p822 : Cursor 822 := by
  let p := p816
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p828 : Cursor 828 := by
  let p := p822
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
theorem passed : ∀ j, 690 ≤ j → j < 828 → autoCheck j=true := p828.get
end AutoWindow690
end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
namespace AutoWindow828
private abbrev Cursor (i : ℕ) := CheckedRange autoCheck 828 i
private def p828 : Cursor 828 := CheckedRange.begin _ _
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p834 : Cursor 834 := by
  let p := p828
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p840 : Cursor 840 := by
  let p := p834
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p846 : Cursor 846 := by
  let p := p840
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p852 : Cursor 852 := by
  let p := p846
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p858 : Cursor 858 := by
  let p := p852
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p864 : Cursor 864 := by
  let p := p858
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p870 : Cursor 870 := by
  let p := p864
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p876 : Cursor 876 := by
  let p := p870
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p882 : Cursor 882 := by
  let p := p876
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p888 : Cursor 888 := by
  let p := p882
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p894 : Cursor 894 := by
  let p := p888
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p900 : Cursor 900 := by
  let p := p894
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p906 : Cursor 906 := by
  let p := p900
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p912 : Cursor 912 := by
  let p := p906
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p918 : Cursor 918 := by
  let p := p912
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p924 : Cursor 924 := by
  let p := p918
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p930 : Cursor 930 := by
  let p := p924
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p936 : Cursor 936 := by
  let p := p930
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p942 : Cursor 942 := by
  let p := p936
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p948 : Cursor 948 := by
  let p := p942
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p954 : Cursor 954 := by
  let p := p948
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p960 : Cursor 960 := by
  let p := p954
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private def p966 : Cursor 966 := by
  let p := p960
  iterate 6 let p := p.advance 1 (by decide +kernel)
  exact p
theorem passed : ∀ j, 828 ≤ j → j < 966 → autoCheck j=true := p966.get
end AutoWindow828
end CriticalConicEvenFinite

namespace CriticalConicEvenFinite
theorem all_tight_checks (i : Fin 966) : autoCheck i.val = true := by
  by_cases b414 : i.val < 414
  · by_cases b138 : i.val < 138
    · exact AutoWindow0.passed i.val (by omega) (by omega)
    · by_cases b276 : i.val < 276
      · exact AutoWindow138.passed i.val (by omega) (by omega)
      · exact AutoWindow276.passed i.val (by omega) (by omega)
  · by_cases b690 : i.val < 690
    · by_cases b552 : i.val < 552
      · exact AutoWindow414.passed i.val (by omega) (by omega)
      · exact AutoWindow552.passed i.val (by omega) (by omega)
    · by_cases b828 : i.val < 828
      · exact AutoWindow690.passed i.val (by omega) (by omega)
      · exact AutoWindow828.passed i.val (by omega) (by omega)

theorem all_tight_representatives (i : Fin 966) :
    CriticalConicEvenSparse.Good (TightReps.L i.val) (TightReps.a i.val) :=
  auto_good (all_tight_checks i)

theorem representative_kernel_tight :
    ∀ L a x y : ℕ, 7 ≤ L → Odd L → a < L → x ≤ 22 → y ≤ 22 →
      ((L+2=3*x+y ∧ a=x) ∨ (L+2=3*x+2*y ∧ a=2*x+y) ∨
       (L+2=2*x+3*y ∧ a=x+y) ∨ (L+2=x+3*y ∧ a=x+2*y)) → CriticalConicEvenSparse.Good L a :=
  representative_kernel_tight_of_cases all_tight_representatives
end CriticalConicEvenFinite

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2.H2 :=
  CriticalConicEvenBoundary.higher_sharp_even CriticalConicEvenFinite.representative_kernel_tight
