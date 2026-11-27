import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Diameter graphs and bisectors in a critical planar distance set

A diameter graph with no matching of size three has a two-vertex cover or a five-cycle.
In the five-cycle case, all other points are isolated in the diameter graph. Counting isosceles
triangles also forces at least 3n more ordered pairs with two bisector centers than with none.
The two geometric branches retain the distance bounds from every contained regular polygon.
-/

open AffineSubspace EuclideanGeometry OMA.R_Erdos1082_erdos_1082_parts_i_R1

namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1

/-- The diameter contains three pairwise disjoint edges. The bisector counts and the restrictions from regular polygons hold in every remaining configuration. -/
def H1 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) →
    A.card=2*distinctDistances A+2 → 5≤distinctDistances A →
    (∀ (c : ℝ²) (r : ℝ), 3*(A.filter (fun z => dist z c=r)).card≤4*distinctDistances A+2) →
    (let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
    3*A.card+(A.offDiag.filter fun b => k b=0).card ≤ (A.offDiag.filter fun b => k b=2).card) → (∀ (T : Finset Circle) (G : Subgroup Circle) (m : ℕ) (P : Finset ℂ) (f : ℂ→ℝ²) (s : ℝ),
      (G:Set Circle)=T → 2 ≤ m → m.Coprime T.card → 0<s →
      (∀ x y, dist (f x) (f y)=s*dist x y) → (∀ z∈T, f (z:ℂ)∈A) → (∀ p∈P, f p∈A) →
      (∀ p∈P, p≠0 ∧ ‖p‖≠1) → Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ) →
      P.card*T.card+(2*min m 9)*P.card ≤ 2*distinctDistances A+(2*min m 9)*P.card*P.card) →
    ∀ M∈distanceSet A, (∀ d∈distanceSet A, d≤M) →
    (∃ B⊆A, A.card/2≤B.card ∧ ∀ x∈B, ∀ y∈B, dist x y<M) →
    (∃ d∈distanceSet A, A.card+2≤distanceMultiplicity A d) →
    (∃ a b c d e f : A, [a,b,c,d,e,f].Nodup ∧ dist a.1 b.1=M ∧ dist c.1 d.1=M ∧ dist e.1 f.1=M) → ∃ x∈A, ∃ y∈A.erase x, ∃ d∈distanceSet A, d∉distanceSet ((A.erase x).erase y)

/-- The diameter consists of the edges of a five-cycle and a shorter distance occurs at least n+4 times. The general diameter argument below reduces the case without a matching of size three to this case. -/
def H2 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) →
    A.card=2*distinctDistances A+2 → 5≤distinctDistances A →
    (∀ (c : ℝ²) (r : ℝ), 3*(A.filter (fun z => dist z c=r)).card≤4*distinctDistances A+2) →
    (let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
    3*A.card+(A.offDiag.filter fun b => k b=0).card ≤ (A.offDiag.filter fun b => k b=2).card) → (∀ (T : Finset Circle) (G : Subgroup Circle) (m : ℕ) (P : Finset ℂ) (f : ℂ→ℝ²) (s : ℝ),
      (G:Set Circle)=T → 2 ≤ m → m.Coprime T.card → 0<s →
      (∀ x y, dist (f x) (f y)=s*dist x y) → (∀ z∈T, f (z:ℂ)∈A) → (∀ p∈P, f p∈A) →
      (∀ p∈P, p≠0 ∧ ‖p‖≠1) → Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ) →
      P.card*T.card+(2*min m 9)*P.card ≤ 2*distinctDistances A+(2*min m 9)*P.card*P.card) →
    ∀ M∈distanceSet A, (∀ d∈distanceSet A, d≤M) →
    (∃ B⊆A, A.card/2≤B.card ∧ ∀ x∈B, ∀ y∈B, dist x y<M) →
    (∃ d∈(distanceSet A).erase M, A.card+4≤distanceMultiplicity A d) →
    distanceMultiplicity A M≤5 → (∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M) → ∃ x∈A, ∃ y∈A.erase x, ∃ d∈distanceSet A, d∉distanceSet ((A.erase x).erase y)

/-- A regular polygon with k additional points whose positive radii about its center are distinct and different from the polygon radius. For each exponent m coprime to the order, the overlap estimate uses the smaller of 4m and 36. The uniform constant also applies when the polygon order has many small prime factors. -/
def H3 : Prop := ∀ (T : Finset Circle) (G : Subgroup Circle), (G:Set Circle)=T →
    ∀ m : ℕ, 2 ≤ m → m.Coprime T.card → ∀ A P : Finset ℂ, P⊆A → (∀ z∈T, (z:ℂ)∈A) →
    (∀ p∈P, p≠0 ∧ ‖p‖≠1) → Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ) →
    P.card*T.card+(2*min m 9)*P.card ≤ 2*distinctDistances A+(2*min m 9)*P.card*P.card

/-- The finite four-distance range. The three-distance maximum is seven, and the four-distance maximum is nine, by Erdős and Fishburn, Maximum planar sets that determine k distances, Theorem 1, https://doi.org/10.1016/0012-365X(95)00153-N. -/
def H4 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=2*distinctDistances A+2 →
    distinctDistances A≤4 → False

namespace Erdos1082Graph

lemma star_of_no_two {V : Type} (R : V → V → Prop) (sym : ∀ {a b}, R a b → R b a)
    (tri : ¬((fun (R : _ → _ → Prop) => ∃ a b c, R a b ∧ R b c ∧ R a c)) R) (x₀ : V)
    (meets : ∀ a b c d, R a b → R c d → a=c ∨ a=d ∨ b=c ∨ b=d) :
    ∃ x, ∀ a b, R a b → a=x ∨ b=x := by
  classical
  by_cases he : ∃ a b, R a b
  · obtain ⟨a,b,hab⟩ := he
    by_cases hc : ∀ c d, R c d → c=a ∨ d=a
    · exact ⟨a,hc⟩
    push Not at hc
    obtain ⟨c,d,hcd,hca,hda⟩ := hc
    have ht : ∃ t, R b t ∧ t≠a := by
      rcases meets a b c d hab hcd with h|h|h|h
      · exact False.elim (hca h.symm)
      · exact False.elim (hda h.symm)
      · exact ⟨d,h ▸ hcd,hda⟩
      · exact ⟨c,h ▸ sym hcd,hca⟩
    obtain ⟨t,hbt,hta⟩ := ht
    refine ⟨b,?_⟩
    intro x y hxy
    by_contra! hn
    have h₁ := meets a b x y hab hxy
    have h₂ := meets b t x y hbt hxy
    have hat : R a t := by grind
    exact tri ⟨a,b,t,hab,hbt,hat⟩
  · exact ⟨x₀,fun a b h => False.elim (he ⟨a,b,h⟩)⟩

lemma cover_of_leaf {V : Type} (R : V → V → Prop) (sym : ∀ {a b}, R a b → R b a)
    (irr : ∀ a, ¬R a a) (tri : ¬((fun (R : _ → _ → Prop) => ∃ a b c, R a b ∧ R b c ∧ R a c)) R) (mat : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e f, [a,b,c,d,e,f].Nodup ∧
  R a b ∧ R c d ∧ R e f)) R)
    (a b : V) (hab : R a b) (leaf : ∀ x, R a x → x=b) : ∃ x y, ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R x y := by
  let Q (x y : V) := R x y ∧ x≠b ∧ y≠b
  have hq (x y : V) (h : Q x y) : x≠a ∧ y≠a := by
    exact ⟨fun he => h.2.2 (leaf y (he ▸ h.1)),fun he => h.2.1 (leaf x (he ▸ sym h.1))⟩
  have ht : ¬((fun (R : _ → _ → Prop) => ∃ a b c, R a b ∧ R b c ∧ R a c)) Q := by
    rintro ⟨x,y,z,h1,h2,h3⟩
    exact tri ⟨x,y,z,h1.1,h2.1,h3.1⟩
  have meets (x y z w : V) (hxy : Q x y) (hzw : Q z w) : x=z ∨ x=w ∨ y=z ∨ y=w := by
    by_contra! h
    apply mat
    refine ⟨a,b,x,y,z,w,?_,hab,hxy.1,hzw.1⟩
    obtain ⟨hx,hy⟩ := hq _ _ hxy
    obtain ⟨hz,hw⟩ := hq _ _ hzw
    have hne {u v : V} (he : R u v) : u≠v := by rintro rfl; exact irr _ he
    have := hne hab
    have := hne hxy.1
    have := hne hzw.1
    simp only [Q] at hxy hzw
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]
    grind
  obtain ⟨c,hc⟩ := star_of_no_two Q (fun h => ⟨sym h.1,h.2.2,h.2.1⟩) ht a meets
  refine ⟨b,c,?_⟩
  intro x y hxy
  by_cases hx : x=b
  · exact Or.inl hx
  by_cases hy : y=b
  · exact Or.inr (Or.inr (Or.inl hy))
  rcases hc _ _ ⟨hxy,hx,hy⟩ with h|h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))


lemma cover_of_square {V : Type} (R : V → V → Prop) (sym : ∀ {a b}, R a b → R b a)
    (irr : ∀ a, ¬R a a) (tri : ¬((fun (R : _ → _ → Prop) => ∃ a b c, R a b ∧ R b c ∧ R a c)) R) (mat : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e f, [a,b,c,d,e,f].Nodup ∧
  R a b ∧ R c d ∧ R e f)) R)
    (a b c d : V) (nd : [a,b,c,d].Nodup) (ab : R a b) (bc : R b c) (cd : R c d) (da : R d a) :
    ∃ x y, ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R x y := by
  classical
  have ntri {x y z : V} (hx : R x y) (hy : R y z) (hz : R x z) : False := tri ⟨x,y,z,hx,hy,hz⟩
  have nmat {x y u v k l : V} (h₁ : R x y) (h₂ : R u v) (h₃ : R k l)
      (dd : [x,y,u,v,k,l].Nodup) : False := mat ⟨x,y,u,v,k,l,dd,h₁,h₂,h₃⟩
  have extEdge (a b c d : V) (nd : [a,b,c,d].Nodup) (ab : R a b) (bc : R b c)
      (cd : R c d) (da : R d a) (hc : ¬((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R a c) :
      ∃ w, w≠a ∧ w≠b ∧ w≠c ∧ w≠d ∧ (R b w ∨ R d w) := by
    push Not at hc
    obtain ⟨x,y,hxy,hxa,hxc,hya,hyc⟩ := hc
    have hnxy : x≠y := by rintro rfl; exact irr _ hxy
    have hbd : ¬R b d := fun h => ntri ab h (sym da)
    have nd' := nd
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true] at nd'
    have hhit : x=b ∨ x=d ∨ y=b ∨ y=d := by
      by_contra! hn
      apply nmat ab cd hxy
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]
      grind
    rcases hhit with h|h|h|h
    · subst x
      exact ⟨y,hya,hnxy.symm,hyc,(fun h => hbd (h ▸ hxy)),Or.inl hxy⟩
    · subst x
      exact ⟨y,hya,(fun h => hbd (h ▸ sym hxy)),hyc,hnxy.symm,Or.inr hxy⟩
    · subst y
      exact ⟨x,hxa,hnxy,hxc,(fun h => hbd (h ▸ sym hxy)),Or.inl (sym hxy)⟩
    · subst y
      exact ⟨x,hxa,(fun h => hbd (h ▸ hxy)),hxc,hnxy,Or.inr (sym hxy)⟩
  by_cases hac : ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R a c
  · exact ⟨a,c,hac⟩
  by_cases hbd : ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R b d
  · exact ⟨b,d,hbd⟩
  obtain ⟨x,hxa,hxb,hxc,hxd,hx⟩ := extEdge a b c d nd ab bc cd da hac
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true] at nd
  obtain ⟨y,hyb,hyc,hyd,hya,hy⟩ := extEdge b c d a (by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind) bc cd da ab hbd
  exfalso
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · have hne : x≠y := by rintro rfl; exact ntri bc hy hx
    apply nmat hx hy da
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
  · have hne : x≠y := by rintro rfl; exact ntri ab hx hy
    apply nmat hx hy cd
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
  · have hne : x≠y := by rintro rfl; exact ntri cd hx hy
    apply nmat hx hy ab
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
  · have hne : x≠y := by rintro rfl; exact ntri da hy hx
    apply nmat hx hy bc
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind


lemma cover_of_triangle {V : Type} (R : V → V → Prop) (sym : ∀ {a b}, R a b → R b a)
    (irr : ∀ a, ¬R a a) (mat : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e f, [a,b,c,d,e,f].Nodup ∧
  R a b ∧ R c d ∧ R e f)) R) (triedge : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e, [a,b,c,d,e].Nodup ∧
  R a b ∧ R b c ∧ R a c ∧ R d e)) R)
    (clique : ¬((fun (R : _ → _ → Prop) => ∃ a b c d, [a,b,c,d].Nodup ∧
  R a b ∧ R a c ∧ R a d ∧ R b c ∧ R b d ∧ R c d)) R) (a b c : V) (ab : R a b) (bc : R b c) (ac : R a c) :
    ∃ x y, ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R x y := by
  classical
  have rne {x y : V} (hh : R x y) : x≠y := by rintro rfl; exact irr _ hh
  have next (a b c : V) (ab : R a b) (bc : R b c) (ac : R a c) (hcov : ¬((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R a b) :
      ∃ x, x≠a ∧ x≠b ∧ x≠c ∧ R c x := by
    push Not at hcov
    obtain ⟨x,y,hr,hxa,hxb,hya,hyb⟩ := hcov
    by_cases hx : x=c
    · subst x; exact ⟨y,hya,hyb,(rne hr).symm,hr⟩
    by_cases hy : y=c
    · subst y; exact ⟨x,hxa,hxb,rne hr,sym hr⟩
    exfalso
    apply triedge
    refine ⟨a,b,c,x,y,?_,ab,bc,ac,hr⟩
    have := rne ab; have := rne bc; have := rne ac; have := rne hr
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
  by_cases hx : ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R a b
  · exact ⟨a,b,hx⟩
  by_cases hy : ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R b c
  · exact ⟨b,c,hy⟩
  by_cases hz : ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R a c
  · exact ⟨a,c,hz⟩
  obtain ⟨x,hxb,hxc,hxa,hax⟩ := next b c a bc (sym ac) (sym ab) hy
  obtain ⟨y,hya,hyc,hyb,hby⟩ := next a c b ac (sym bc) ab hz
  obtain ⟨z,hza,hzb,hzc,hcz⟩ := next a b c ab bc ac hx
  have := rne ab; have := rne bc; have := rne ac
  exfalso
  have sharedNeighbor (a b c x z : V) (ab : R a b) (ac : R a c) (bc : R b c) (ax : R a x) (bx : R b x)
      (cz : R c z) (xa : x≠a) (xb : x≠b) (xc : x≠c) (za : z≠a) (zb : z≠b) (zc : z≠c) : False := by
    have := rne ab; have := rne bc; have := rne ac
    by_cases hxz : x=z
    · subst z
      apply clique
      refine ⟨a,b,c,x,?_,ab,ac,ax,bc,bx,cz⟩
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
    · apply triedge
      refine ⟨a,b,x,c,z,?_,ab,bx,ax,cz⟩
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
  by_cases hxy : x=y
  · subst y; exact sharedNeighbor a b c x z ab ac bc hax hby hcz hxa hxb hxc hza hzb hzc
  by_cases hxz : x=z
  · subst z; exact sharedNeighbor a c b x y ac ab (sym bc) hax hcz hby hxa hxc hxb hya hyc hyb
  by_cases hyz : y=z
  · subst z; exact sharedNeighbor b c a y x bc (sym ab) (sym ac) hby hcz hax hyb hyc hya hxb hxc hxa
  apply mat
  refine ⟨a,x,b,y,c,z,?_,hax,hby,hcz⟩
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind


lemma obstruction {V : Type} (R : V → V → Prop) (sym : ∀ {a b}, R a b → R b a)
    (irr : ∀ a, ¬R a a) (base : V) (mat : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e f, [a,b,c,d,e,f].Nodup ∧
  R a b ∧ R c d ∧ R e f)) R) (pent : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e, [a,b,c,d,e].Nodup ∧
  R a b ∧ R b c ∧ R c d ∧ R d e ∧ R e a)) R)
    (te : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e, [a,b,c,d,e].Nodup ∧
  R a b ∧ R b c ∧ R a c ∧ R d e)) R) (four : ¬((fun (R : _ → _ → Prop) => ∃ a b c d, [a,b,c,d].Nodup ∧
  R a b ∧ R a c ∧ R a d ∧ R b c ∧ R b d ∧ R c d)) R) : ∃ a b, ((fun (R : _ → _ → Prop) a b => ∀ x y, R x y → x=a ∨ x=b ∨ y=a ∨ y=b)) R a b := by
  classical
  by_cases ht : ((fun (R : _ → _ → Prop) => ∃ a b c, R a b ∧ R b c ∧ R a c)) R
  · obtain ⟨a,b,c,ab,bc,ac⟩ := ht
    exact cover_of_triangle R sym irr mat te four a b c ab bc ac
  by_cases hl : ∃ a b, R a b ∧ ∀ x, R a x → x=b
  · obtain ⟨a,b,ab,hleaf⟩ := hl
    exact cover_of_leaf R sym irr ht mat a b ab hleaf
  by_cases hstart : ∃ x y, R x y
  · obtain ⟨a,b,ab⟩ := hstart
    have grow (x y : V) (hxy : R x y) : ∃ z, R y z ∧ z≠x := by
      by_contra! h
      exact hl ⟨y,x,sym hxy,h⟩
    have rne {x y : V} (hh : R x y) : x≠y := by rintro rfl; exact irr _ hh
    have ntri {x y z : V} (hxy : R x y) (hyz : R y z) : ¬R x z := fun hxz => ht ⟨x,y,z,hxy,hyz,hxz⟩
    obtain ⟨c,bc,hca⟩ := grow a b ab
    obtain ⟨d,cd,hdb⟩ := grow b c bc
    have hda : d≠a := fun he => ntri ab bc (he ▸ sym cd)
    have := rne ab; have := rne bc; have := rne cd
    obtain ⟨e,de,hec⟩ := grow c d cd
    have heb : e≠b := fun h => ntri bc cd (h ▸ sym de)
    have := rne de
    by_cases hea : e=a
    · subst e
      apply cover_of_square R sym irr ht mat a b c d _ ab bc cd de
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
    obtain ⟨f,ef,hfd⟩ := grow d e de
    have hfc : f≠c := fun h => ntri cd de (h ▸ sym ef)
    have := rne ef
    by_cases hfb : f=b
    · subst f
      apply cover_of_square R sym irr ht mat b c d e _ bc cd de ef
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
    by_cases hfa : f=a
    · subst f; exfalso; apply pent
      refine ⟨a,b,c,d,e,?_,ab,bc,cd,de,ef⟩
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
    exfalso; apply mat
    refine ⟨a,b,c,d,e,f,?_,ab,cd,ef⟩
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind
  · exact ⟨base,base,fun x y h => False.elim (hstart ⟨x,y,h⟩)⟩

end Erdos1082Graph
open EuclideanGeometry OMA.R_Erdos1082_erdos_1082_parts_i_R1

namespace Erdos1082Diameter

lemma lens_re (x : ℂ) (ha : ‖x‖≤1) (hb : ‖x-1‖≤1) (h0 : x≠0) (h1 : x≠1) :
    0<x.re ∧ x.re<1 := by
  have hA : x.re^2+x.im^2 ≤ 1 := by
    have h := Complex.sq_norm x
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg x]
  have hB : (x.re-1)^2+x.im^2 ≤ 1 := by
    have h := Complex.sq_norm (x-1)
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero] at h
    nlinarith [norm_nonneg (x-1)]
  constructor
  · by_contra! hn
    have hx : x.re=0 := by nlinarith [sq_nonneg x.im,sq_nonneg x.re]
    have hy : x.im=0 := by nlinarith [sq_nonneg x.im]
    exact h0 (Complex.ext (by simpa using hx) (by simpa using hy))
  · by_contra! hn
    have hx : x.re=1 := by nlinarith [sq_nonneg x.im,sq_nonneg (x.re-1)]
    have hy : x.im=0 := by nlinarith [sq_nonneg x.im]
    exact h1 (Complex.ext (by simpa using hx) (by simpa using hy))

lemma one_side_distance (x y : ℂ) (hx : 0 < x.re) (hx' : x.re<1) (hy : 0<y.re) (hy' : y.re<1)
    (h0x : ‖x‖≤1) (h1x : ‖x-1‖≤1) (h0y : ‖y‖≤1) (h1y : ‖y-1‖≤1)
    (hside : 0≤x.im*y.im) : dist x y<1 := by
  have hnorm (z : ℂ) (hz : ‖z‖≤1) : z.re^2+z.im^2≤1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  have hsq := Complex.sq_norm (x-y)
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at hsq
  have hI : (x.im-y.im)^2 ≤ max (x.im^2) (y.im^2) := by
    rcases le_total (x.im^2) (y.im^2) with h|h
    · rw [max_eq_right h]
      by_cases hi : x.im≤y.im
      · nlinarith [sq_nonneg x.im,sq_nonneg y.im,
          mul_nonneg (show 0≤(y.im-x.im) by linarith) (show 0 ≤ (y.im-x.im) by linarith)]
      · nlinarith [sq_nonneg x.im,sq_nonneg y.im]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg x.im,sq_nonneg y.im]
  have hf (a b : ℝ) (ha : 0<a) (ha' : a<1) (hb : 0<b) (hb' : b<1) :
      (a-b)^2 < max (b^2) ((1-b)^2) := by
    rcases le_total a b with h|h
    · exact lt_of_lt_of_le (by nlinarith [mul_pos ha (by linarith : 0<2*b-a)]) (le_max_left _ _)
    · exact lt_of_lt_of_le (by nlinarith [mul_pos (show 0<1-a by linarith) (show 0<1+a-2*b by linarith)]) (le_max_right _ _)
  have hbound (z : ℂ) (hh : ‖z‖≤1) (hhh : ‖z-1‖≤1) :
      max (z.re^2) ((1-z.re)^2)+z.im^2 ≤ 1 := by
    have h0 := hnorm z hh
    have h1 := hnorm (z-1) hhh
    simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at h1
    rcases le_total (z.re^2) ((1-z.re)^2) with h|h <;> simp only [max_eq_right h,max_eq_left h] <;> nlinarith
  rw [dist_eq_norm]
  rcases le_total (x.im^2) (y.im^2) with h|h
  · rw [max_eq_right h] at hI
    nlinarith [hf x.re y.re hx hx' hy hy',hbound y h0y h1y,sq_nonneg (‖x-y‖-1)]
  · rw [max_eq_left h] at hI
    nlinarith [hf y.re x.re hy hy' hx hx',hbound x h0x h1x,sq_nonneg (‖x-y‖-1)]


lemma opposite_diameters (x y : ℂ) (hx : x.re<1) (hy : 0<y.re) (hside : x.im*y.im ≤ 0)
    (hax : ‖x‖=1) (hby : ‖y-1‖=1) : 1<dist x y := by
  have h₁ := Complex.sq_norm x
  have h₂ := Complex.sq_norm (y-1)
  have h₃ := Complex.sq_norm (x-y)
  simp only [hax,hby,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,sub_zero,one_pow] at h₁ h₂ h₃
  rw [dist_eq_norm]
  nlinarith [mul_pos (show 0<1-x.re by linarith) hy,norm_nonneg (x-y)]

lemma diameter_sides (A : Finset ℝ²) (M : ℝ) (hM : 0<M)
    (hm : ∀ x y : A, dist x.1 y.1≤M) (a b : A) (hab : dist a.1 b.1=M) :
    ∃ s : A → Bool, ∀ x y : A, x≠a → x≠b → y≠a → y≠b →
      (dist x.1 y.1 = M → s x≠s y) ∧ (dist a.1 x.1=M → dist b.1 y.1=M → s x=s y) := by
  classical
  let E := Complex.orthonormalBasisOneI.repr.symm
  let v := E (b.1-a.1)
  have hvnorm : ‖v‖=M := by dsimp [v]; rw [E.norm_map,←dist_eq_norm,dist_comm,hab]
  have hv : v≠0 := by intro h; rw [h,norm_zero] at hvnorm; linarith
  let f (x : A) := E (x.1-a.1)/v
  have hdist (x y : A) : dist (f x) (f y)= dist x.1 y.1/M := by
    rw [dist_eq_norm]
    dsimp only [f]
    rw [←sub_div,norm_div,←map_sub,E.norm_map,hvnorm,show (x.1-a.1)-(y.1-a.1)=x.1-y.1 by abel,dist_eq_norm]
  have hf : Function.Injective f := by
    intro x y h
    have hh := hdist x y
    rw [h,dist_self] at hh
    exact Subtype.ext (dist_eq_zero.mp ((div_eq_zero_iff.mp hh.symm).resolve_right hM.ne'))
  have hfa : f a=0 := by simp [f]
  have hfb : f b=1 := by change v/v=1; exact div_self hv
  have near (x y : A) : dist (f x) (f y)≤1 := by rw [hdist,div_le_one hM]; exact hm _ _
  have hlens (x : A) (hxa : x≠a) (hxb : x≠b) : ‖f x‖≤1 ∧ ‖f x-1‖≤1 ∧ 0<(f x).re ∧ (f x).re<1 := by
    have h0 := near x a; have h1 := near x b
    rw [hfa,dist_zero_right] at h0; rw [hfb,dist_eq_norm] at h1
    exact ⟨h0,h1,lens_re _ h0 h1 (fun h => hxa (hf (h.trans hfa.symm))) (fun h => hxb (hf (h.trans hfb.symm)))⟩
  refine ⟨fun x => decide (0≤(f x).im),?_⟩
  intro x y xa xb ya yb
  obtain ⟨x0,x1,xp,xm⟩ := hlens x xa xb
  obtain ⟨y0,y1,yp,ym⟩ := hlens y ya yb
  constructor
  · intro hxy he
    have hside : 0≤(f x).im*(f y).im := by
      by_cases hx : 0≤(f x).im <;> by_cases hy : 0≤(f y).im <;> simp [hx,hy] at he
      · exact mul_nonneg hx hy
      · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx) (le_of_not_ge hy)
    have hnear := one_side_distance _ _ xp xm yp ym x0 x1 y0 y1 hside
    rw [hdist,hxy,div_self hM.ne'] at hnear
    exact lt_irrefl _ hnear
  · intro hax hby
    by_contra h
    have hs : (f x).im*(f y).im≤0 := by
      by_cases hx : 0≤(f x).im <;> by_cases hy : 0≤(f y).im <;> simp [hx,hy] at h
      · exact mul_nonpos_of_nonneg_of_nonpos hx (le_of_not_ge hy)
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) hy
    have hx := hdist a x; have hy := hdist y b
    rw [hfa,dist_zero_left,hax,div_self hM.ne'] at hx
    rw [hfb,dist_eq_norm,dist_comm y.1 b.1,hby,div_self hM.ne'] at hy
    exact (not_lt_of_ge (near x y)) (opposite_diameters _ _ xm yp hs hx hy)

lemma diameter_exclusions (A : Finset ℝ²) (M : ℝ) (hM : 0<M)
    (hm : ∀ x y : A, dist x.1 y.1≤M) :
    ¬ ((fun (R : _ → _ → Prop) => ∃ a b c d e, [a,b,c,d,e].Nodup ∧
  R a b ∧ R b c ∧ R a c ∧ R d e)) (fun x y : A => dist x.1 y.1=M) ∧
    ¬ ((fun (R : _ → _ → Prop) => ∃ a b c d, [a,b,c,d].Nodup ∧
  R a b ∧ R a c ∧ R a d ∧ R b c ∧ R b d ∧ R c d)) (fun x y : A => dist x.1 y.1=M) := by
  constructor
  · rintro ⟨x,y,z,a,b,nd,xy,yz,xz,ab⟩
    obtain ⟨s,hs⟩ := diameter_sides A M hM hm a b ab
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true] at nd
    have h₁ := (hs x y (by grind) (by grind) (by grind) (by grind)).1 xy
    have h₂ := (hs y z (by grind) (by grind) (by grind) (by grind)).1 yz
    have h₃ := (hs x z (by grind) (by grind) (by grind) (by grind)).1 xz
    cases hₓ : s x <;> cases hᵧ : s y <;> cases h𝓏 : s z <;> simp_all
  · rintro ⟨a,b,x,y,nd,ab,ax,_,_,byy,xy⟩
    obtain ⟨s,hs⟩ := diameter_sides A M hM hm a b ab
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true] at nd
    obtain ⟨hsep,hopp⟩ := hs x y (by grind) (by grind) (by grind) (by grind)
    exact hsep xy (hopp ax byy)


lemma diameter_small_cover (A : Finset ℝ²) (d : ℝ) (hd : d∈distanceSet A)
    (hmax : ∀ l∈distanceSet A, l≤d)
    (mat : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e f, [a,b,c,d,e,f].Nodup ∧
  R a b ∧ R c d ∧ R e f)) (fun x y : A => dist x.1 y.1=d))
    (pent : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e, [a,b,c,d,e].Nodup ∧
  R a b ∧ R b c ∧ R c d ∧ R d e ∧ R e a)) (fun x y : A => dist x.1 y.1=d)) :
    ∃ x ∈ A, ∃ y ∈ A.erase x, d ∉ distanceSet ((A.erase x).erase y) := by
  classical
  obtain ⟨⟨u,v⟩,huv,he⟩ := Finset.mem_image.mp hd
  obtain ⟨hu,hv,huv⟩ := Finset.mem_offDiag.mp huv
  change dist u v=d at he
  have hdpos := (dist_pos.mpr huv).trans_eq he
  let R (a b : A) := dist a.1 b.1=d
  have hm (x y : A) : dist x.1 y.1≤d := by
    by_cases h : x.1=y.1
    · simpa [h] using hdpos.le
    · exact hmax _ (dist_mem x.2 y.2 h)
  obtain ⟨te,four⟩ := diameter_exclusions A d hdpos hm
  obtain ⟨x,y,hxy⟩ := Erdos1082Graph.obstruction R (fun {a b} h => (dist_comm b.1 a.1).trans h)
    (fun a (h : dist a.1 a.1=d) => hdpos.ne ((dist_self a.1).symm.trans h))
    ⟨u,hu⟩ mat pent te four
  have erase (y' : A) (hy' : y'≠x) (hh : ∀ i j : A, R i j → i=x ∨ i=y' ∨ j=x ∨ j=y') :
      ∃ x ∈ A, ∃ y ∈ A.erase x, d ∉ distanceSet ((A.erase x).erase y) := by
    refine ⟨x,x.2,y',Finset.mem_erase.mpr ⟨fun h => hy' (Subtype.ext h), y'.2⟩,?_⟩
    rintro h
    obtain ⟨⟨i,j⟩,hij,hid⟩ := Finset.mem_image.mp h
    obtain ⟨hi,hj,_⟩ := Finset.mem_offDiag.mp hij
    obtain ⟨hiy,hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hix,hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hjy,hj⟩ := Finset.mem_erase.mp hj
    obtain ⟨hjx,hj⟩ := Finset.mem_erase.mp hj
    rcases hh ⟨i,hi⟩ ⟨j,hj⟩ hid with he|he|he|he
    · exact hix (congrArg Subtype.val he)
    · exact hiy (congrArg Subtype.val he)
    · exact hjx (congrArg Subtype.val he)
    · exact hjy (congrArg Subtype.val he)
  by_cases h : y=x
  · subst y
    have ex : ∃ z : A, z≠x := by
      by_cases hh : (⟨u,hu⟩:A)=x
      · exact ⟨⟨v,hv⟩,fun hh' => huv (congrArg Subtype.val (hh.trans hh'.symm))⟩
      · exact ⟨⟨u,hu⟩,hh⟩
    obtain ⟨z,hz⟩ := ex
    exact erase z hz (fun i j h => by rcases hxy i j h with h|h|h|h <;> tauto)
  · exact erase y h hxy

set_option maxHeartbeats 1500000 in
lemma pentagon_multiplicity (A : Finset ℝ²) (d : ℝ) (hd : 0<d)
    (hm : ∀ x y : A, dist x.1 y.1≤d)
    (mat : ¬((fun (R : _ → _ → Prop) => ∃ a b c d e f, [a,b,c,d,e,f].Nodup ∧
  R a b ∧ R c d ∧ R e f)) (fun x y : A => dist x.1 y.1=d))
    (pent : ((fun (R : _ → _ → Prop) => ∃ a b c d e, [a,b,c,d,e].Nodup ∧
  R a b ∧ R b c ∧ R c d ∧ R d e ∧ R e a)) (fun x y : A => dist x.1 y.1=d)) :
    distanceMultiplicity A d≤5 := by
  classical
  let R (x y : A) := dist x.1 y.1=d
  obtain ⟨te,_⟩ := diameter_exclusions A d hd hm
  obtain ⟨a,b,c,e,f,nd,ab,bc,ce,ef,fa⟩ := pent
  have rs {x y : A} (h : R x y) : R y x := (dist_comm y.1 x.1).trans h
  have irr {x y : A} (h : R x y) : x≠y := by rintro rfl; exact hd.ne ((dist_self x.1).symm.trans h)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true] at nd
  have member (x y : A) (hxy : R x y) : x=a ∨ x=b ∨ x=c ∨ x=e ∨ x=f := by
    by_contra! hn
    have hit (p q u v : A) (hpq : R p q) (huv : R u v) (hnd : [p,q,u,v,x].Nodup) :
        y=p ∨ y=q ∨ y=u ∨ y=v := by
      by_contra! hy
      apply mat
      refine ⟨p,q,u,v,x,y,?_,hpq,huv,hxy⟩
      have := irr hxy
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true] at hnd ⊢
      grind
    have h₁ := hit a b c e ab ce (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
    have h₂ := hit b c e f bc ef (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
    have h₃ := hit c e f a ce fa (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
    have h₄ := hit e f a b ef ab (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
    have h₅ := hit f a b c fa bc (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
    grind
  have noChord (p q u v w : A) (hpq : R p q) (hqu : R q u) (hvw : R v w)
      (nd : [p,q,u,v,w].Nodup) : ¬R p u := fun h => te ⟨p,q,u,v,w,nd,hpq,hqu,h,hvw⟩
  have h₁ := noChord a b c e f ab bc ef (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
  have h₂ := noChord b c e f a bc ce fa (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
  have h₃ := noChord c e f a b ce ef ab (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
  have h₄ := noChord e f a b c ef fa bc (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
  have h₅ := noChord f a b c e fa ab ce (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true]; grind)
  let L : List (ℝ² × ℝ²) := [(a.1,b.1),(b.1,a.1),(b.1,c.1),(c.1,b.1),(c.1,e.1),(e.1,c.1),(e.1,f.1),(f.1,e.1),(f.1,a.1),(a.1,f.1)]
  have hs : (A.offDiag.filter fun p => dist p.1 p.2=d) ⊆ L.toFinset := by
    rintro ⟨x,y⟩ h
    obtain ⟨ho,hxy⟩ := Finset.mem_filter.mp h
    obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.mp ho
    let i : A := ⟨x,hx⟩
    let j : A := ⟨y,hy⟩
    have hij : R i j := hxy
    have hji := rs hij
    have hne := irr hij
    have hi := member i j hij
    have hj := member j i hji
    change (i.1,j.1)∈L.toFinset
    simp only [List.mem_toFinset,L,List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with h|h|h|h|h <;> rcases hj with k|k|k|k|k <;> simp only [h,k] at hne hij hji ⊢ <;> first | tauto | simp
  have hh := (Finset.card_le_card hs).trans L.toFinset_card_le
  change (A.offDiag.filter fun p => dist p.1 p.2=d).card / 2 ≤ 5
  change (A.offDiag.filter fun p => dist p.1 p.2=d).card ≤ 10 at hh
  omega


lemma pentagon_heavy (A : Finset ℝ²) (hcard : A.card=2*distinctDistances A+2)
    (d : ℝ) (hd : d∈distanceSet A) (hfew : distanceMultiplicity A d≤5) :
    ∃ r∈(distanceSet A).erase d, A.card+4≤distanceMultiplicity A r := by
  classical
  by_contra! hall
  have hsum := Finset.sum_le_sum (s := (distanceSet A).erase d)
    (g:= fun _ => A.card+3) (fun r hr => Nat.le_of_lt_succ (hall r hr))
  have hsplit := Finset.sum_erase_add (s:=distanceSet A) (distanceMultiplicity A) hd
  rw [sum_distanceMultiplicity,Nat.choose_two_right] at hsplit
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have he := Finset.card_erase_add_one hd
  change ((distanceSet A).erase d).card+1=distinctDistances A at he
  rw [hcard] at hsplit hsum
  have hh : (2*distinctDistances A+2)-1=2*distinctDistances A+1 := by omega
  rw [hh] at hsplit
  have ht : (2*distinctDistances A+2)*(2*distinctDistances A+1) =
      2*((distinctDistances A+1)*(2*distinctDistances A+1)) := by ring
  rw [ht,Nat.mul_div_cancel_left _ (by decide : 0<2)] at hsplit
  have hm := congrArg (fun n : ℕ => n*(2*distinctDistances A+5)) he
  nlinarith


lemma avoid_normalized_diameter {α : Type*} (A : Finset α) (a b : α) (ha : a∈A) (hb : b∈A)
    (f : α→ℂ) (hf : Function.Injective f) (hfa : f a=0) (hfb : f b=1)
    (hbound : ∀ x∈A, ∀ y∈A, dist (f x) (f y)≤1) :
    ∃ B ⊆ A, A.card/2 ≤ B.card ∧ ∀ x∈B, ∀ y∈B, dist (f x) (f y)<1 := by
  classical
  have hab : a≠b := by intro h; rw [h,hfb] at hfa; exact one_ne_zero hfa
  let P := (A.erase a).erase b
  have hbp : b ∈ A.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  have hcard : P.card + 2 = A.card := by
    have h₁ := Finset.card_erase_add_one ha
    have h₂ := Finset.card_erase_add_one hbp
    dsimp only [P]; omega
  have hmem {x : α} (hx : x∈P) : x∈A ∧ x≠a ∧ x≠b := by
    obtain ⟨hxb,hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxa,hx⟩ := Finset.mem_erase.mp hx
    exact ⟨hx,hxa,hxb⟩
  have hlens (x : α) (hx : x∈P) : ‖f x‖≤1 ∧ ‖f x-1‖≤1 ∧ 0<(f x).re ∧ (f x).re<1 := by
    have hm := hmem hx
    have h0 := hbound x hm.1 a ha
    have h1 := hbound x hm.1 b hb
    rw [hfa,dist_zero_right] at h0
    rw [hfb,dist_eq_norm] at h1
    exact ⟨h0,h1,lens_re (f x) h0 h1 (fun h => hm.2.1 (hf (h.trans hfa.symm))) (fun h => hm.2.2 (hf (h.trans hfb.symm)))⟩
  let U := P.filter (fun x => 0≤(f x).im)
  let V := P.filter (fun x => ¬0≤(f x).im)
  have hsum : U.card+V.card=P.card := Finset.card_filter_add_card_filter_not (s:=P) _
  have small (x : α) (hx : x∈P) (y : α) (hy : y∈P) (hside : 0≤(f x).im*(f y).im) : dist (f x) (f y)<1 := by
    obtain ⟨ha,hb,hx,hx'⟩ := hlens x hx
    obtain ⟨hc,hd,hy,hy'⟩ := hlens y hy
    exact one_side_distance _ _ hx hx' hy hy' ha hb hc hd hside
  have hU : ∀ x∈U, ∀ y∈U, dist (f x) (f y)<1 := by
    intro x hx y hy
    obtain ⟨hx,hx'⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy,hy'⟩ := Finset.mem_filter.mp hy
    exact small x hx y hy (mul_nonneg hx' hy')
  have hV : ∀ x∈V, ∀ y∈V, dist (f x) (f y)<1 := by
    intro x hx y hy
    obtain ⟨hx,hx'⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy,hy'⟩ := Finset.mem_filter.mp hy
    exact small x hx y hy (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx') (le_of_not_ge hy'))
  have subU : U ⊆ A := fun _ hx => (hmem (Finset.mem_filter.mp hx).1).1
  have subV : V ⊆ A := fun _ hx => (hmem (Finset.mem_filter.mp hx).1).1
  by_cases hu : A.card/2 ≤ U.card
  · exact ⟨U,subU,hu,hU⟩
  by_cases hv : A.card/2 ≤ V.card
  · exact ⟨V,subV,hv,hV⟩
  have extend (Q : Finset α) (hs : Q ⊆ A) (c : α) (hc : c∈A) (hnot : c∉Q) (hle : A.card/2 ≤ Q.card+1)
      (hQ : ∀ x∈Q, ∀ y∈Q, dist (f x) (f y)<1) (hins : ∀ x∈Q, dist (f c) (f x)<1) :
      ∃ B ⊆ A, A.card/2 ≤ B.card ∧ ∀ x∈B, ∀ y∈B, dist (f x) (f y)<1 := by
    refine ⟨insert c Q,Finset.insert_subset hc hs,by simpa [hnot] using hle,?_⟩
    intro x hx y hy
    by_cases hxc : x=c
    · subst x
      by_cases hyc : y=c
      · subst y; simp
      · exact hins _ ((Finset.mem_insert.mp hy).resolve_left hyc)
    · have hxQ := (Finset.mem_insert.mp hx).resolve_left hxc
      by_cases hyc : y=c
      · subst y; rw [dist_comm]; exact hins _ hxQ
      · exact hQ _ hxQ _ ((Finset.mem_insert.mp hy).resolve_left hyc)
  by_cases h : ∀ x∈U, dist (f a) (f x)<1
  · exact extend U subU a ha (fun hh => (hmem (Finset.mem_filter.mp hh).1).2.1 rfl) (by omega) hU h
  · push Not at h
    obtain ⟨x,hx,hax⟩ := h
    apply extend V subV b hb (fun hh => (hmem (Finset.mem_filter.mp hh).1).2.2 rfl) (by omega) hV
    intro y hy
    apply lt_of_le_of_ne (hbound b hb y (subV hy))
    intro he
    obtain ⟨hxP,hxpos⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyP,hyneg⟩ := Finset.mem_filter.mp hy
    have hax' := le_antisymm (hbound a ha x (subU hx)) hax
    rw [hfa,dist_zero_left] at hax'
    rw [dist_comm,hfb,dist_eq_norm] at he
    have hxy := opposite_diameters _ _ (hlens x hxP).2.2.2 (hlens y hyP).2.2.1
      (mul_nonpos_of_nonneg_of_nonpos hxpos (le_of_not_ge hyneg)) hax' he
    exact (not_lt_of_ge (hbound _ (subU hx) _ (subV hy))) hxy


lemma avoid_diameter (A : Finset ℝ²) (d : ℝ) (hd : d ∈ distanceSet A)
    (hmax : ∀ l ∈ distanceSet A, l≤d) : ∃ B ⊆ A, A.card/2 ≤ B.card ∧ ∀ x∈B, ∀ y∈B, dist x y<d := by
  classical
  obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hd
  obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp hab
  change dist a b=d at he
  have hdpos : 0<d := (dist_pos.mpr hab).trans_eq he
  let E := Complex.orthonormalBasisOneI.repr.symm
  let v := E (b-a)
  have hvnorm : ‖v‖=d := by dsimp [v]; rw [E.norm_map,←dist_eq_norm,dist_comm,he]
  have hv : v≠0 := by intro h; rw [h,norm_zero] at hvnorm; linarith
  let f (x : ℝ²) := E (x-a)/v
  have hdist (x y : ℝ²) : dist (f x) (f y)= dist x y/d := by
    rw [dist_eq_norm]
    dsimp only [f]
    rw [←sub_div,norm_div,←map_sub,E.norm_map,hvnorm,show (x-a)-(y-a)=x-y by abel,dist_eq_norm]
  have hf : Function.Injective f := by
    intro x y h
    have hh := hdist x y
    rw [h,dist_self] at hh
    exact dist_eq_zero.mp ((div_eq_zero_iff.mp hh.symm).resolve_right hdpos.ne')
  obtain ⟨B,hBA,hcard,hB⟩ := avoid_normalized_diameter A a b ha hb f hf (by simp [f])
    (by change v/v=1; exact div_self hv) (by
      intro x hx y hy
      rw [hdist,div_le_one hdpos]
      by_cases hxy : x=y
      · simp [hxy,hdpos.le]
      · exact hmax _ (dist_mem hx hy hxy))
  exact ⟨B,hBA,hcard,fun x hx y hy => (div_lt_one hdpos).mp (by rw [←hdist]; exact hB x hx y hy)⟩


end Erdos1082Diameter



lemma bisector_limit (A : Finset ℝ²) (hA : NonTrilinear (A:Set ℝ²)) (x y : ℝ²) (hne : x≠y) :
    (A.filter fun c => dist c x=dist c y).card≤2 := by
  classical
  by_contra! hh
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩ := Finset.two_lt_card_iff.mp hh
  obtain ⟨hp,hp'⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq,hq'⟩ := Finset.mem_filter.mp hq
  obtain ⟨hr,hr'⟩ := Finset.mem_filter.mp hr
  apply hA hp hq hr hpq hqr hpr
  apply collinear_iff_finrank_le_one.mpr
  have hsub : ({p,q,r}:Set ℝ²) ⊆ perpBisector x y := by
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl|rfl
    · exact mem_perpBisector_iff_dist_eq.mpr hp'
    · exact mem_perpBisector_iff_dist_eq.mpr hq'
    · exact mem_perpBisector_iff_dist_eq.mpr hr'
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))=1+1) := ⟨finrank_euclideanSpace_fin⟩
  have hd := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  rw [←AffineSubspace.direction_eq_vectorSpan,direction_perpBisector,
    Submodule.finrank_orthogonal_span_singleton (𝕜:=ℝ) (E:=EuclideanSpace ℝ (Fin 2)) (n:=1) (vsub_ne_zero.mpr hne.symm)] at hd
  exact hd

lemma apex_count (A : Finset ℝ²) (hcard : A.card=2*distinctDistances A+2) (p : ℝ²) (hp : p∈A) :
    A.card+2 ≤ (A.offDiag.filter fun b => dist p b.1=dist p b.2).card := by
  classical
  let B := A.erase p
  let F (r : ℝ) := B.filter fun x => dist p x=r
  let P := A.offDiag.filter fun b => dist p b.1=dist p b.2
  have hBx (x : ℝ²) (hx : x∈B) : dist p x∈distanceSet A := by
    obtain ⟨hne,hx⟩ := Finset.mem_erase.mp hx
    exact dist_mem hp hx hne.symm
  have hmap (b : ℝ²×ℝ²) (hb : b∈P) : b.1∈B ∧ b.2∈B := by
    obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
    obtain ⟨hx,hy,hn⟩ := Finset.mem_offDiag.mp hb
    have hx' : b.1≠p := by intro h; rw [h,dist_self] at he; exact hn (h.trans (dist_eq_zero.mp he.symm))
    have hy' : b.2≠p := by intro h; rw [h,dist_self] at he; exact hn ((dist_eq_zero.mp he).symm.trans h.symm)
    exact ⟨Finset.mem_erase.mpr ⟨hx',hx⟩,Finset.mem_erase.mpr ⟨hy',hy⟩⟩
  have hsum : B.card=∑ r∈distanceSet A, (F r).card := Finset.card_eq_sum_card_fiberwise hBx
  have hpair : P.card=∑ r∈distanceSet A, (F r).offDiag.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=fun b : ℝ²×ℝ² => dist p b.1)
      (t:=distanceSet A) (fun b hb => hBx _ (hmap b hb).1)]
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    ext b
    constructor
    · intro h
      obtain ⟨hb,hr⟩ := Finset.mem_filter.mp h
      obtain ⟨hx,hy⟩ := hmap b hb
      obtain ⟨ho,he⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_filter.mpr ⟨hx,hr⟩,
        Finset.mem_filter.mpr ⟨hy,he.symm.trans hr⟩,(Finset.mem_offDiag.mp ho).2.2⟩
    · intro h
      obtain ⟨hx,hy,hn⟩ := Finset.mem_offDiag.mp h
      obtain ⟨hx,hr⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy,ht⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_of_mem_erase hx,Finset.mem_of_mem_erase hy,hn⟩,hr.trans ht.symm⟩,hr⟩
  have term (r : ℝ) : 4*(F r).card≤(F r).offDiag.card+6 := by
    rw [Finset.offDiag_card]
    generalize (F r).card=k
    match k with
    | 0 | 1 | 2 => decide
    | k+3 =>
      have he : (k+3)*(k+3)=(k+3)+(k*k+5*k+6) := by ring
      rw [he,Nat.add_sub_cancel_left]; nlinarith
  have hsum' := Finset.sum_le_sum (s:=distanceSet A) (fun r _ => term r)
  rw [←Finset.mul_sum,←hsum,Finset.sum_add_distrib,←hpair,Finset.sum_const,nsmul_eq_mul] at hsum'
  have hb : B.card+1=A.card := Finset.card_erase_add_one hp
  change 4*B.card≤P.card+distinctDistances A*6 at hsum'
  change A.card+2≤P.card
  omega

lemma critical_bisectors (A : Finset ℝ²) (hA : NonTrilinear (A:Set ℝ²)) (hcard : A.card=2*distinctDistances A+2) :
    let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
    3*A.card+(A.offDiag.filter fun b => k b=0).card≤(A.offDiag.filter fun b => k b=2).card := by
  classical
  dsimp only
  let R (p : ℝ²) (b : ℝ²×ℝ²) := dist p b.1=dist p b.2
  let k (b : ℝ²×ℝ²) := (A.filter fun p => R p b).card
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s:=A) (t:=A.offDiag) R
  change (∑ p∈A,(A.offDiag.filter (R p)).card)=∑ b∈A.offDiag,k b at hdouble
  have hs := Finset.sum_le_sum (s:=A) (fun p hp => apex_count A hcard p hp)
  change (∑ _∈A,(A.card+2))≤∑ p∈A,(A.offDiag.filter (R p)).card at hs
  rw [Finset.sum_const,nsmul_eq_mul,hdouble] at hs
  have hk (b : ℝ²×ℝ²) (hb : b∈A.offDiag) : k b ≤ 2 :=
    bisector_limit A hA _ _ (Finset.mem_offDiag.mp hb).2.2
  have hsum := Finset.sum_congr (s₁:=A.offDiag) rfl (fun b hb => show
    k b+(if k b=0 then 1 else 0) = 1 + (if k b=2 then 1 else 0) by
      have := hk b hb
      split_ifs <;> omega)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hsum
  simp only [Finset.sum_boole] at hsum
  rw [Finset.offDiag_card] at hsum
  change 3*A.card+(A.offDiag.filter fun b => k b=0).card≤(A.offDiag.filter fun b => k b=2).card
  have hn : 1≤A.card := by omega
  have hmul := Nat.mul_le_mul_left A.card hn
  simp only [Nat.mul_one] at hmul
  nlinarith [Nat.sub_add_cancel hmul]


lemma radial_in_plane (hr : H3) (A : Finset ℝ²) : ∀ (T : Finset Circle) (G : Subgroup Circle) (m : ℕ) (P : Finset ℂ) (f : ℂ→ℝ²) (s : ℝ),
      (G:Set Circle)=T → 2 ≤ m → m.Coprime T.card → 0<s →
      (∀ x y, dist (f x) (f y)=s*dist x y) → (∀ z∈T, f (z:ℂ)∈A) → (∀ p∈P, f p∈A) →
      (∀ p∈P, p≠0 ∧ ‖p‖≠1) → Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ) →
      P.card*T.card+(2*min m 9)*P.card ≤ 2*distinctDistances A+(2*min m 9)*P.card*P.card := by
  classical
  intro T G m P f s hT hm hcop hs hf hTA hPA hgood hinj
  let Q := T.image (fun z : Circle => (z:ℂ)) ∪ P
  have hq := hr T G hT m hm hcop Q P (Finset.subset_union_right ..)
    (fun z hz => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz)) hgood hinj
  have hmap (q : ℂ) (hq : q∈Q) : f q∈A := by
    rcases Finset.mem_union.mp hq with he|hp
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp he
      exact hTA z hz
    · exact hPA q hp
  have hsub : (distanceSet Q).image (fun x => s*x) ⊆ distanceSet A := by
    intro d hd
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hxy
    have hpos : 0<dist (f x) (f y) := by rw [hf]; exact mul_pos hs (dist_pos.mpr hne)
    exact Finset.mem_image.mpr ⟨(f x,f y),Finset.mem_offDiag.mpr
      ⟨hmap x hx,hmap y hy,dist_pos.mp hpos⟩,hf x y⟩
  have hb := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun _ _ he => mul_left_cancel₀ hs.ne' he)] at hb
  change distinctDistances Q≤distinctDistances A at hb
  omega

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1082_erdos_1082_parts_i_R1.H2 := by
  classical
  intro hmat hpent hrad hsmall A hA hcard hheavy hsparse
  by_cases h₀ : distinctDistances A≤4
  · exact False.elim (hsmall A hA hcard h₀)
  have witness := hheavy
  obtain ⟨d,hd,_⟩ := witness
  let M := (distanceSet A).max' ⟨d,hd⟩
  have hm : M∈distanceSet A := Finset.max'_mem ..
  have hmax (r : ℝ) (hr : r∈distanceSet A) : r≤M := Finset.le_max' _ r hr
  obtain ⟨⟨x,y⟩,hxy,he⟩ := Finset.mem_image.mp hm
  have hpos : 0<M := (dist_pos.mpr (Finset.mem_offDiag.mp hxy).2.2).trans_eq he
  have hbound (x y : A) : dist x.1 y.1≤M := by
    by_cases h : x.1=y.1
    · simpa [h] using hpos.le
    · exact hmax _ (dist_mem x.2 y.2 h)
  have hbis := critical_bisectors A hA hcard
  have hrad' := radial_in_plane hrad A
  have havoid := Erdos1082Diameter.avoid_diameter A M hm hmax
  by_cases mat : ∃ a b c d e f : A, [a,b,c,d,e,f].Nodup ∧ dist a.1 b.1=M ∧ dist c.1 d.1=M ∧ dist e.1 f.1=M
  · exact hmat A hA hcard (by omega) hsparse hbis hrad' M hm hmax havoid hheavy mat
  by_cases pent : ∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M
  · have hcount := Erdos1082Diameter.pentagon_multiplicity A M hpos hbound mat pent
    exact hpent A hA hcard (by omega) hsparse hbis hrad' M hm hmax havoid
      (Erdos1082Diameter.pentagon_heavy A hcard M hm hcount) hcount pent
  obtain ⟨x,hx,y,hy,hd⟩ := Erdos1082Diameter.diameter_small_cover A M hm hmax mat pent
  exact ⟨x,hx,y,hy,M,hm,hd⟩

end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1
