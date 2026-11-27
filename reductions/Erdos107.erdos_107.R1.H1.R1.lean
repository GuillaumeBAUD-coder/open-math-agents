import OMAReductions.R_Erdos107_erdos_107_R1

/-!
Reduce the sharp Erdős–Szekeres upper bound to two fixed finite sign problems
(five vertices selected from nine and six from seventeen), and the general
case from seven vertices onward. In the latter two steps the signs must come
from integer-coordinate points with strictly increasing horizontal coordinates
and nonzero orientation determinants. Simultaneous rational approximation
preserves the strict signs and clearing denominators gives the integer model.
Every subset of the preceding conjectured threshold size already contains
a polygon with one fewer vertex.

On an ordered quadruple, the four triple orientations change sign at most
once. When each end pair of signs agrees, supporting lines expose all four
vertices. Planar Carathéodory then gives convex independence of a set from
its four-point subsets. For five points the quadruple signs give a short
parity proof: each nonconvex quadruple has odd parity and every triple
occurs twice across all five quadruples.

The orientation approach follows Szekeres and Peters, ANZIAM Journal 48
(2006), 151–164. The separating-coordinate and noncollinearity calculations
are adapted from Genbox's accepted open-math-agents PR 1086.
-/

-- Credit: @zarnab222-dev

section

open Finset EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace E107Order

private theorem planar_coordinates (X : Finset (ℝ^2)) :
    ∃ x y : (ℝ^2) →ₗ[ℝ] ℝ, Set.InjOn x (X : Set (ℝ^2)) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  classical
  let bad := (X ×ˢ X).image fun uv : (ℝ^2) × (ℝ^2) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : ℝ^2) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

private theorem orient_ne_in_image (X : Finset ℝ²)
    (hX : EuclideanGeometry.NonTrilinear (X : Set ℝ²))
    (x y : ℝ² →ₗ[ℝ] ℝ) (hjoint : ∀ p q, x p = x q → y p = y q → p = q) :
    ∀ a ∈ X.image (x.prod y), ∀ b ∈ X.image (x.prod y), ∀ c ∈ X.image (x.prod y),
      a.1 < b.1 → b.1 < c.1 → (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0 := by
  intro u hu v hv w hw hab hbc he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hw
  change x a < x b at hab
  change x b < x c at hbc
  change (x b - x a) * (y c - y b) - (y b - y a) * (x c - x b) = 0 at he
  have hnab : a ≠ b := fun h => hab.ne (congrArg x h)
  have hnbc : b ≠ c := fun h => hbc.ne (congrArg x h)
  have hnac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg x h)
  apply hX ha hb hc hnab hnbc hnac
  let r := (x b - x a) / (x c - x b)
  have hden := sub_ne_zero.mpr hbc.ne'
  have hxb : x b - x a = r * (x c - x b) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hden]
  have hyb : y b - y a = r * (y c - y b) := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    linarith only [he]
  have hdiff : b - a = r • (c - b) := by
    apply hjoint
    · simpa only [map_sub, map_smul, smul_eq_mul] using hxb
    · simpa only [map_sub, map_smul, smul_eq_mul] using hyb
  apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set ℝ²) by simp)).mpr
  refine ⟨c - b, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨-r, ?_⟩
    change _ = (-r) • (c - b) + b
    rw [neg_smul, ← hdiff]
    abel
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

private theorem enumerate {N : ℕ} (P : Finset ℝ²) (size : P.card = N)
    (gp : NonTrilinear (P : Set ℝ²)) :
    ∃ (x y : ℝ² →ₗ[ℝ] ℝ) (p : Fin N ↪ ℝ²), (∀ i, p i ∈ P) ∧
      StrictMono (fun i => x (p i)) ∧
      ∀ i j k, i < j → j < k →
        (x (p j)-x (p i))*(y (p k)-y (p i)) -
        (y (p j)-y (p i))*(x (p k)-x (p i)) ≠ 0 := by
  classical
  obtain ⟨x,y,hx,hxy⟩ := planar_coordinates P
  let keys := P.image x
  have num : keys.card = N := (card_image_of_injOn hx).trans size
  let key := keys.orderIsoOfFin num
  have pre (i : Fin N) : ∃ v ∈ P, x v = (key i).val := mem_image.mp (key i).property
  choose pt member rep using pre
  have mono : StrictMono (fun i => x (pt i)) := by
    intro i j lt
    dsimp only
    rw [rep,rep]
    exact key.strictMono lt
  let p : Fin N ↪ ℝ² := ⟨pt, fun i j eq => mono.injective (congrArg x eq)⟩
  refine ⟨x,y,p,member,mono,?_⟩
  intro i j k hij hjk
  have nonzero := orient_ne_in_image P gp x y hxy
    _ (mem_image_of_mem (x.prod y) (member i)) _ (mem_image_of_mem (x.prod y) (member j))
    _ (mem_image_of_mem (x.prod y) (member k)) (mono hij) (mono hjk)
  change (x (p j)-x (p i))*(y (p k)-y (p j)) -
    (y (p j)-y (p i))*(x (p k)-x (p j)) ≠ 0 at nonzero
  intro h
  apply nonzero
  linarith only [h]

end E107Order

end

section

open EuclideanGeometry
open scoped EuclideanGeometry

namespace E107Signs

private theorem between_sign {u v w a b c : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (eq : c*v=a*u+b*w) (same : 0<u ↔ 0<w) : 0<u ↔ 0<v := by
  by_cases h : 0<u
  · have hw := same.mp h
    have hv : 0<v := by
      by_contra! hv
      linarith [mul_nonpos_of_nonneg_of_nonpos hc.le hv, mul_pos ha h, mul_pos hb hw]
    simp [h,hv]
  · have hw : w ≤ 0 := le_of_not_gt fun hw => h (same.mpr hw)
    have hv : ¬0<v := by
      intro hv
      linarith [mul_pos hc hv, mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h),
        mul_nonpos_of_nonneg_of_nonpos hb.le hw]
    simp [h,hv]

/-- In each of the four three-element subsequences of the orientation signs, matching
outside signs force the same middle sign. -/
theorem signotope {P : Type*} (x y : P → ℝ) (D : P → P → P → ℝ) (deq : ∀ a b c, D a b c = (x b-x a)*(y c-y a) - (y b-y a)*(x c-x a)) (a b c d : P)
    (hab : x a < x b) (hbc : x b < x c) (hcd : x c < x d) :
    let A := 0 < D a b c
    let B := 0 < D a b d
    let C := 0 < D a c d
    let E := 0 < D b c d
    ((A ↔ C) → (A ↔ B)) ∧ ((A ↔ E) → (A ↔ B)) ∧
      ((A ↔ E) → (A ↔ C)) ∧ ((B ↔ E) → (B ↔ C)) := by
  dsimp only
  refine ⟨between_sign (a:=x d-x a) (b:=x b-x a) (c:=x c-x a) (by linarith) (by linarith) (by linarith) ?_,
    between_sign (a:=x d-x b) (b:=x b-x a) (c:=x c-x b) (by linarith) (by linarith) (by linarith) ?_,
    between_sign (a:=x d-x c) (b:=x c-x a) (c:=x c-x b) (by linarith) (by linarith) (by linarith) ?_,
    between_sign (a:=x d-x c) (b:=x d-x a) (c:=x d-x b) (by linarith) (by linarith) (by linarith) ?_⟩
  all_goals simp only [deq]; ring

private theorem boundary_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E →ₗ[ℝ] ℝ) (S : Set E) (u v : E) (hne : u ≠ v) (tie : F u = F v)
    (above : ∀ t ∈ S, t ≠ u → t ≠ v → F u < F t) :
    u ∉ convexHull ℝ (S \ {u}) := by
  let T := {t : E | F u < F t ∨ t = v}
  have cv : Convex ℝ T := by
    intro p hp q hq α β hα hβ hsum
    change F u < F p ∨ p = v at hp
    change F u < F q ∨ q = v at hq
    change F u < F (α • p + β • q) ∨ α • p + β • q = v
    rcases eq_or_lt_of_le hα with he | hα'
    · have ht : β=1 := by linarith
      simpa [← he, ht] using hq
    rcases eq_or_lt_of_le hβ with he | hβ'
    · have ht : α=1 := by linarith
      simpa [← he, ht] using hp
    have iden : α*F u + β*F u = F u := by rw [← add_mul,hsum,one_mul]
    simp only [map_add,map_smul,smul_eq_mul]
    rcases hp with hp | rfl <;> rcases hq with hq | rfl
    · exact Or.inl (by linarith [mul_lt_mul_of_pos_left hp hα', mul_lt_mul_of_pos_left hq hβ'])
    · exact Or.inl (by rw [← tie]; linarith [mul_lt_mul_of_pos_left hp hα'])
    · exact Or.inl (by rw [← tie]; linarith [mul_lt_mul_of_pos_left hq hβ'])
    · exact Or.inr (by rw [← add_smul,hsum,one_smul])
  have sub : S \ {u} ⊆ T := by
    intro t ht
    by_cases h : t=v
    · exact Or.inr h
    · exact Or.inl (above t ht.1 ht.2 h)
  intro h
  exact (convexHull_min sub cv h).elim (lt_irrefl _) hne

private theorem edge_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y : E →ₗ[ℝ] ℝ) (D : E → E → E → ℝ) (deq : ∀ a b c, D a b c = (x b-x a)*(y c-y a) - (y b-y a)*(x c-x a)) (S : Set E) (u v p q : E)
    (cover : ∀ t ∈ S, t=u ∨ t=v ∨ t=p ∨ t=q) (hne : u≠v)
    (hp : D u v p ≠ 0) (hq : D u v q ≠ 0)
    (same : 0<D u v p ↔ 0<D u v q) :
    u ∉ convexHull ℝ (S \ {u}) ∧ v ∉ convexHull ℝ (S \ {v}) := by
  let L : E →ₗ[ℝ] ℝ := (x v-x u) • y - (y v-y u) • x
  have val (t : E) : L t - L u = D u v t := by simp [L,deq]; ring
  have tie : L u = L v := by have h := val v; simp [deq] at h; linarith
  have oneSide : ∃ F : E →ₗ[ℝ] ℝ, F u = F v ∧ F u < F p ∧ F u < F q := by
    by_cases pos : 0 < D u v p
    · exact ⟨L,tie,by linarith [val p],by linarith [val q, same.mp pos]⟩
    · have hn := lt_of_le_of_ne (le_of_not_gt pos) hp
      have hn' := lt_of_le_of_ne (le_of_not_gt (fun h => pos (same.mpr h))) hq
      refine ⟨-L,by simp [tie], ?_, ?_⟩
      · simp only [LinearMap.neg_apply, neg_lt_neg_iff]
        linarith [val p]
      · simp only [LinearMap.neg_apply, neg_lt_neg_iff]
        linarith [val q]
  obtain ⟨F,he,hp',hq'⟩ := oneSide
  have side (t : E) (ht : t ∈ S) (nu : t≠u) (nv : t≠v) : F u < F t := by
    rcases cover t ht with h | h | h | h
    · exact (nu h).elim
    · exact (nv h).elim
    · simpa only [h] using hp'
    · simpa only [h] using hq'
  exact ⟨boundary_extreme F S u v hne he side, boundary_extreme F S v u hne.symm he.symm
    (fun t ht nv nu => he ▸ side t ht nu nv)⟩

/-- Two supporting lines through the first and last pairs expose all four vertices. -/
theorem convex_of_signs (x y : ℝ² →ₗ[ℝ] ℝ) (D : ℝ² → ℝ² → ℝ² → ℝ) (deq : ∀ a b c, D a b c = (x b-x a)*(y c-y a) - (y b-y a)*(x c-x a)) (a b c d : ℝ²) (hab : a≠b) (hcd : c≠d)
    (hA : D a b c ≠ 0) (hB : D a b d ≠ 0)
    (hC : D a c d ≠ 0) (hE : D b c d ≠ 0)
    (left : 0<D a b c ↔ 0<D a b d)
    (right : 0<D a c d ↔ 0<D b c d) :
    ConvexIndep ({a,b,c,d} : Set ℝ²) := by
  let S : Set ℝ² := {a,b,c,d}
  have cover (t : ℝ²) (ht : t∈S) : t=a ∨ t=b ∨ t=c ∨ t=d := by simpa [S] using ht
  have ab := edge_extreme x y D deq S a b c d cover hab hA hB left
  have cyc (t : ℝ²) : D c d t = D t c d := by simp only [deq]; ring
  have cd := edge_extreme x y D deq S c d a b (fun t ht => by rcases cover t ht with h|h|h|h <;> tauto)
    hcd (by rwa [cyc]) (by rwa [cyc]) (by simpa only [cyc] using right)
  intro t ht
  rcases cover t ht with rfl|rfl|rfl|rfl
  exacts [ab.1,ab.2,cd.1,cd.2]

end E107Signs

end

section

open EuclideanGeometry Finset
namespace E107Helly

theorem convexIndep_of_four_large (S : Finset ℝ²) (large : 4 ≤ S.card)
    (four : ∀ Q ⊆ S, Q.card = 4 → ConvexIndep (Q : Set ℝ²)) :
    ConvexIndep (S : Set ℝ²) := by
  classical
  intro p hp hull
  rw [convexHull_eq_union] at hull
  simp only [Set.mem_iUnion,exists_prop] at hull
  obtain ⟨T,sub,indep,contains⟩ := hull
  have bound : T.card ≤ 3 := by
    have h := indep.card_le_finrank_succ
    have d := (vectorSpan ℝ (Set.range ((↑) : T → ℝ²))).finrank_le
    rw [finrank_euclideanSpace_fin] at d
    simp only [Fintype.card_coe] at h
    omega
  have inside : insert p T ⊆ S := insert_subset hp (fun x hx => (sub hx).1)
  obtain ⟨Q,hQ,hQS,size⟩ := exists_subsuperset_card_eq inside
    ((card_insert_le p T).trans (by omega : T.card + 1 ≤ 4)) large
  apply four Q hQS size p (hQ (mem_insert_self ..))
  apply convexHull_mono _ contains
  intro y hy
  exact ⟨hQ (mem_insert_of_mem hy),(sub hy).2⟩

theorem convexIndep_of_four (S : Finset ℝ²) (gp : NonTrilinear (S : Set ℝ²))
    (four : ∀ Q ⊆ S, Q.card = 4 → ConvexIndep (Q : Set ℝ²)) :
    ConvexIndep (S : Set ℝ²) := by
  classical
  by_cases large : 4 ≤ S.card
  · exact convexIndep_of_four_large S large four
  intro p hp hull
  let T := S.erase p
  have few : T.card ≤ 2 := by dsimp [T]; rw [card_erase_of_mem hp]; omega
  have inHull : p ∈ convexHull ℝ (T : Set ℝ²) := by simpa only [T,coe_erase] using hull
  have outside : p ∉ T := notMem_erase _ _
  by_cases empty : T.card = 0
  · rw [card_eq_zero.mp empty] at inHull
    simpa only [coe_empty,convexHull_empty,Set.mem_empty_iff_false] using inHull
  by_cases one : T.card = 1
  · obtain ⟨b,eq⟩ := card_eq_one.mp one
    rw [eq,coe_singleton,convexHull_singleton,Set.mem_singleton_iff] at inHull
    exact outside (by simp [eq,inHull])
  obtain ⟨b,c,bc,eq⟩ := card_eq_two.mp (show T.card = 2 by omega)
  have hb : b ∈ T := by simp [eq]
  have hc : c ∈ T := by simp [eq]
  have pb : p ≠ b := fun e => outside (e ▸ hb)
  have pc : p ≠ c := fun e => outside (e ▸ hc)
  have general := gp hp (mem_of_mem_erase hb) (mem_of_mem_erase hc) pb bc pc
  apply general
  have span : p ∈ affineSpan ℝ ({b,c} : Set ℝ²) := by
    apply convexHull_subset_affineSpan
    simpa only [eq,coe_insert,coe_singleton] using inHull
  exact (collinear_insert_iff_of_mem_affineSpan span).mpr (collinear_pair ℝ b c)

theorem polygon_of_four {P : Set ℝ²} {n : ℕ} (S : Finset ℝ²) (size : S.card = n)
    (sub : (S : Set ℝ²) ⊆ P) (gp : NonTrilinear P)
    (four : ∀ Q ⊆ S, Q.card = 4 → ConvexIndep (Q : Set ℝ²)) : HasConvexNGon n P :=
  ⟨S,size,sub,convexIndep_of_four S (Set.Triplewise.mono sub gp) four⟩

end E107Helly

end

section

open EuclideanGeometry Finset
namespace E107Image

theorem polygon_of_ordered_four {N n : ℕ} {P : Set ℝ²} (p : Fin N ↪ ℝ²)
    (T : Finset (Fin N)) (size : T.card = n) (inside : ∀ i ∈ T, p i ∈ P)
    (gp : NonTrilinear P)
    (four : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a < b → b < c → c < d →
      ConvexIndep ({p a,p b,p c,p d} : Set ℝ²)) : HasConvexNGon n P := by
  classical
  apply E107Helly.polygon_of_four (T.map p) (by simpa only [card_map] using size) _ gp
  · intro Q sub hQ
    let R := T.filter (fun i => p i ∈ Q)
    have imageR : R.map p = Q := by
      ext x
      constructor
      · intro hx
        obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
        exact (mem_filter.mp hi).2
      · intro hx
        obtain ⟨i,hi,rfl⟩ := mem_map.mp (sub hx)
        exact mem_map.mpr ⟨i,mem_filter.mpr ⟨hi,hx⟩,rfl⟩
    have sizeR : R.card = 4 := (card_map (s := R) p).symm.trans ((congrArg card imageR).trans hQ)
    let e := R.orderEmbOfFin sizeR
    have member (i : Fin 4) : e i ∈ T := (mem_filter.mp (R.orderEmbOfFin_mem sizeR i)).1
    have corners := four _ (member 0) _ (member 1) _ (member 2) _ (member 3)
      (e.strictMono (by decide : (0 : Fin 4)<1)) (e.strictMono (by decide : (1 : Fin 4)<2))
      (e.strictMono (by decide : (2 : Fin 4)<3))
    have listR : R = {e 0,e 1,e 2,e 3} := by
      calc
        R = univ.map e.toEmbedding := (R.map_orderEmbOfFin_univ sizeR).symm
        _ = _ := by
          rw [show (univ : Finset (Fin 4)) = {0,1,2,3} by decide]
          simp
    have points : (Q : Set ℝ²) = {p (e 0),p (e 1),p (e 2),p (e 3)} := by
      calc
        (Q : Set ℝ²) = (R.map p : Set ℝ²) := congrArg (fun U : Finset ℝ² => (U : Set ℝ²)) imageR.symm
        _ = (({e 0,e 1,e 2,e 3} : Finset (Fin N)).map p : Set ℝ²) :=
          congrArg (fun U : Finset (Fin N) => (U.map p : Set ℝ²)) listR
        _ = _ := by simp
    exact points.symm ▸ corners
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
    exact inside i hi

end E107Image

end

section

open Finset

namespace E107Parity

private theorem choose_four {N : ℕ} (col : Fin N → Fin N → Fin N → Bool)
    {a b c d : Fin N} (ab : a<b) (bc : b<c) (cd : c<d)
    (left : col a b c = col a b d) (right : col a c d = col b c d) :
    ∃ T : Finset (Fin N), T.card=4 ∧
      ∀ i∈T, ∀ j∈T, ∀ k∈T, ∀ l∈T, i<j → j<k → k<l →
        col i j k=col i j l ∧ col i k l=col j k l := by
  refine ⟨{a,b,c,d}, ?_, ?_⟩
  · simp [ab.ne,bc.ne,cd.ne,(ab.trans bc).ne,(bc.trans cd).ne,((ab.trans bc).trans cd).ne]
  · intro i hi j hj k hk l hl ij jk kl
    simp only [mem_insert,mem_singleton] at hi hj hk hl
    have h : i=a ∧ j=b ∧ k=c ∧ l=d := by omega
    obtain ⟨rfl,rfl,rfl,rfl⟩ := h
    exact ⟨left,right⟩

private theorem odd_of_bad : ∀ A B C D : Bool,
    ((A=B ∧ B=C) ∨ (A=B ∧ C=D) ∨ (B=C ∧ C=D)) →
    ¬ (A=B ∧ C=D) → ((A.xor B).xor (C.xor D)) = true := by decide

private theorem parity : ∀ a b c d e f g h i j : Bool,
    ((a.xor b).xor (d.xor g)) = true →
    ((a.xor c).xor (e.xor h)) = true →
    ((b.xor c).xor (f.xor i)) = true →
    ((d.xor e).xor (f.xor j)) = true →
    ((g.xor h).xor (i.xor j)) = true → False := by decide +kernel

private theorem five (col : Fin 5 → Fin 5 → Fin 5 → Bool)
    (good : ∀ a b c d, a<b → b<c → c<d →
      ((col a b c=col a b d ∧ col a b d=col a c d) ∨
        (col a b c=col a b d ∧ col a c d=col b c d) ∨
        (col a b d=col a c d ∧ col a c d=col b c d))) :
    ∃ T : Finset (Fin 5), T.card=4 ∧
      ∀ i∈T, ∀ j∈T, ∀ k∈T, ∀ l∈T, i<j → j<k → k<l →
        col i j k=col i j l ∧ col i k l=col j k l := by
  by_contra fail
  have odd (a b c d : Fin 5) (ab : a<b) (bc : b<c) (cd : c<d) :
      (((col a b c).xor (col a b d)).xor ((col a c d).xor (col b c d))) = true := by
    apply odd_of_bad _ _ _ _ (good a b c d ab bc cd)
    exact fun h => fail (choose_four col ab bc cd h.1 h.2)
  exact parity _ _ _ _ _ _ _ _ _ _
    (odd 0 1 2 3 (by decide) (by decide) (by decide))
    (odd 0 1 2 4 (by decide) (by decide) (by decide))
    (odd 0 1 3 4 (by decide) (by decide) (by decide))
    (odd 0 2 3 4 (by decide) (by decide) (by decide))
    (odd 1 2 3 4 (by decide) (by decide) (by decide))

end E107Parity

end

section

open Filter Topology

namespace E107Rational

theorem rational_sign_realization {N : ℕ} (x y : Fin N → ℝ) (mono : StrictMono x)
    (nonzero : ∀ i j k : Fin N, i < j → j < k →
      (x j - x i) * (y k - y i) - (y j - y i) * (x k - x i) ≠ 0) :
    ∃ u v : Fin N → ℚ, StrictMono u ∧ ∀ i j k : Fin N, i < j → j < k →
      let detQ := (u j - u i) * (v k - v i) - (v j - v i) * (u k - u i)
      detQ ≠ 0 ∧ (0 < detQ ↔
        0 < (x j - x i) * (y k - y i) - (y j - y i) * (x k - x i)) := by
  choose u _ _ hu using fun i => Real.exists_seq_rat_strictMono_tendsto (x i)
  choose v _ _ hv using fun i => Real.exists_seq_rat_strictMono_tendsto (y i)
  let d (i j k : Fin N) := (x j - x i) * (y k - y i) - (y j - y i) * (x k - x i)
  let q (t : ℕ) (i j k : Fin N) :=
    (u j t - u i t) * (v k t - v i t) - (v j t - v i t) * (u k t - u i t)
  have limit (i j k : Fin N) : Tendsto (fun t => (q t i j k : ℝ)) atTop (𝓝 (d i j k)) := by
    simpa only [q, d, Rat.cast_sub, Rat.cast_mul] using
      (((hu j).sub (hu i)).mul ((hv k).sub (hv i))).sub
        (((hv j).sub (hv i)).mul ((hu k).sub (hu i)))
  have order : ∀ᶠ t in atTop, ∀ i j : Fin N, i < j → u i t < u j t := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i < j
    · filter_upwards [(hu i).eventually_lt (hu j) (mono hij)] with t ht _
      exact_mod_cast ht
    · exact Eventually.of_forall fun _ h => (hij h).elim
  have signs : ∀ᶠ t in atTop, ∀ i j k : Fin N, i < j → j < k →
      q t i j k ≠ 0 ∧ (0 < q t i j k ↔ 0 < d i j k) := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => ?_
    by_cases hij : i < j
    · by_cases hjk : j < k
      · have hn : d i j k ≠ 0 := nonzero i j k hij hjk
        rcases lt_or_gt_of_ne hn with neg | pos
        · filter_upwards [(limit i j k).eventually_lt tendsto_const_nhds neg] with t ht _ _
          have hq : q t i j k < 0 := by exact_mod_cast ht
          exact ⟨hq.ne, iff_of_false (not_lt_of_gt hq) (not_lt_of_gt neg)⟩
        · filter_upwards [tendsto_const_nhds.eventually_lt (limit i j k) pos] with t ht _ _
          have hq : 0 < q t i j k := by exact_mod_cast ht
          exact ⟨hq.ne', iff_of_true hq pos⟩
      · exact Eventually.of_forall fun _ _ h => (hjk h).elim
    · exact Eventually.of_forall fun _ h => (hij h).elim
  obtain ⟨t, ht, hs⟩ := (order.and signs).exists
  exact ⟨fun i => u i t, fun i => v i t, fun _ _ h => ht _ _ h, hs⟩

end E107Rational

end

section

open Finset

namespace E107Integral

/-- A single positive scaling puts both coordinates of every point into the integers. -/
theorem clear_coordinates {N : ℕ} (u v : Fin N → ℚ) :
    ∃ s : ℕ, 0 < s ∧ ∃ x y : Fin N → ℤ,
      (∀ i, (x i:ℚ) = s*u i) ∧ (∀ i, (y i:ℚ) = s*v i) := by
  let d (i : Fin N) := (u i).den * (v i).den
  let s := ∏ i : Fin N, d i
  have hs : 0 < s := Finset.prod_pos (fun i _ => Nat.mul_pos (u i).den_pos (v i).den_pos)
  have prod_dvd (i : Fin N) : d i ∣ s := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have clear_one (q : ℚ) (h : q.den ∣ s) : ∃ z : ℤ, (z:ℚ) = s*q := by
    obtain ⟨k,hk⟩ := h
    refine ⟨(k:ℤ)*q.num, ?_⟩
    have hne : (q.den:ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    have he : (q.num:ℚ) = q * q.den := (div_eq_iff hne).mp q.num_div_den
    rw [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, he]
    ring
  choose x hx using fun i => clear_one (u i) ((dvd_mul_right _ _).trans (prod_dvd i))
  choose y hy using fun i => clear_one (v i) ((dvd_mul_left _ _).trans (prod_dvd i))
  exact ⟨s,hs,x,y,hx,hy⟩

/-- Both vanishing and strict orientation of every triple survive denominator clearing. -/
theorem integral_sign_realization {N : ℕ} (u v : Fin N → ℚ) (hu : StrictMono u) :
    ∃ x y : Fin N → ℤ, StrictMono x ∧ ∀ i j k : Fin N,
      let I := (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)
      let R := (u j-u i)*(v k-v i) - (v j-v i)*(u k-u i)
      (I≠0 ↔ R≠0) ∧ (0<I ↔ 0<R) := by
  obtain ⟨s,hs,x,y,hx,hy⟩ := clear_coordinates u v
  have hp : (0:ℚ) < s := by exact_mod_cast hs
  refine ⟨x,y,?_,?_⟩
  · intro i j hij
    have h : (x i:ℚ) < (x j:ℚ) := by rw [hx,hx]; exact mul_lt_mul_of_pos_left (hu hij) hp
    exact_mod_cast h
  · intro i j k I R
    have eq : (I:ℚ) = (s:ℚ)^2 * R := by
      dsimp only [I,R]
      push_cast
      simp only [hx,hy]
      ring
    have pos : 0 < (s:ℚ)^2 := by positivity
    have nonzero : (I:ℚ) ≠ 0 ↔ R≠0 := by simp [eq, pos.ne']
    have same : (0:ℚ) < I ↔ 0<R := by rw [eq, mul_pos_iff_of_pos_left pos]
    exact ⟨by exact_mod_cast nonzero, by exact_mod_cast same⟩

end E107Integral

end

open Finset EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace OMA.R_Erdos107_erdos_107_R1_H1_R1

/-- The nine-point finite orientation problem for convex pentagons. -/
def H1 : Prop :=
  ∀ col : Fin 9 → Fin 9 → Fin 9 → Bool,
  let polygon (T : Finset (Fin 9)) : Prop := ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a < b → b < c → c < d →
    col a b c = col a b d ∧ col a c d = col b c d
  (∀ a b c d, a < b → b < c → c < d →
    ((col a b c = col a b d ∧ col a b d = col a c d) ∨
     (col a b c = col a b d ∧ col a c d = col b c d) ∨
     (col a b d = col a c d ∧ col a c d = col b c d))) →
  ∃ T, T.card = 5 ∧ polygon T

/-- The seventeen-point finite orientation problem for convex hexagons. Only
realizable signs for which every nine indices contain a pentagon are required. -/
def H2 : Prop :=
  ∀ col : Fin 17 → Fin 17 → Fin 17 → Bool,
  let polygon (T : Finset (Fin 17)) : Prop := ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a < b → b < c → c < d →
    col a b c = col a b d ∧ col a c d = col b c d
  (∀ a b c d, a < b → b < c → c < d →
    ((col a b c = col a b d ∧ col a b d = col a c d) ∨
     (col a b c = col a b d ∧ col a c d = col b c d) ∨
     (col a b d = col a c d ∧ col a c d = col b c d))) →
  (∃ x y : Fin 17 → ℤ, StrictMono x ∧
    ∀ i j k, i < j → j < k →
      let det := (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)
      det ≠ 0 ∧ col i j k = decide (0 < det)) →
  (∀ S : Finset (Fin 17), S.card = 9 →
    ∃ T ⊆ S, T.card = 5 ∧ polygon T) →
  ∃ T, T.card = 6 ∧ polygon T

/-- For n at least seven, every subset of the preceding critical size already
contains an (n-1)-gon. The signs must be realized by an increasing sequence
of integer horizontal coordinates and nonzero determinants. -/
def H3 : Prop := ∀ n : ℕ, 7 ≤ n →
  let N := 2^(n-2)+1
  ∀ col : Fin N → Fin N → Fin N → Bool,
  let polygon (T : Finset (Fin N)) : Prop := ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a < b → b < c → c < d →
    col a b c = col a b d ∧ col a c d = col b c d
  (∀ a b c d, a < b → b < c → c < d →
    ((col a b c = col a b d ∧ col a b d = col a c d) ∨
     (col a b c = col a b d ∧ col a c d = col b c d) ∨
     (col a b d = col a c d ∧ col a c d = col b c d))) →
  (∃ x y : Fin N → ℤ, StrictMono x ∧
    ∀ i j k, i < j → j < k →
      let det := (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)
      det ≠ 0 ∧ col i j k = decide (0 < det)) →
  (∀ S : Finset (Fin N), S.card = 2^(n-3)+1 →
    ∃ T ⊆ S, T.card = n-1 ∧ polygon T) →
  ∃ T, T.card = n ∧ polygon T

section

private theorem word {A B C D : Prop} [Decidable A] [Decidable B] [Decidable C] [Decidable D]
    (g : ((A↔C) → (A↔B)) ∧ ((A↔D) → (A↔B)) ∧ ((A↔D) → (A↔C)) ∧ ((B↔D) → (B↔C))) :
    ((decide A=decide B ∧ decide B=decide C) ∨ (decide A=decide B ∧ decide C=decide D) ∨
      (decide B=decide C ∧ decide C=decide D)) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;> simp_all

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos107_erdos_107_R1.H1 := by
  intro nine seventeen general n lower
  classical
  let polygon {N : ℕ} (col : Fin N → Fin N → Fin N → Bool) (T : Finset (Fin N)) := ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T, a < b → b < c → c < d →
    col a b c = col a b d ∧ col a c d = col b c d
  let legal {N : ℕ} (col : Fin N → Fin N → Fin N → Bool) := ∀ a b c d, a < b → b < c → c < d →
    ((col a b c = col a b d ∧ col a b d = col a c d) ∨
     (col a b c = col a b d ∧ col a c d = col b c d) ∨
     (col a b d = col a c d ∧ col a c d = col b c d))
  let realized {N : ℕ} (col : Fin N → Fin N → Fin N → Bool) :=
    ∃ x y : Fin N → ℤ, StrictMono x ∧ ∀ i j k, i<j → j<k →
      let det := (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)
      det ≠ 0 ∧ col i j k = decide (0 < det)
  have signed (m : ℕ) (hm : 4 ≤ m) :
      let N := 2^(m-2)+1
      ∀ col : Fin N → Fin N → Fin N → Bool, legal col → realized col →
        ∃ T : Finset (Fin N), T.card=m ∧ polygon col T := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro N col ok coordinates
      by_cases four : m=4
      · subst m
        exact E107Parity.five col ok
      by_cases five : m=5
      · subst m
        exact nine col ok
      have near (S : Finset (Fin N)) (size : S.card=2^(m-3)+1) :
          ∃ T ⊆ S, T.card=m-1 ∧ polygon col T := by
        have ksize : S.card=2^((m-1)-2)+1 := by simpa only [show m-1-2=m-3 by omega] using size
        let e := S.orderEmbOfFin ksize
        let restricted a b c := col (e a) (e b) (e c)
        have localOK : legal restricted := fun a b c d ab bc cd =>
          ok _ _ _ _ (e.strictMono ab) (e.strictMono bc) (e.strictMono cd)
        have localReal : realized restricted := by
          obtain ⟨x,y,mon,data⟩ := coordinates
          exact ⟨x ∘ e,y ∘ e,mon.comp e.strictMono,
            fun i j k ij jk => data _ _ _ (e.strictMono ij) (e.strictMono jk)⟩
        obtain ⟨U,usize,fit⟩ := ih (m-1) (by omega) (by omega) restricted localOK localReal
        refine ⟨U.map e.toEmbedding,?_,by simpa only [card_map] using usize,?_⟩
        · intro u hu
          obtain ⟨v,_,rfl⟩ := mem_map.mp hu
          exact S.orderEmbOfFin_mem ksize v
        · intro a ha b hb c hc d hd ab bc cd
          obtain ⟨a₀,ha₀,rfl⟩ := mem_map.mp ha
          obtain ⟨b₀,hb₀,rfl⟩ := mem_map.mp hb
          obtain ⟨c₀,hc₀,rfl⟩ := mem_map.mp hc
          obtain ⟨d₀,hd₀,rfl⟩ := mem_map.mp hd
          exact fit a₀ ha₀ b₀ hb₀ c₀ hc₀ d₀ hd₀ (e.lt_iff_lt.mp ab) (e.lt_iff_lt.mp bc) (e.lt_iff_lt.mp cd)
      by_cases six : m=6
      · subst m
        exact seventeen col ok coordinates near
      exact general m (by omega) col ok coordinates near
  by_cases three : n=3
  · subst n
    simpa only [Erdos107.f_three_eq] using (show 3 ≤ 2^(3-2)+1 by decide)
  apply Nat.sInf_le
  intro P sz gp
  obtain ⟨x,y,p,mem,mon,nonzero⟩ := E107Order.enumerate P sz gp
  let D (a b c : ℝ²) := (x b-x a)*(y c-y a) - (y b-y a)*(x c-x a)
  let col i j k := decide (0 < D (p i) (p j) (p k))
  have ok : legal col := by
    intro a b c d ab bc cd
    exact word (E107Signs.signotope x y D (fun _ _ _ => rfl) (p a) (p b) (p c) (p d)
      (mon ab) (mon bc) (mon cd))
  have integralData : realized col := by
    obtain ⟨u,v,hu,hq⟩ := E107Rational.rational_sign_realization
      (fun i => x (p i)) (fun i => y (p i)) mon nonzero
    obtain ⟨u',v',hu',hz⟩ := E107Integral.integral_sign_realization u v hu
    refine ⟨u',v',hu',?_⟩
    intro i j k ij jk det
    exact ⟨(hz i j k).1.mpr (hq i j k ij jk).1,
      decide_eq_decide.mpr ((hz i j k).2.trans (hq i j k ij jk).2).symm⟩
  obtain ⟨T,hT,fit⟩ := signed n (by omega) col ok integralData
  apply E107Image.polygon_of_ordered_four p T hT (fun i _ => mem i) gp
  intro a ha b hb c hc d hd ab bc cd
  obtain ⟨l,r⟩ := fit a ha b hb c hc d hd ab bc cd
  apply E107Signs.convex_of_signs x y D (fun _ _ _ => rfl) (p a) (p b) (p c) (p d)
    (p.injective.ne ab.ne) (p.injective.ne cd.ne)
    (nonzero _ _ _ ab bc) (nonzero _ _ _ ab (bc.trans cd))
    (nonzero _ _ _ (ab.trans bc) cd) (nonzero _ _ _ bc cd)
    (decide_eq_decide.mp l) (decide_eq_decide.mp r)

end
end OMA.R_Erdos107_erdos_107_R1_H1_R1
