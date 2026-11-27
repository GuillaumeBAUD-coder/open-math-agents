import OMAReductions.R_Erdos19_erdos_19_R1_H2_R1
/-!
In the disjointness graph, orient each edge of a maximum matching toward an
end that meets every unmatched support. Write U for the unmatched supports
and V for the chosen ends. If their combined incidence matrix has too many
rows, it has a dependence. Its coefficients satisfy one equation per support.

On a positive sign domain P, a two-step neighborhood estimate gives
2(r-1) ≤ |P| when the coefficients have nonnegative total mass, with strict
inequality for positive mass. A zero-mass dependence forces this bound on
both sign domains inside V. Nonzero mass can be necessary only at deficiency
one, and then there is no weighting of ground points giving every retained
support weight one. The remaining tasks ask to augment such packings by a
single pair. In particular the required matching exists up to n+2r-1
supports, and up to n+4r-4 when the supports have equal size.
-/

-- Credit: @zarnab222-dev
open Finset
open scoped Classical
namespace E19Exchange

theorem exists_max_pack {V : Type*} (F : Finset (Finset V)) :
    ∃ M ⊆ F, (M : Set (Finset V)).PairwiseDisjoint id ∧
      ∀ P ⊆ F, (P : Set (Finset V)).PairwiseDisjoint id → P.card ≤ M.card := by
  classical
  let C := F.powerset.filter fun P : Finset (Finset V) => (P : Set (Finset V)).PairwiseDisjoint id
  have empty : ∅ ∈ C := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp⟩
  obtain ⟨M,hM,maxi⟩ := exists_max_image C Finset.card ⟨∅,empty⟩
  exact ⟨M,mem_powerset.mp (mem_filter.mp hM).1,(mem_filter.mp hM).2,
    fun P sub sep => maxi P (mem_filter.mpr ⟨mem_powerset.mpr sub,sep⟩)⟩

theorem cannot_extend {V : Type*} [DecidableEq V] (F M : Finset (Finset V)) (sub : M ⊆ F)
    (sep : (M : Set (Finset V)).PairwiseDisjoint id)
    (maxi : ∀ P ⊆ F, (P : Set (Finset V)).PairwiseDisjoint id → P.card ≤ M.card)
    {e : Finset V} (yes : e ∈ F) (fresh : e ∉ M) (free : ∀ a ∈ M, Disjoint e a) : False := by
  classical
  have sep' : ((insert e M : Finset _) : Set (Finset V)).PairwiseDisjoint id := by
    rw [coe_insert,Set.pairwiseDisjoint_insert_of_notMem (by simpa using fresh)]
    exact ⟨sep,free⟩
  have bound := maxi (insert e M) (insert_subset yes sub) sep'
  rw [card_insert_of_notMem fresh] at bound
  omega

theorem cannot_exchange {V : Type*} [DecidableEq V] (F M : Finset (Finset V)) (sub : M ⊆ F)
    (sep : (M : Set (Finset V)).PairwiseDisjoint id)
    (maxi : ∀ P ⊆ F, (P : Set (Finset V)).PairwiseDisjoint id → P.card ≤ M.card)
    {old a b : Finset V} (h : old ∈ M) (ha : a ∈ F) (hb : b ∈ F)
    (aFresh : a ∉ M) (bFresh : b ∉ M) (ne : a ≠ b) (dis : Disjoint a b)
    (ap : ∀ p ∈ M.erase old, Disjoint a p) (bp : ∀ p ∈ M.erase old, Disjoint b p) : False := by
  classical
  let T := M.erase old
  have af : a ∉ T := fun ha => aFresh (mem_of_mem_erase ha)
  have bf : b ∉ insert a T := by simp [ne.symm,T,bFresh]
  have s0 : (T : Set (Finset V)).PairwiseDisjoint id := sep.subset (by exact_mod_cast erase_subset old M)
  have s1 : ((insert a T : Finset _) : Set (Finset V)).PairwiseDisjoint id := by
    rw [coe_insert,Set.pairwiseDisjoint_insert_of_notMem (by simpa using af)]
    exact ⟨s0,ap⟩
  have s2 : ((insert b (insert a T) : Finset _) : Set (Finset V)).PairwiseDisjoint id := by
    rw [coe_insert,Set.pairwiseDisjoint_insert_of_notMem (by simpa using bf)]
    refine ⟨s1,?_⟩
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact dis.symm
    · exact bp _ hp
  have upper := maxi _ (insert_subset hb (insert_subset ha ((erase_subset old M).trans sub))) s2
  rw [card_insert_of_notMem bf,card_insert_of_notMem af] at upper
  have eq := card_erase_add_one h
  dsimp [T] at upper
  omega

/-- One end of any matched edge has no unmatched neighbor. Otherwise either
a triangle appears, or two disjoint edges replace the single matched edge. -/
theorem safe_end {V : Type*} [DecidableEq V] (F M : Finset (Finset V)) (sub : M ⊆ F)
    (sep : (M : Set (Finset V)).PairwiseDisjoint id)
    (maxi : ∀ P ⊆ F, (P : Set (Finset V)).PairwiseDisjoint id → P.card ≤ M.card)
    (U : Finset V) (unused : ∀ u ∈ U, ∀ p ∈ M, u ∉ p)
    (tri : ∀ a b u : V, {a,b} ∈ F → {a,u} ∈ F → {b,u} ∉ F)
    {a b : V} (ab : a ≠ b) (old : {a,b} ∈ M) :
    (∀ u ∈ U, {a,u} ∉ F) ∨ (∀ u ∈ U, {b,u} ∉ F) := by
  classical
  by_contra! bad
  obtain ⟨⟨x,hx,ax⟩,⟨y,hy,by'⟩⟩ := bad
  have xy : x ≠ y := by
    rintro rfl
    exact tri a b x (sub old) ax by'
  have xo := unused x hx _ old
  have yo := unused y hy _ old
  have axby : Disjoint ({a,x} : Finset V) {b,y} := by
    simp only [disjoint_insert_left,disjoint_singleton_left,mem_insert,mem_singleton,not_or]
    simp only [mem_insert,mem_singleton,not_or] at xo yo
    exact ⟨⟨ab,Ne.symm yo.1⟩,⟨xo.2,xy⟩⟩
  apply cannot_exchange F M sub sep maxi old ax by'
  · exact fun h => unused x hx _ h (by simp)
  · exact fun h => unused y hy _ h (by simp)
  · intro eq
    exact disjoint_left.mp axby (show a ∈ ({a,x} : Finset V) by simp) (eq ▸ (by simp : a ∈ ({a,x} : Finset V)))
  · exact axby
  · intro p hp
    obtain ⟨neq,hp'⟩ := mem_erase.mp hp
    have d := disjoint_left.mp (sep old hp' neq.symm)
    exact disjoint_left.mpr (by
      intro z hz hz'
      rcases mem_insert.mp hz with rfl | hx'
      · exact d (by simp) hz'
      · exact unused x hx p hp' ((mem_singleton.mp hx') ▸ hz'))
  · intro p hp
    obtain ⟨neq,hp'⟩ := mem_erase.mp hp
    have d := disjoint_left.mp (sep old hp' neq.symm)
    exact disjoint_left.mpr (by
      intro z hz hz'
      rcases mem_insert.mp hz with rfl | hy'
      · exact d (by simp) hz'
      · exact unused y hy p hp' ((mem_singleton.mp hy') ▸ hz'))


theorem oriented {X : Type*} [DecidableEq X] (K : Finset X) (adj : X → X → Prop)
    (symm : ∀ {x y}, adj x y → adj y x) (irr : ∀ x, ¬ adj x x)
    (tri : ∀ {x y z}, adj x y → adj x z → ¬ adj y z) :
    ∃ (m : ℕ) (L R : Fin m → X) (U : Finset X),
      (∀ i, L i ∈ K) ∧ (∀ i, R i ∈ K) ∧ Function.Injective L ∧ Function.Injective R ∧
      (∀ i j, L i ≠ R j) ∧ (∀ i, adj (L i) (R i)) ∧ U ⊆ K ∧
      (∀ u ∈ U, ∀ v ∈ U, ¬ adj u v) ∧ (∀ i, ∀ u ∈ U, ¬ adj (L i) u) ∧
      (∀ i, L i ∉ U) ∧ (∀ i, R i ∉ U) ∧ K.card=U.card+2*m ∧
      ∀ (j : ℕ) (l r : Fin j → X), (∀ i, l i ∈ K) → (∀ i, r i ∈ K) →
        Function.Injective l → Function.Injective r → (∀ i k, l i ≠ r k) → (∀ i, adj (l i) (r i)) → j ≤ m := by
  classical
  let F := K.powerset.filter fun e : Finset X => ∃ a b, e={a,b} ∧ adj a b
  have pair {a b : X} : {a,b} ∈ F ↔ a ∈ K ∧ b ∈ K ∧ adj a b := by
    constructor
    · intro h
      obtain ⟨hs,x,y,eq,edge⟩ := mem_filter.mp h
      have sub := mem_powerset.mp hs
      refine ⟨sub (by simp),sub (by simp),?_⟩
      have ha : a=x ∨ a=y := by simpa using (eq ▸ (by simp : a ∈ ({a,b}:Finset X)) : a ∈ ({x,y}:Finset X))
      have hb : b=x ∨ b=y := by simpa using (eq ▸ (by simp : b ∈ ({a,b}:Finset X)) : b ∈ ({x,y}:Finset X))
      have xy : x ≠ y := by rintro rfl; exact irr _ edge
      have ab : a ≠ b := by
        rintro rfl
        have hcard := congrArg Finset.card eq
        simp [xy] at hcard
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | exact edge | exact symm edge | contradiction
    · rintro ⟨ha,hb,ab⟩
      exact mem_filter.mpr ⟨mem_powerset.mpr (by simp [insert_subset_iff,ha,hb]),a,b,rfl,ab⟩
  obtain ⟨M,sub,sep,maxi⟩ := exists_max_pack F
  let covered := M.biUnion id
  let U := K \ covered
  have unused : ∀ u ∈ U, ∀ p ∈ M, u ∉ p := by
    intro u hu p hp h
    exact (mem_sdiff.mp hu).2 (mem_biUnion.mpr ⟨p,hp,h⟩)
  have inside : covered ⊆ K := by
    intro x hx
    obtain ⟨p,hp,hx⟩ := mem_biUnion.mp hx
    exact mem_powerset.mp (mem_filter.mp (sub hp)).1 hx
  have orient (p : M) : ∃ a b, p.val={a,b} ∧ adj a b ∧ ∀ u ∈ U, ¬adj a u := by
    obtain ⟨_,a,b,eq,ab⟩ := mem_filter.mp (sub p.property)
    have h : {a,b} ∈ M := eq ▸ p.property
    have ha := pair.mp (sub h)
    have ne : a ≠ b := by rintro rfl; exact irr _ ab
    have triangle : ∀ x y u : X, {x,y} ∈ F → {x,u} ∈ F → {y,u} ∉ F :=
      fun _ _ _ h1 h2 h3 => tri (pair.mp h1).2.2 (pair.mp h2).2.2 (pair.mp h3).2.2
    rcases safe_end F M sub sep maxi U unused triangle ne h with l | r
    · exact ⟨a,b,eq,ab,fun u hu edge => l u hu (pair.mpr ⟨ha.1,(mem_sdiff.mp hu).1,edge⟩)⟩
    · exact ⟨b,a,by simpa [pair_comm] using eq,symm ab,fun u hu edge => r u hu (pair.mpr ⟨ha.2.1,(mem_sdiff.mp hu).1,edge⟩)⟩
  choose l r hpair edge safe using orient
  have hl (p : M) : l p ∈ p.val := by rw [hpair]; simp
  have hr (p : M) : r p ∈ p.val := by rw [hpair]; simp
  have unique {p q : M} {x : X} (hp : x ∈ p.val) (hq : x ∈ q.val) : p=q := by
    by_contra neq
    exact disjoint_left.mp (sep p.property q.property (fun e => neq (Subtype.ext e))) hp hq
  let e : Fin M.card ≃ M := (M.equivFin).symm
  refine ⟨M.card,l ∘ e,r ∘ e,U,fun i => inside (mem_biUnion.mpr ⟨_,(e i).property,hl _⟩),
    fun i => inside (mem_biUnion.mpr ⟨_,(e i).property,hr _⟩),?_,?_,?_,fun i => edge _,sdiff_subset,
    ?_,fun i => safe _,fun i hu => unused _ hu _ (e i).property (hl _),fun i hu => unused _ hu _ (e i).property (hr _),?_,?_⟩
  · intro i j h
    change l (e i) = l (e j) at h
    exact e.injective (unique (hl (e i)) (h.symm ▸ hl (e j)))
  · intro i j h
    change r (e i) = r (e j) at h
    exact e.injective (unique (hr (e i)) (h.symm ▸ hr (e j)))
  · intro i j h
    change l (e i) = r (e j) at h
    have same : e i=e j := unique (hl (e i)) (h.symm ▸ hr (e j))
    have edge' := edge (e i)
    change l (e i) = r (e j) at h
    rw [← same] at h
    rw [h] at edge'
    exact irr _ edge'
  · intro u hu v hv uv
    apply cannot_extend F M sub sep maxi (pair.mpr ⟨(mem_sdiff.mp hu).1,(mem_sdiff.mp hv).1,uv⟩)
    · intro h
      exact unused _ hu _ h (by simp)
    · intro p hp
      simp [disjoint_insert_left,unused u hu p hp,unused v hv p hp]
  · have two (p : Finset X) (hp : p ∈ M) : p.card=2 := by
      let q : M := ⟨p,hp⟩
      have ne : l q ≠ r q := by intro he; have h := edge q; rw [he] at h; exact irr _ h
      change q.val.card=2
      rw [hpair q,card_pair ne]
    have hcov : covered.card=M.card*2 := by
      rw [show covered=M.biUnion id from rfl,card_biUnion sep]
      simpa using sum_congr rfl two
    have total := card_sdiff_of_subset inside
    have atmost := card_le_card inside
    change K.card = (K \ covered).card+2*M.card
    omega

  · intro j ll rr inL inR il ir distinct linked
    let pairOf (i : Fin j) : Finset X := {ll i,rr i}
    have same {i k : Fin j} {x : X} (hi : x ∈ pairOf i) (hk : x ∈ pairOf k) : i=k := by
      simp only [pairOf,mem_insert,mem_singleton] at hi hk
      rcases hi with hi | hi <;> rcases hk with hk | hk
      · exact il (hi.symm.trans hk)
      · exact (distinct i k (hi.symm.trans hk)).elim
      · exact (distinct k i (hk.symm.trans hi)).elim
      · exact ir (hi.symm.trans hk)
    have inj : Function.Injective pairOf := by
      intro i k eq
      have h : ll i ∈ pairOf i := by simp [pairOf]
      exact same h (eq ▸ h)
    let P := univ.image pairOf
    have hP : P ⊆ F := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      exact pair.mpr ⟨inL _,inR _,linked _⟩
    have sP : (P : Set (Finset X)).PairwiseDisjoint id := by
      intro a ha b hb ne
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      obtain ⟨k,_,rfl⟩ := mem_image.mp hb
      exact disjoint_left.mpr (fun _ h1 h2 => ne (congrArg pairOf (same h1 h2)))
    simpa [P,card_image_of_injective _ inj] using maxi P hP sP

end E19Exchange

open Finset
open scoped Classical
namespace E19Signs

theorem sign_count {α : Type*} (P : Finset α) (rel : α → α → Prop)
    (localTri : ∀ i ∈ P, ∀ j ∈ P, ∀ k ∈ P, rel i j → rel i k → ¬rel j k)
    (f : α → ℝ) (pos : ∀ i ∈ P, 0 < f i) (existsP : P.Nonempty)
    (t T : ℝ) (ht : 0<t) (hT : 0≤T)
    (rows : ∀ i ∈ P, T+t*f i ≤ ∑ j ∈ P.filter (rel i), f j) :
    2*t ≤ P.card ∧ (0<T → 2*t < P.card) := by
  classical
  obtain ⟨i,hi,top⟩ := exists_max_image P f existsP
  let N := P.filter (rel i)
  have nonneg := (pos i hi).le
  have sub : N ⊆ P := filter_subset _ _
  have individual (j) (hj : j ∈ N) :
      T+t*f j ≤ ((P.card:ℝ)-N.card)*f i := by
    obtain ⟨hP,edge⟩ := mem_filter.mp hj
    have dis : P.filter (rel j) ⊆ P \ N := by
      intro k hk
      obtain ⟨hK,jk⟩ := mem_filter.mp hk
      exact mem_sdiff.mpr ⟨hK,fun ik => localTri i hi j hP k hK edge (mem_filter.mp ik).2 jk⟩
    have cap := sum_le_sum (s := P.filter (rel j)) (fun k hk => top k (mem_filter.mp hk).1)
    simp only [sum_const,nsmul_eq_mul] at cap
    have num := card_le_card dis
    rw [card_sdiff_of_subset sub] at num
    have num' : ((P.filter (rel j)).card:ℝ) ≤ (P.card:ℝ)-N.card := by
      have a := card_le_card sub
      have b : (P.filter (rel j)).card+N.card ≤ P.card := by omega
      exact le_sub_iff_add_le.mpr (by exact_mod_cast b)
    exact (rows j hP).trans (cap.trans (mul_le_mul_of_nonneg_right num' nonneg))
  have total := sum_le_sum individual
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum] at total
  have first := mul_le_mul_of_nonneg_left (rows i hi) ht.le
  change t*(T+t*f i) ≤ t*(∑ j ∈ N, f j) at first
  have sq : (N.card:ℝ)*((P.card:ℝ)-N.card) ≤ ((P.card:ℝ)/2)^2 := by
    nlinarith [sq_nonneg ((N.card:ℝ)-(P.card:ℝ)/2)]
  have h := mul_le_mul_of_nonneg_right sq nonneg
  have nonnegD : 0 ≤ (N.card:ℝ)*T := by positivity
  have key : t*T+t^2*f i ≤ ((P.card:ℝ)/2)^2*f i := by nlinarith only [h,first,total,nonnegD]
  have square : t^2 ≤ ((P.card:ℝ)/2)^2 := by
    apply le_of_mul_le_mul_right _ (pos i hi)
    linarith [mul_nonneg ht.le hT]
  have size : 0 ≤ (P.card:ℝ) := by positivity
  constructor
  · nlinarith only [square,ht,size,sq_nonneg (t-(P.card:ℝ)/2)]
  · intro gt
    have ls : t^2 < ((P.card:ℝ)/2)^2 := by
      apply (mul_lt_mul_iff_left₀ (pos i hi)).mp
      linarith [mul_pos ht gt]
    nlinarith only [ls,ht,size,sq_nonneg (t-(P.card:ℝ)/2)]

theorem sign_alternative {α : Type*} [Fintype α] (V : Finset α) (rel : α → α → Prop)
    (tri : ∀ i j k, rel i j → rel i k → ¬rel j k)
    (isolate : ∀ i ∉ V, ∀ j, ¬rel i j) (s : ℕ) (hs : 0<s)
    (d g : α → ℝ) (floorD : ∀ i, (s:ℝ) ≤ d i) (nz : ∃ i, g i ≠ 0)
    (rows : ∀ i, (∑ j, g j) + d i*g i = ∑ j ∈ univ.filter (rel i), g j) :
    ((∑ j, g j) ≠ 0 ∧ 2*s < V.card) ∨ ((∑ j, g j)=0 ∧ 4*s ≤ V.card) := by
  classical
  have side (f : α → ℝ) (T : ℝ) (hT : 0 ≤ T) (somePos : ∃ j, 0<f j)
      (eqn : ∀ i, T + d i*f i = ∑ j ∈ univ.filter (rel i), f j) :
      let P := univ.filter fun j => 0 < f j
      P ⊆ V ∧ 2*s ≤ P.card ∧ (0<T → 2*s<P.card) := by
    let P := univ.filter fun j => 0 < f j
    have pos (i) (hi : i ∈ P) := (mem_filter.mp hi).2
    have nonempty : P.Nonempty := by
      obtain ⟨j,hj⟩ := somePos
      exact ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
    have bound := sign_count P rel (fun i _ j _ k _ => tri i j k) f pos nonempty
      (s:ℝ) T (by exact_mod_cast hs) hT (by
      intro i hi
      have first := mul_le_mul_of_nonneg_right (floorD i) (pos i hi).le
      have cap := sum_le_sum (s := univ.filter (rel i)) (fun j _ => (show f j ≤ (if 0 < f j then f j else 0) by split_ifs <;> linarith))
      rw [← sum_filter] at cap
      have equal : ((univ.filter (rel i)).filter fun j => 0 < f j) = P.filter (rel i) := by
        ext j
        simp [P,and_comm]
      rw [equal] at cap
      linarith [eqn i])
    refine ⟨?_,by exact_mod_cast bound.1,fun h => by exact_mod_cast bound.2 h⟩
    intro i hi
    by_contra h
    have empty : univ.filter (rel i)=∅ := by ext j; simp [isolate i h j]
    have eq := eqn i
    rw [empty,sum_empty] at eq
    have hdi := lt_of_lt_of_le (show (0:ℝ)<s by exact_mod_cast hs) (floorD i)
    linarith [mul_pos hdi (pos i hi)]
  have has_pos (f : α → ℝ) (T : 0 ≤ ∑ j, f j) (nz' : ∃ i, f i ≠ 0) : ∃ i, 0<f i := by
    by_contra! nonpos
    obtain ⟨i,hi⟩ := nz'
    have low := sum_nonpos (s := univ.erase i) (fun j _ => nonpos j)
    rw [← sum_erase_add _ _ (mem_univ i)] at T
    exact hi (by linarith [nonpos i])
  have nzNeg : ∃ i, (-g i) ≠ 0 := by simpa using nz
  have negEq (i) : -(∑ j, g j) + d i*(-g i) = ∑ j ∈ univ.filter (rel i), -g j := by
    simp only [sum_neg_distrib,mul_neg]
    linarith [rows i]
  rcases lt_trichotomy (∑ j, g j) 0 with neg | zero | pos
  · have h := side (fun j => -g j) _ (neg_nonneg.mpr neg.le) (has_pos _ (by simpa using neg.le) nzNeg) negEq
    exact Or.inl ⟨neg.ne,(h.2.2 (neg_pos.mpr neg)).trans_le (card_le_card h.1)⟩
  · have a := side g _ zero.ge (has_pos _ zero.ge nz) rows
    have b := side (fun j => -g j) _ (by rw [zero,neg_zero]) (has_pos _ (by simp [zero]) nzNeg) negEq
    let P := univ.filter fun i => 0 < g i
    let Q := univ.filter fun i => 0 < -g i
    have dis : Disjoint P Q := disjoint_left.mpr (by intro i hp hq; have p := (mem_filter.mp hp).2; have q := (mem_filter.mp hq).2; linarith)
    have total := card_le_card (union_subset a.1 b.1)
    change (P ∪ Q).card ≤ V.card at total
    rw [card_union_of_disjoint dis] at total
    have pa : 2*s ≤ P.card := a.2.1
    have pb : 2*s ≤ Q.card := b.2.1
    exact Or.inr ⟨zero,by omega⟩
  · have h := side g _ pos.le (has_pos _ pos.le nz) rows
    exact Or.inl ⟨pos.ne',(h.2.2 pos).trans_le (card_le_card h.1)⟩




theorem dependent_columns {ι α : Type*} [Fintype ι] [Fintype α] (v : ι → α → ℝ)
    (large : Fintype.card α < Fintype.card ι) :
    ∃ g : ι → ℝ, (∃ i, g i ≠ 0) ∧ ∀ j, ∑ i, g i * v i j = 0 := by
  classical
  by_contra! good
  have indep : LinearIndependent ℝ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    by_contra neq
    obtain ⟨j,hj⟩ := good g ⟨i,neq⟩
    apply hj
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hg j
  have cap := indep.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at cap
  omega

theorem incidence_rows {n : ℕ} (K : Finset (Finset (Fin n)))
    (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (posSize : ∀ A ∈ K, 0 < A.card) (g : K → ℝ)
    (column : ∀ i : Fin n, ∑ B : K, g B * (if i ∈ B.val then 1 else 0) = 0) :
    ∀ A : K, (∑ B, g B) + ((A.val.card:ℝ)-1)*g A = ∑ B ∈ univ.filter (fun B : K => Disjoint A.val B.val), g B := by
  classical
  let v (A : K) (i : Fin n) : ℝ := if i ∈ A.val then 1 else 0
  let N (A : K) := univ.filter fun B : K => Disjoint A.val B.val
  have gram (A B : K) : (∑ i ∈ A.val, v B i) =
      (1 + (if B=A then (A.val.card:ℝ)-1 else 0)) - (if B ∈ N A then 1 else 0) := by
    have pos : 0 < A.val.card := posSize _ A.property
    by_cases same : B=A
    · subst B
      have nonempty := (card_pos.mp pos).ne_empty
      simp [v,N,nonempty]
    have diff : A.val ≠ B.val := fun he => same (Subtype.ext he.symm)
    have cap := linear _ A.property _ B.property diff
    by_cases ab : Disjoint A.val B.val
    · have zero := Finset.disjoint_iff_inter_eq_empty.mp ab
      simp [v,N,same,ab,zero]
    · have yes := card_pos.mpr (not_disjoint_iff_nonempty_inter.mp ab)
      have one : (A.val ∩ B.val).card=1 := by omega
      simp [v,N,same,ab,one]
  intro A
  change (∑ B, g B) + ((A.val.card:ℝ)-1)*g A = ∑ B ∈ N A, g B
  change ∀ i, ∑ B : K, g B * v B i = 0 at column
  have he : ∑ B : K, g B * (∑ i ∈ A.val, v B i) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [column, Finset.sum_const_zero]
  simp only [gram,mul_sub,mul_add,mul_one,mul_ite,mul_zero,sum_sub_distrib,sum_add_distrib] at he
  have rhs : (∑ B : K, if B ∈ N A then g B else 0) = ∑ B ∈ N A, g B := by
    rw [← sum_filter]
    congr 1
    ext x
    simp
  rw [rhs] at he
  simp only [sum_ite_eq', mem_univ, if_true] at he
  linarith


theorem dependence {n : ℕ} (K : Finset (Finset (Fin n))) (large : n < K.card) :
    ∃ g : K → ℝ, (∃ A, g A ≠ 0) ∧
      (n+1 < K.card → (∑ A, g A) = 0) ∧
      ∀ i : Fin n, ∑ B : K, g B * (if i ∈ B.val then 1 else 0) = 0 := by
  classical
  let v (A : K) (i : Fin n) : ℝ := if i ∈ A.val then 1 else 0
  by_cases deficit : n+1 < K.card
  · obtain ⟨g,nz,cols⟩ := dependent_columns (fun A : K => Fin.cons (1:ℝ) (v A))
      (by simpa using deficit)
    exact ⟨g,nz,fun _ => by simpa using cols 0,fun i => by simpa [v] using cols i.succ⟩
  · obtain ⟨g,nz,cols⟩ := dependent_columns v (by simpa using large)
    exact ⟨g,nz,fun h => (deficit h).elim,cols⟩

theorem normalized_mass {n : ℕ} (K : Finset (Finset (Fin n))) (g : K → ℝ)
    (cols : ∀ i : Fin n, ∑ B : K, g B * (if i ∈ B.val then 1 else 0) = 0)
    (w : Fin n → ℝ) (hw : ∀ A ∈ K, ∑ i ∈ A,w i = 1) : ∑ A, g A = 0 := by
  classical
  calc ∑ A, g A = ∑ A : K, g A * (∑ i ∈ A.val, w i) := by simp [hw]
       _ = ∑ A : K, ∑ i : Fin n, w i * (g A * (if i ∈ A.val then 1 else 0)) := by
         apply sum_congr rfl
         intro A _
         rw [mul_sum]
         simp only [mul_ite,mul_one,mul_zero,← sum_filter]
         have sub : univ.filter (fun i => i ∈ A.val) = A.val := by ext; simp
         rw [sub]
         exact sum_congr rfl (fun _ _ => mul_comm ..)
       _ = _ := by rw [sum_comm]; simp only [←mul_sum,cols,mul_zero,sum_const_zero]

theorem retained_obstruction {n r : ℕ} (U V : Finset (Finset (Fin n))) (apart : Disjoint U V)
    (linear : ∀ A ∈ U ∪ V, ∀ B ∈ U ∪ V, A ≠ B → (A ∩ B).card ≤ 1)
    (sizes : ∀ A ∈ U ∪ V, r ≤ A.card) (hr : 2 ≤ r)
    (meetU : ∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B)
    (cross : ∀ A ∈ V, ∀ B ∈ U, ¬ Disjoint A B)
    (triangle : ∀ A ∈ U ∪ V, ∀ B ∈ U ∪ V, ∀ C ∈ U ∪ V, Disjoint A B → Disjoint A C → ¬ Disjoint B C)
    (large : n < U.card+V.card) :
    (U.card+V.card=n+1 ∧ 2*(r-1)<V.card ∧ ¬ ∃ w : Fin n → ℝ, ∀ A ∈ U ∪ V, ∑ i ∈ A, w i = 1) ∨
     (4*(r-1) ≤ V.card ∧ ∃ g : (U ∪ V : Finset _) → ℝ,
       (∃ A, g A ≠ 0) ∧ (∑ A, g A)=0 ∧ (∀ A, A.val ∈ U → g A=0) ∧
       ∀ i : Fin n, ∑ B, g B * (if i ∈ B.val then 1 else 0) = 0) := by
  classical
  let K := U ∪ V
  have count : K.card=U.card+V.card := card_union_of_disjoint apart
  have posSize (A) (hA : A ∈ K) : 0<A.card := by have h := sizes A hA; omega
  obtain ⟨g,nz,affine,cols⟩ := dependence K (by omega)
  let F := univ.filter (fun A : K => A.val ∈ V)
  have vcard : F.card=V.card := by
    let e := Function.Embedding.subtype (fun A => A ∈ K)
    have eq : F.map e=V := by
      ext A
      simp [F,e,K]
      exact Or.inr
    rw [←eq,card_map]
  have isolate (A : K) (hA : A ∉ F) (B : K) : ¬Disjoint A.val B.val := by
    have aU := (mem_union.mp A.property).resolve_right (fun h => hA (mem_filter.mpr ⟨mem_univ _,h⟩))
    rcases mem_union.mp B.property with bU | bV
    · exact meetU _ aU _ bU
    · exact fun dis => cross _ bV _ aU dis.symm
  have floorD (A : K) : ((r-1:ℕ):ℝ) ≤ (A.val.card:ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    have e : (r:ℝ) ≤ A.val.card := by exact_mod_cast sizes _ A.property
    linarith
  have out := sign_alternative F (fun A B : K => Disjoint A.val B.val)
    (fun A B C => triangle _ A.property _ B.property _ C.property)
    isolate (r-1) (by omega) (fun A => (A.val.card:ℝ)-1) g floorD nz (by
      intro A
      rw [incidence_rows K linear posSize g cols A]
      congr! 3)
  rw [vcard] at out
  rcases out with ⟨mass,big⟩ | ⟨zero,big⟩
  · have h : ¬ n+1<K.card := fun d => mass (affine d)
    exact Or.inl ⟨by omega,big,fun ⟨w,hw⟩ => mass (normalized_mass K g cols w hw)⟩
  · refine Or.inr ⟨big,g,nz,zero,?_,cols⟩
    intro A hU
    have noV : A ∉ F := by
      intro h
      exact disjoint_left.mp apart hU (mem_filter.mp h).2
    have empty : univ.filter (fun B : K => Disjoint A.val B.val) = ∅ := by
      ext B
      simp [isolate A noV B]
    have eq := incidence_rows K linear posSize g cols A
    rw [empty,sum_empty,zero,zero_add] at eq
    have p : (1:ℝ)<A.val.card := by exact_mod_cast (show 1 < A.val.card by have := sizes A.val A.property; omega)
    exact (mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr p.ne')

theorem matching_from_augmentation {n r : ℕ} (K : Finset (Finset (Fin n))) (hr : 2 ≤ r)
    (size : ∀ A ∈ K, r ≤ A.card) (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (noThree : ¬ ∃ T ⊆ K, T.card=3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B)
    (augment :
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card+2*m →
    (n < U.card + m) →
    ((U.card+m = n+1 ∧ (2 * (r - 1) < m) ∧ ¬ ∃ w : Fin n → ℝ, ∀ A ∈ U ∪ univ.image L, ∑ i ∈ A, w i = 1) ∨
      ((4 * (r - 1) ≤ m) ∧ ∃ g : (U ∪ univ.image L : Finset _) → ℝ, (∃ A, g A ≠ 0) ∧ (∑ A, g A)=0 ∧
        (∀ A, A.val ∈ U → g A=0) ∧ ∀ i : Fin n, ∑ B, g B * (if i ∈ B.val then 1 else 0) = 0)) →
    ∃ l r' : Fin (m+1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)) :
    ∃ l r' : Fin (K.card-n) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i) := by
  classical
  let adj (A B : Finset (Fin n)) := A ∈ K ∧ B ∈ K ∧ A ≠ B ∧ Disjoint A B
  have tri {A B C} (ab : adj A B) (ac : adj A C) (bc : adj B C) : False := by
    apply noThree
    refine ⟨{A,B,C},by simpa only [insert_subset_iff,singleton_subset_iff] using ⟨ab.1,ab.2.1,ac.2.1⟩,
      by simp [ab.2.2.1,ac.2.2.1,bc.2.2.1],?_⟩
    intro X hX Y hY ne
    simp only [mem_insert,mem_singleton] at hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> first | contradiction | exact ab.2.2.2 | exact ac.2.2.2 | exact bc.2.2.2 | exact ab.2.2.2.symm | exact ac.2.2.2.symm | exact bc.2.2.2.symm
  obtain ⟨m,L,R,U,hL,hR,injL,injR,apart,edges,subU,meetU,cross,disU,disR,count,maxi⟩ :=
    E19Exchange.oriented K adj (fun h => ⟨h.2.1,h.1,h.2.2.1.symm,h.2.2.2.symm⟩)
      (fun _ h => h.2.2.1 rfl) (fun ab ac bc => tri ab ac bc)
  have enough : K.card-n ≤ m := by
    by_contra! few
    let V := univ.image L
    have vcard : V.card=m := by simp [V,card_image_of_injective _ injL]
    have subV : V ⊆ K := by rintro A h; obtain ⟨i,_,rfl⟩ := mem_image.mp h; exact hL i
    have sub := union_subset subU subV
    have nonempty (A) (ha : A ∈ K) : ¬ Disjoint A A := by
      have h := size A ha
      intro dis
      have emp : A=∅ := disjoint_self.mp dis
      rw [emp,card_empty] at h
      omega
    have lift {A B} (ha : A ∈ K) (hb : B ∈ K) (h : ¬adj A B) : ¬Disjoint A B := by
      intro d
      by_cases e : A=B
      · exact nonempty A ha (e ▸ d)
      · exact h ⟨ha,hb,e,d⟩
    have dUV : Disjoint U V := by
      apply disjoint_left.mpr
      rintro A hu hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact disU i hu
    have umeet : ∀ A ∈ U, ∀ B ∈ U, ¬Disjoint A B := fun A ha B hb => lift (subU ha) (subU hb) (meetU A ha B hb)
    have lmeet : ∀ i, ∀ B ∈ U, ¬Disjoint (L i) B := fun i B hb => lift (hL i) (subU hb) (cross i B hb)
    have big : n<U.card+m := by omega
    have split := E19Signs.retained_obstruction U V dUV
      (fun A ha B hb => linear A (sub ha) B (sub hb)) (fun A ha => size A (sub ha)) (by omega)
      umeet (by intro A ha B hb; obtain ⟨i,_,rfl⟩ := mem_image.mp ha; exact lmeet i B hb)
      (by
        intro A ha B hb C hc ab ac bc
        have mk {X Y} (hx : X ∈ U ∪ V) (hy : Y ∈ U ∪ V) (dis : Disjoint X Y) : adj X Y :=
          ⟨sub hx,sub hy,fun h => nonempty X (sub hx) (h ▸ dis),dis⟩
        exact tri (mk ha hb ab) (mk ha hc ac) (mk hb hc bc))
      (by omega)
    have dLR (i) := (edges i).2.2.2
    rw [vcard] at split
    have alter := augment m L R U hL hR injL injR apart dLR subU umeet lmeet disU disR count big split
    obtain ⟨l,r',ml,mr,il,ir,distinct,links⟩ := alter
    have bad := maxi _ l r' ml mr il ir distinct (fun i => ⟨ml i,mr i,distinct i i,links i⟩)
    omega
  let e := Fin.castLEEmb enough
  exact ⟨L ∘ e,R ∘ e,fun i => hL _,fun i => hR _,injL.comp e.injective,injR.comp e.injective,
    fun i j => apart _ _,fun i => (edges (e i)).2.2.2⟩

/-- The wider band applies whenever all supports can receive the same
nonzero total weight, including every uniform support family. -/
theorem matching_in_band {n r : ℕ} (K : Finset (Finset (Fin n))) (hr : 2 ≤ r)
    (size : ∀ A ∈ K, r ≤ A.card) (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (noThree : ¬ ∃ T ⊆ K, T.card=3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B)
    (band : K.card ≤ n+2*(r-1)+1 ∨
      (K.card ≤ n+4*(r-1) ∧ ∃ w : Fin n → ℝ, ∀ A ∈ K, ∑ i ∈ A, w i = 1)) :
    ∃ l r' : Fin (K.card-n) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i) := by
  classical
  apply matching_from_augmentation K hr size linear noThree
  intro m L R U hL _ _ _ _ _ subU _ _ _ _ count big split
  have subV : univ.image L ⊆ K := by
    intro A ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact hL i
  rcases split with ⟨_,bound,noWeight⟩ | ⟨bound,_⟩
  · rcases band with small | ⟨_,w,hw⟩
    · omega
    · exact (noWeight ⟨w,fun A ha => hw A ((union_subset subU subV) ha)⟩).elim
  · rcases band with small | ⟨small,_⟩ <;> omega

theorem uniform_matching_in_band {n r : ℕ} (K : Finset (Finset (Fin n))) (hr : 2 ≤ r)
    (size : ∀ A ∈ K, r ≤ A.card) (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (noThree : ¬ ∃ T ⊆ K, T.card=3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) (uniform : ∀ A ∈ K, A.card=r)
    (band : K.card ≤ n+4*(r-1)) :
    ∃ l r' : Fin (K.card-n) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i) := by
  apply matching_in_band K hr size linear noThree
  refine Or.inr ⟨band,fun _ => (r:ℝ)⁻¹,?_⟩
  intro A ha
  simp [uniform A ha,show (r:ℝ) ≠ 0 by exact_mod_cast (show r ≠ 0 by omega)]

end E19Signs
namespace OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1

def H1 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r*r+r-1 ≤ n →
    n ≤ r*((n-r)/(r-1)) →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →

    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card+2*m →
    (U.card + m = n + 1) → (2 * (r - 1) < m) →
    (¬ ∃ w : Fin n → ℝ, ∀ A ∈ U ∪ univ.image L, ∑ i ∈ A, w i = 1) →
    ∃ l r' : Fin (m+1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

def H2 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r*r+r-1 ≤ n →
    n ≤ r*((n-r)/(r-1)) →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →

    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card+2*m →
    (n < U.card + m) → (4 * (r - 1) ≤ m) →
    (∃ g : (U ∪ univ.image L : Finset _) → ℝ, (∃ A, g A ≠ 0) ∧ (∑ A, g A)=0 ∧
      (∀ A, A.val ∈ U → g A=0) ∧ ∀ i : Fin n, ∑ B, g B * (if i ∈ B.val then 1 else 0) = 0) →
    ∃ l r' : Fin (m+1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_R1_H2_R1.H2 := by
  intro one two n r K hr gap pack witness size linear degree large disorder notSplit noThree
  apply E19Signs.matching_from_augmentation K (by omega) size linear noThree
  intro m L R U hL hR injL injR apart dLR subU umeet lmeet disU disR count big split
  rcases split with ⟨total,bound,weights⟩ | ⟨bound,dep⟩
  · exact one n r K hr gap pack witness size linear degree large disorder notSplit noThree
      m L R U hL hR injL injR apart dLR subU umeet lmeet disU disR count total bound weights
  · exact two n r K hr gap pack witness size linear degree large disorder notSplit noThree
      m L R U hL hR injL injR apart dLR subU umeet lmeet disU disR count big bound dep
end OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1
