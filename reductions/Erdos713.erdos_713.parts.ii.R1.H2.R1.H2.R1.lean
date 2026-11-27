import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1_H2_R1

-- Credit: @zarnab222-dev
/-!
The four-cycle and the threshold for embedding a bipartite graph with degree
two on one side divide the rational-exponent question at 3/2.

If F contains a four-cycle, finite-field polarity graphs avoiding C4 also
avoid F. Bertrand's postulate and padding give an order n^(3/2) lower bound
uniformly for large n. Conversely, if every vertex on one side of F has degree at most two, an
order n^(3/2) upper bound follows by counting pairs in common neighborhoods.
We find a set whose distinct pairs all have at least |F| common neighbors,
embed the opposite side there, and choose distinct images for the remaining
vertices. These bounds rule out alpha < 3/2 and alpha > 3/2 respectively.
For patterns satisfying both graph conditions, these give matching order bounds.
At equality the exponent is already rational.

For the common-neighborhood argument see J. Fox and B. Sudakov, "Dependent
Random Choice" (2011), https://arxiv.org/abs/0909.3271. For the classical
four-cycle construction see P. Erdős, A. Rényi and V. T. Sós, "On a problem
of graph theory" (1966).
-/
open Finset SimpleGraph
open scoped Classical
namespace E713Polarity

theorem free_of_common {W : Type*} (X : SimpleGraph W)
    (one : ∀ a b u v, a≠b → X.Adj a u → X.Adj b u → X.Adj a v → X.Adj b v → u=v) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free X := by
  rintro ⟨e⟩
  have edge (i j : Fin 2) : X.Adj (e (Sum.inl i)) (e (Sum.inr j)) :=
    e.toHom.map_rel' (show (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl i) (Sum.inr j) from Or.inl ⟨rfl,rfl⟩)
  have ne : e (Sum.inl 0) ≠ e (Sum.inl 1) := fun h => (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj (e.injective h))
  have eq := one _ _ _ _ ne (edge 0 0) (edge 1 0) (edge 0 1) (edge 1 1)
  exact (by decide : (0:Fin 2) ≠ 1) (Sum.inr.inj (e.injective eq))

theorem witness (K : Type*) [Field K] [Fintype K] :
    ∃ G : SimpleGraph (K × K), (completeBipartiteGraph (Fin 2) (Fin 2)).Free G ∧
      (Fintype.card K)^2*(Fintype.card K-1) ≤ 2*G.edgeFinset.card := by
  classical
  let G : SimpleGraph (K × K) := {
    Adj p q := p ≠ q ∧ p.2+q.2=p.1*q.1
    symm := ⟨by intro a b h; exact ⟨h.1.symm,by simpa only [add_comm b.2,mul_comm b.1] using h.2⟩⟩
    loopless := ⟨fun a h => h.1 rfl⟩ }
  refine ⟨G,?_,?_⟩
  · apply free_of_common
    intro a b u v ne au bu av bv
    have dx : a.1≠b.1 := by
      intro h
      apply ne
      apply Prod.ext h
      have h1 := au.2
      rw [h] at h1
      exact add_right_cancel (h1.trans bu.2.symm)
    have zero : (a.1-b.1)*(u.1-v.1)=0 := by
      linear_combination -au.2+bu.2+av.2-bv.2
    have x := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr dx))
    refine Prod.ext x ?_
    have h := au.2
    rw [x] at h
    exact add_left_cancel (h.trans av.2.symm)
  · have per (p : K × K) : Fintype.card K-1 ≤ G.degree p := by
      let f : K ↪ K × K := ⟨fun x => (x,p.1*x-p.2),fun x y h => congrArg Prod.fst h⟩
      let T := (univ : Finset K).erase p.1
      have sub : T.map f ⊆ G.neighborFinset p := by
        intro w hw
        obtain ⟨x,hx,rfl⟩ := mem_map.mp hw
        apply (G.mem_neighborFinset _ _).mpr
        refine ⟨fun eq => (mem_erase.mp hx).1 (congrArg Prod.fst eq).symm,?_⟩
        change p.2+(p.1*x-p.2)=p.1*x
        ring
      have h := card_le_card sub
      rw [card_map,G.card_neighborFinset_eq_degree] at h
      simpa [T] using h
    have h := sum_le_sum (s:=univ) fun p _ => per p
    rw [sum_const,card_univ,smul_eq_mul,Fintype.card_prod,G.sum_degrees_eq_twice_card_edges] at h
    rw [pow_two]
    convert! h using 1
    congr!
end E713Polarity
namespace E713Amplify
theorem padding {V W : Type*} [Fintype W] (G : SimpleGraph V) (active : ∀ v, ¬G.IsIsolated v)
    (X : SimpleGraph W) (free : G.Free X) (m : ℕ) (fit : Fintype.card W ≤ m) :
    X.edgeFinset.card ≤ extremalNumber m G := by
  classical
  let k := m-Fintype.card W
  let Z := X ⊕g (⊥ : SimpleGraph (Fin k))
  have hf : G.Free Z := by
    rintro ⟨e⟩
    have original (v : V) : ∃ w : W, e v = Sum.inl w := by
      cases h : e v with
      | inl w => exact ⟨w,rfl⟩
      | inr i =>
        obtain ⟨u,adj⟩ := exists_adj_iff_not_isIsolated.mpr (active v)
        have a := e.toHom.map_rel' adj
        change Z.Adj (e v) (e u) at a
        rw [h] at a
        cases hu : e u with
        | inl t => rw [hu] at a; exact (not_adj_sum_inl_inr t i a.symm).elim
        | inr j => rw [hu] at a; exact (sum_adj_inr.mp a).elim
    choose f he using original
    apply free
    refine ⟨⟨⟨f,?_⟩,?_⟩⟩
    · intro a b adj
      have h := e.toHom.map_rel' adj
      change Z.Adj (e a) (e b) at h
      rw [he a,he b] at h
      exact sum_adj_inl.mp h
    · intro a b eq
      exact e.injective ((he a).trans ((congrArg Sum.inl eq).trans (he b).symm))
  have sumedges : Z.edgeFinset.card=X.edgeFinset.card := by
    simp only [Z,edgeFinset_card]
    have eq := Fintype.card_congr (edgeSetSumEquiv (G:=X) (H:=(⊥ : SimpleGraph (Fin k))))
    simpa using eq
  have hh := card_edgeFinset_le_extremalNumber hf
  have sz : Fintype.card (W ⊕ Fin k)=m := by simp [k,fit]
  simpa only [sumedges,sz] using hh



end E713Amplify
namespace E713Interpolation
open E713Polarity Filter Asymptotics
open scoped Topology

theorem active (v) : ¬(completeBipartiteGraph (Fin 2) (Fin 2)).IsIsolated v := by
  apply exists_adj_iff_not_isIsolated.mp
  cases v with
  | inl i => exact ⟨Sum.inr 0,Or.inl ⟨rfl,rfl⟩⟩
  | inr j => exact ⟨Sum.inl 0,Or.inr ⟨rfl,rfl⟩⟩

theorem lower (n p : ℕ) (prime : p.Prime) (fit : p^2 ≤ n) :
    p^3 ≤ 2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) + p^2 := by
  classical
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨G,free,edge⟩ := witness (ZMod p)
  have sz : Fintype.card (ZMod p × ZMod p) ≤ n := by simpa [pow_two] using fit
  have pad := E713Amplify.padding (completeBipartiteGraph (Fin 2) (Fin 2)) active G free n sz
  rw [ZMod.card] at edge
  have pp : p-1+1=p := by have := prime.pos; omega
  calc p^3 = p^2*((p-1)+1) := by rw [pp]; ring
       _ ≤ 2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2))+p^2 := by rw [Nat.mul_add,Nat.mul_one]; change _ ≤ 2*G.edgeFinset.card at edge; omega

/-- A uniform lower estimate independent of any prime-gap asymptotic. -/
theorem lower_uniform (n : ℕ) (large : 16 ≤ n) :
    (Nat.sqrt n)^3 ≤ 32*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  let k := Nat.sqrt n
  have h4 : 4 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hdiv : k/2 ≠ 0 := by omega
  obtain ⟨p,prime,lo,hi⟩ := Nat.exists_prime_lt_and_le_two_mul _ hdiv
  have pk : p ≤ k := by omega
  have half : k ≤ 2*p := by omega
  have fit : p^2 ≤ n := (Nat.pow_le_pow_left pk 2).trans (by simpa [pow_two,k] using Nat.sqrt_le n)
  have lb := lower n p prime fit
  have p2 : 2 ≤ p := prime.two_le
  have twice := Nat.mul_le_mul_left (p^2) p2
  have cube := Nat.pow_le_pow_left half 3
  change k^3 ≤ _
  nlinarith only [lb,twice,cube]

end E713Interpolation
/- Common neighborhoods supply pairwise extensions for embedding a bipartite
graph in which vertices on one side have degree at most two. -/
open SimpleGraph Finset
open scoped Classical
namespace E713Pairs

theorem rich_set {W : Type*} [Fintype W] (X : SimpleGraph W) (s : ℕ)
    (dense : (Fintype.card W)^3*(s^2+2*s) < (2*X.edgeFinset.card)^2) :
    ∃ A : Finset W, s ≤ A.card ∧
      ∀ u ∈ A, ∀ v ∈ A, u≠v → s ≤ (X.neighborFinset u ∩ X.neighborFinset v).card := by
  classical
  let V := (univ : Finset W)
  let pairs := (univ : Finset (W × W))
  let common (p : W × W) := X.neighborFinset p.1 ∩ X.neighborFinset p.2
  let bad := pairs.filter fun p => p.1≠p.2 ∧ (common p).card < s
  let inside (p : W × W) := bad.filter fun e => e.1 ∈ common p ∧ e.2 ∈ common p
  have sym (p e : W × W) : (e.1 ∈ common p ∧ e.2 ∈ common p) ↔
      (p.1 ∈ common e ∧ p.2 ∈ common e) := by
    simp only [common,mem_inter,SimpleGraph.mem_neighborFinset]
    grind [SimpleGraph.adj_comm]
  have products (e : W × W) : (pairs.filter fun p => e.1 ∈ common p ∧ e.2 ∈ common p) =
      common e ×ˢ common e := by ext p; simp only [pairs,mem_filter,mem_univ,true_and,mem_product,sym p e]
  have total_bad : ∑ p ∈ pairs, (inside p).card ≤ (Fintype.card W)^2*s^2 := by
    simp only [inside,Finset.card_filter]
    rw [sum_comm]
    have per (e) (he : e ∈ bad) : (∑ p ∈ pairs, if e.1 ∈ common p ∧ e.2 ∈ common p then 1 else 0) ≤ s^2 := by
      rw [← Finset.card_filter,products,card_product,← pow_two]
      exact Nat.pow_le_pow_left (mem_filter.mp he).2.2.le 2
    apply (sum_le_sum per).trans
    rw [sum_const,smul_eq_mul]
    have le : bad.card ≤ (Fintype.card W)^2 := (card_le_univ bad).trans_eq (by simp [pow_two])
    exact Nat.mul_le_mul_right _ le
  have fibers (v : W) : (pairs.filter (fun p => v ∈ common p)) =
      X.neighborFinset v ×ˢ X.neighborFinset v := by
    ext p
    simp [pairs,common,SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm]
  have asFilter (p : W × W) : common p = V.filter (fun v => v ∈ common p) := by ext v; simp [V]
  have total : (∑ p ∈ pairs,(common p).card) = ∑ v, (X.degree v)^2 := by
    calc _ = ∑ p ∈ pairs, ∑ v ∈ V, if v ∈ common p then 1 else 0 := by
           apply sum_congr rfl
           intro p _
           rw [← Finset.card_filter,← asFilter]
         _ = _ := by
           rw [sum_comm]
           apply sum_congr rfl
           intro v _
           rw [← Finset.card_filter,fibers,card_product,X.card_neighborFinset_eq_degree,pow_two]
  have cs := sq_sum_le_card_mul_sum_sq (s:=(univ : Finset W)) (f:=fun v => X.degree v)
  rw [card_univ,X.sum_degrees_eq_twice_card_edges,← total] at cs
  have existsPair : ∃ p ∈ pairs, (inside p).card+s < (common p).card := by
    by_contra! all
    have cap := sum_le_sum all
    rw [sum_add_distrib,sum_const,smul_eq_mul] at cap
    have n2 : pairs.card = (Fintype.card W)^2 := by simp [pairs,pow_two]
    rw [n2] at cap
    have num := Nat.mul_le_mul_left (Fintype.card W) (cap.trans (Nat.add_le_add_right total_bad _))
    nlinarith only [dense,cs,num]
  obtain ⟨p,_,hp⟩ := existsPair
  let D := (inside p).image Prod.fst
  let A := common p \ D
  have fit : s ≤ A.card := by
    have h : D.card ≤ (inside p).card := card_image_le
    have loss := Finset.le_card_sdiff D (common p)
    dsimp [A]
    omega
  refine ⟨A,fit,?_⟩
  intro u hu v hv ne
  by_contra! few
  have f : (u,v) ∈ bad := mem_filter.mpr ⟨mem_univ _,ne,few⟩
  have b : (u,v) ∈ inside p := mem_filter.mpr ⟨f,(mem_sdiff.mp hu).1,(mem_sdiff.mp hv).1⟩
  exact (mem_sdiff.mp hu).2 (mem_image.mpr ⟨(u,v),b,rfl⟩)

theorem distinct_choices {L W : Type*} [Fintype L] [Fintype W] (D : Finset W)
    (choices : L → Finset W) (many : ∀ v, D.card+Fintype.card L ≤ (choices v).card) :
    ∃ f : L ↪ W, ∀ v, f v ∈ choices v ∧ f v ∉ D := by
  classical
  have go (P : Finset L) : ∃ f : P ↪ W, ∀ v, f v ∈ choices v.val ∧ f v ∉ D := by
    induction P using Finset.induction_on with
    | empty => exact ⟨⟨fun x => (notMem_empty x.val x.property).elim,fun x => (notMem_empty x.val x.property).elim⟩,
        fun x => (notMem_empty x.val x.property).elim⟩
    | @insert v P miss ih =>
      obtain ⟨f,valid⟩ := ih
      let used := D ∪ univ.map f
      have strict : P.card < Fintype.card L := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨subset_univ _,fun h => miss (h ▸ mem_univ v)⟩)
      have sz : used.card < (choices v).card := by
        have h := card_union_le D (univ.map f)
        rw [card_map,card_univ,Fintype.card_coe] at h
        change (D ∪ univ.map f).card < _
        have bound := many v
        omega
      obtain ⟨w,hw,un⟩ := exists_mem_notMem_of_card_lt_card sz
      have fresh (j : P) : w ≠ f j := fun eq => un (mem_union_right D (mem_map.mpr ⟨j,mem_univ _,eq.symm⟩))
      let old (j : ↥(insert v P)) (h : j.val ≠ v) : P := ⟨j.val,(mem_insert.mp j.property).resolve_left h⟩
      let g (j : ↥(insert v P)) := if h : j.val=v then w else f (old j h)
      refine ⟨⟨g,?_⟩,?_⟩
      · intro x y eq
        by_cases hx : x.val=v <;> by_cases hy : y.val=v
        · exact Subtype.ext (hx.trans hy.symm)
        · exact (fresh (old y hy) (by simpa [g,hx,hy] using eq)).elim
        · exact (fresh (old x hx) (by simpa [g,hx,hy] using eq.symm)).elim
        · exact Subtype.ext (congrArg (fun a : P => a.val) (f.injective (by simpa [g,hx,hy] using eq : f (old x hx)=f (old y hy))))
      · intro j
        change g j ∈ choices j.val ∧ g j ∉ D
        by_cases h : j.val=v
        · simpa [g,h] using (show w ∈ choices v ∧ w ∉ D from ⟨hw,fun hd => un (mem_union_left _ hd)⟩)
        · simpa [g,h,old] using valid (old j h)
  obtain ⟨g,valid⟩ := go univ
  let f : L ↪ W := ⟨fun v => g ⟨v,mem_univ _⟩,fun _ _ eq => congrArg Subtype.val (g.injective eq)⟩
  exact ⟨f,fun v => valid ⟨v,mem_univ _⟩⟩

/-- Embed the high-degree side in A. Enlarge the image of each remaining vertex’s neighborhood to a pair
in A, then choose a fresh common neighbor as its image. -/
theorem embed {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) (A : Finset W)
    (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R)) (left : ∀ v ∉ R, F.degree v ≤ 2)
    (two : 2 ≤ A.card) (fit : Fintype.card V ≤ A.card)
    (rich : ∀ u ∈ A, ∀ v ∈ A, u≠v → Fintype.card V ≤ (X.neighborFinset u ∩ X.neighborFinset v).card) :
    F ⊑ X := by
  classical
  let L := Rᶜ
  let inj : R ↪ A := R.equivFin.toEmbedding.trans
    ((Fin.castLEEmb ((card_le_univ R).trans fit)).trans A.equivFin.symm.toEmbedding)
  let f : R ↪ W := inj.trans (Function.Embedding.subtype _)
  let D := univ.map f
  let ns (v : L) := univ.filter fun x : R => F.Adj v.val x.val
  have neighbors (v : L) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ (ns v).map f ⊆ {a,b} := by
    have inside : (ns v).map f ⊆ A := by
      intro w hw
      obtain ⟨i,_,rfl⟩ := mem_map.mp hw
      exact (inj i).property
    have sub : (ns v).map (Function.Embedding.subtype _) ⊆ F.neighborFinset v.val := by
      intro u hu
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hu
      exact (F.mem_neighborFinset _ _).mpr (mem_filter.mp hi).2
    have size := card_le_card sub
    rw [card_map, F.card_neighborFinset_eq_degree] at size
    have cap : ((ns v).map f).card ≤ 2 := by
      rw [card_map]
      exact size.trans (left v.val (mem_compl.mp v.property))
    obtain ⟨T,contains,within,twoT⟩ := exists_subsuperset_card_eq inside cap two
    obtain ⟨a,b,ne,rfl⟩ := card_eq_two.mp twoT
    exact ⟨a,within (by simp),b,within (by simp),ne,contains⟩
  choose a ha b hb ne adj using neighbors
  let opts (v : L) := X.neighborFinset (a v) ∩ X.neighborFinset (b v)
  have total : D.card+Fintype.card L=Fintype.card V := by simp [D,L,Nat.add_sub_of_le (card_le_univ R)]
  have many (v : L) : D.card+Fintype.card L ≤ (opts v).card := by
    rw [total]
    exact rich _ (ha v) _ (hb v) (ne v)
  obtain ⟨g,valid⟩ := distinct_choices D opts many
  have link (u : L) (v : R) (h : F.Adj u.val v.val) : X.Adj (g u) (f v) := by
    have mapped : f v ∈ (ns u).map f := mem_map.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
    have hv := adj u mapped
    rcases mem_insert.mp hv with he | he
    · rw [he]
      exact ((X.mem_neighborFinset _ _).mp (mem_inter.mp (valid u).1).1).symm
    · rw [mem_singleton.mp he]
      exact ((X.mem_neighborFinset _ _).mp (mem_inter.mp (valid u).1).2).symm
  let h (v : V) := if mem : v ∈ R then f ⟨v,mem⟩ else g ⟨v,mem_compl.mpr mem⟩
  refine ⟨⟨⟨h,?_⟩,?_⟩⟩
  · intro u v edge
    by_cases hu : u ∈ R
    · have hv := (colors u v edge).mp hu
      simpa [h,hu,hv] using (link ⟨v,mem_compl.mpr hv⟩ ⟨u,hu⟩ edge.symm).symm
    · have hv := (colors v u edge.symm).mpr hu
      simpa [h,hu,hv] using link ⟨u,mem_compl.mpr hu⟩ ⟨v,hv⟩ edge
  · intro u v eq
    change h u=h v at eq
    have apart (x : R) (y : L) : f x ≠ g y := fun he => (valid y).2 (mem_map.mpr ⟨x,mem_univ _,he⟩)
    by_cases hu : u∈R <;> by_cases hv : v∈R
    · exact congrArg Subtype.val (f.injective (by simpa [h,hu,hv] using eq : f ⟨u,hu⟩=f ⟨v,hv⟩))
    · exact (apart ⟨u,hu⟩ ⟨v,mem_compl.mpr hv⟩ (by simpa [h,hu,hv] using eq)).elim
    · exact (apart ⟨v,hv⟩ ⟨u,mem_compl.mpr hu⟩ (by simpa [h,hu,hv] using eq.symm)).elim
    · exact congrArg Subtype.val (g.injective (by simpa [h,hu,hv] using eq :
        g ⟨u,mem_compl.mpr hu⟩=g ⟨v,mem_compl.mpr hv⟩))

theorem degree_two_bound {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    (R : Finset V) (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (left : ∀ v ∉ R, F.degree v ≤ 2) (n : ℕ) (nonemptyEdges : F ≠ ⊥) :
    (2*extremalNumber n F)^2 ≤ n^3*((Fintype.card V)^2+2*Fintype.card V) := by
  classical
  have witness : ∃ X : SimpleGraph (Fin n), F.Free X ∧ X.edgeFinset.card = extremalNumber n F := by
    obtain ⟨X,_,ext⟩ := exists_isExtremal_free (V:=Fin n) nonemptyEdges
    obtain ⟨avoid,h⟩ := isExtremal_free_iff.mp ext
    refine ⟨X,avoid,?_⟩
    convert! h using 1
    · congr! 2
    · rw [Fintype.card_fin]
  obtain ⟨X,avoid,edges⟩ := witness
  by_contra! dense
  rw [← edges] at dense
  have h : (Fintype.card (Fin n))^3*((Fintype.card V)^2+2*Fintype.card V) < (2*X.edgeFinset.card)^2 := by
    simpa only [Fintype.card_fin] using dense
  obtain ⟨A,fit,rich⟩ := rich_set X (Fintype.card V) h
  obtain ⟨u,v,edge⟩ := ne_bot_iff_exists_adj.mp nonemptyEdges
  have two : 2 ≤ Fintype.card V := by
    have sz := card_le_univ ({u,v} : Finset V)
    simpa [edge.ne] using sz
  exact avoid (embed F X R A colors left (two.trans fit) fit rich)

end E713Pairs

namespace E713Exponents
open Filter Asymptotics Real

theorem smaller {a b : ℝ} (h : a<b) :
    (fun n : ℕ => (n:ℝ)^a) =o[atTop] (fun n : ℕ => (n:ℝ)^b) := by
  have pos : ∀ᶠ n : ℕ in atTop, 0<(n:ℝ) := (eventually_gt_atTop (0:ℕ)).mono fun n hn => by exact_mod_cast hn
  apply (isLittleO_iff_tendsto' (pos.mono fun n hn hz => ((Real.rpow_pos_of_pos hn b).ne' hz).elim)).2
  apply ((tendsto_rpow_neg_atTop (sub_pos.mpr h)).comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [pos] with n hn
  change (n:ℝ)^(-(b-a)) = (n:ℝ)^a/(n:ℝ)^b
  rw [neg_sub,Real.rpow_sub hn]

theorem mono_ex {V W : Type*} {F : SimpleGraph V} {H : SimpleGraph W} (sub : F ⊑ H) (n : ℕ) :
    extremalNumber n F ≤ extremalNumber n H := by
  classical
  have goal : extremalNumber (Fintype.card (Fin n)) F ≤ extremalNumber (Fintype.card (Fin n)) H := by
    apply (extremalNumber_le_iff ..).mpr
    intro X _ free
    exact card_edgeFinset_le_extremalNumber (H:=H) (G:=X) (fun ff => free (sub.trans ff))
  simpa using goal

theorem power (n : ℕ) (hn : 0<(n:ℝ)) : (n:ℝ)^(3/2:ℝ) = (Real.sqrt n)^3 := by
  rw [show (3/2:ℝ) = 1+(1/2:ℝ) by norm_num,Real.rpow_add hn,Real.rpow_one,← Real.sqrt_eq_rpow]
  nlinarith [congrArg (· * Real.sqrt n) (Real.sq_sqrt hn.le)]

theorem square_lower {V : Type*} (F : SimpleGraph V) (sub : completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F) :
    (fun n : ℕ => (n:ℝ)^(3/2:ℝ)) =O[atTop] (fun n : ℕ => (extremalNumber n F : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨256,?_⟩
  filter_upwards [eventually_ge_atTop (16:ℕ)] with n hn
  have pos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have one : (1:ℝ) ≤ Nat.sqrt n := by exact_mod_cast (show 1 ≤ Nat.sqrt n from Nat.le_sqrt.mpr (by omega))
  have root : Real.sqrt n ≤ 2*(Nat.sqrt n:ℝ) := by linarith [Real.real_sqrt_le_nat_sqrt_succ (a:=n)]
  have cap := E713Interpolation.lower_uniform n hn
  have full := cap.trans (Nat.mul_le_mul_left 32 (mono_ex sub n))
  have cast : (Nat.sqrt n:ℝ)^3 ≤ 32*(extremalNumber n F : ℝ) := by exact_mod_cast full
  have cube := pow_le_pow_left₀ (Real.sqrt_nonneg _) root 3
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg pos.le _),Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),power n pos]
  nlinarith only [cast,cube]

theorem degree_upper {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V) (R : Finset V)
    (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R)) (left : ∀ v ∉ R, F.degree v ≤ 2) (nb : F ≠ ⊥) :
    (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n:ℝ)^(3/2:ℝ)) := by
  let C := (Fintype.card V)^2+2*Fintype.card V
  apply isBigO_iff.mpr
  refine ⟨(C:ℝ)+1,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have pos : (0:ℝ)<n := by exact_mod_cast hn
  have h : (2*(extremalNumber n F:ℝ))^2 ≤ (n:ℝ)^3*(C:ℝ) := by exact_mod_cast E713Pairs.degree_two_bound F R colors left n nb
  have cmp : (C:ℝ) ≤ ((C:ℝ)+1)^2 := by nlinarith [sq_nonneg (C:ℝ),Nat.cast_nonneg (α:=ℝ) C]
  have r := Real.sqrt_nonneg (n:ℝ)
  have eq : ((Real.sqrt n)^3)^2 = (n:ℝ)^3 := by rw [← pow_mul, mul_comm, pow_mul,Real.sq_sqrt pos.le]
  have t : (extremalNumber n F : ℝ)^2 ≤ (((C:ℝ)+1)*(Real.sqrt n)^3)^2 := by
    rw [mul_pow,eq]
    nlinarith only [h,mul_le_mul_of_nonneg_left cmp (show 0 ≤ (n:ℝ)^3 by positivity),sq_nonneg (extremalNumber n F : ℝ)]
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg pos.le _),power n pos]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp t

/-- When the two graph conditions overlap, the extremal exponent is exactly 3/2
in the sense of matching order bounds. This also applies to disconnected patterns. -/
theorem square_degree_two_theta {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V)
    (square : completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F)
    (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (left : ∀ v ∉ R, F.degree v ≤ 2) :
    (fun n : ℕ => (extremalNumber n F : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)^(3/2:ℝ)) := by
  have nonemptyEdges : F ≠ ⊥ := by
    rintro rfl
    obtain ⟨copy⟩ := square
    exact copy.toHom.map_rel' (show (completeBipartiteGraph (Fin 2) (Fin 2)).Adj
      (Sum.inl 0) (Sum.inr 0) from Or.inl ⟨rfl,rfl⟩)
  exact ⟨degree_upper F R colors left nonemptyEdges, square_lower F square⟩

end E713Exponents
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology

namespace OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1

/-- Below exponent 3/2 the forbidden graph must be four-cycle-free. -/
def H1 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.Connected → G.IsBipartite →
    (∀ v, 2 ≤ G.degree v) → (completeBipartiteGraph (Fin 2) (Fin 2)).Free G →
    ∀ α : ℝ, α ∈ Set.Ioo 1 (3/2:ℝ) →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

/-- Above exponent 3/2 both sides of any proper bipartition must contain a vertex
of degree at least three. Either side can be chosen as R. -/
def H2 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.Connected → G.IsBipartite →
    (∀ v, 2 ≤ G.degree v) →
    (∀ R : Finset (Fin q), (∀ u v, G.Adj u v → (u ∈ R ↔ v ∉ R)) →
      ∃ v ∉ R, 3 ≤ G.degree v) →
    ∀ α : ℝ, α ∈ Set.Ioo (3/2:ℝ) 2 →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

theorem main : H1 → H2 → OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1.H2 := by
  intro small large q G conn bip minDeg α range big sharp
  classical
  rcases lt_trichotomy α (3/2:ℝ) with lt|eq|gt
  · apply small q G conn bip minDeg _ α ⟨range.1,lt⟩ big sharp
    intro sub
    have impossible := ((E713Exponents.square_lower G sub).trans big).trans_isLittleO (E713Exponents.smaller lt)
    have nonzero : ∃ᶠ n : ℕ in atTop, (n:ℝ)^(3/2:ℝ) ≠ 0 :=
      ((eventually_gt_atTop (0:ℕ)).mono fun n hn => (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne').frequently
    exact isLittleO_irrefl nonzero impossible
  · exact ⟨(3/2:ℚ),by push_cast; linarith⟩
  · apply large q G conn bip minDeg _ α ⟨gt,range.2⟩ big sharp
    intro R colors
    by_contra! thin
    have left (v) (out : v ∉ R) : G.degree v ≤ 2 := by have := thin v out; omega
    have nb : G ≠ ⊥ := by
      obtain ⟨v⟩ := conn.nonempty
      rintro rfl
      have h := minDeg v
      simp at h
    exact sharp ((E713Exponents.degree_upper G R colors left nb).trans_isLittleO (E713Exponents.smaller gt))

end OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1
