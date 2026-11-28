import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1

/-!
Upper bound for the fattened subdivisions K(r,t) of complete graphs: r main vertices and t private
common neighbours for every pair. If G on n vertices does not contain K(r,t) then
2 e(G) ≤ (1+o(1)) sqrt(t-1) n^(3/2).

Notation: cod u v is the number of common neighbours, q = r + t r^2, σ^2 the sum of squared degrees.

1. Pairs with cod ≥ q form a graph Q without a clique of size r (choose witnesses by Hall's theorem).
2. Second moment. Fix y and F = N(y). For every x the set C = N(x) ∩ F spans at most (1-1/(r-1))|C|^2
   ordered pairs of Q by Turán's theorem, and every other pair lies in at most q-1 of the sets C. Double
   counting gives Σ_x cod(x,y)^2 ≤ (r-1)((q-1) d(y)^2 + s(y)), s(y) the number of walks of length two
   from y; summing over y, Σ cod^2 ≤ (r-1) q σ^2. By Cauchy–Schwarz σ^2 = Σ cod ≤ n sqrt(Σ cod^2), so
   σ^2 ≤ (r-1) q n^2.
3. Hence vertices of degree above D carry at most (r-1) q n^2/D edges; deleting these edges leaves a
   graph of maximum degree at most D.
4. In a graph of maximum degree Λ sqrt(n) with 2e > (1+ε) sqrt(t-1) n^(3/2): the set Good of vertices with
   s(v) ≥ (1+ε/2) sqrt(t-1) σ has at least c n elements, and by Cauchy–Schwarz every subset B of Good has
   Σ_{u,v in B} cod(u,v) ≥ (1+ε/2)^2 (t-1) |B|^2. Since pairs of large cod carry little weight (2.), in
   every subset of Good of linear size some vertex has linearly many partners with t ≤ cod ≤ K.
5. Choose main vertices one at a time inside shrinking linear subsets of Good, each time discarding the
   O(sqrt(n)) vertices adjacent to an earlier main vertex or to a common neighbour of two earlier main
   vertices. The r vertices obtained are pairwise non-adjacent, pairwise have t common neighbours, and no
   vertex is adjacent to three of them, so the common neighbourhoods of distinct pairs are disjoint and
   K(r,t) embeds.
-/

open SimpleGraph Finset Filter
open scoped Classical Topology

namespace E713D

abbrev Fat (r t : ℕ) : SimpleGraph (Fin r ⊕ ({p : Fin r × Fin r // p.1 < p.2} × Fin t)) :=
  SimpleGraph.fromRel (fun u v => ∃ i p k, u = Sum.inl i ∧ v = Sum.inr (p,k) ∧ (i = p.1.1 ∨ i = p.1.2))

variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- The number of common neighbours. -/
noncomputable def cod (u v : V) : ℕ := (G.neighborFinset u ∩ G.neighborFinset v).card

theorem cod_comm (u v : V) : cod G u v = cod G v u := by
  unfold cod
  rw [inter_comm]

/-- Independent vertices, pairwise with t common neighbours, no vertex adjacent to three of them. -/
theorem embed2 (r t : ℕ) (S : Finset V) (hS : S.card = r)
    (indep : ∀ u ∈ S, ∀ w ∈ S, ¬G.Adj u w)
    (many : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → t ≤ cod G u w)
    (two : ∀ x, (S.filter (fun u => G.Adj x u)).card ≤ 2) : Fat r t ⊑ G := by
  let f (i : Fin r) : V := ((Finset.equivFinOfCardEq hS).symm i : V)
  have fS (i : Fin r) : f i ∈ S := ((Finset.equivFinOfCardEq hS).symm i).2
  have inj : Function.Injective f := fun i j h =>
    (Finset.equivFinOfCardEq hS).symm.injective (Subtype.ext h)
  have room (p : {p : Fin r × Fin r // p.1 < p.2}) :
      Nonempty (Fin t ↪ ↥(G.neighborFinset (f p.1.1) ∩ G.neighborFinset (f p.1.2))) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin,Fintype.card_coe]
    exact many _ (fS _) _ (fS _) (fun h => p.2.ne (inj h))
  let e (p : {p : Fin r × Fin r // p.1 < p.2}) := (room p).some
  let g (x : {p : Fin r × Fin r // p.1 < p.2} × Fin t) : V := (e x.1 x.2 : V)
  have left (x) : G.Adj (f x.1.1.1) (g x) :=
    (G.mem_neighborFinset _ _).mp (mem_inter.mp (e x.1 x.2).2).1
  have right (x) : G.Adj (f x.1.1.2) (g x) :=
    (G.mem_neighborFinset _ _).mp (mem_inter.mp (e x.1 x.2).2).2
  have fresh (x) (i : Fin r) : f i ≠ g x := by
    intro h
    exact indep _ (fS x.1.1.1) _ (fS i) (h ▸ left x)
  have ginj : Function.Injective g := by
    rintro ⟨p,k⟩ ⟨p',k'⟩ h
    have same : p = p' := by
      by_contra ne
      let U : Finset (Fin r) := {p.1.1,p.1.2,p'.1.1,p'.1.2}
      have sub : U.image f ⊆ S.filter (fun u => G.Adj (g (p,k)) u) := by
        intro w hw
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hw
        refine mem_filter.mpr ⟨fS i,?_⟩
        simp only [U,mem_insert,mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact (left (p,k)).symm
        · exact (right (p,k)).symm
        · rw [h]; exact (left (p',k')).symm
        · rw [h]; exact (right (p',k')).symm
      have small : U.card ≤ 2 := by
        rw [← card_image_of_injective U inj]
        exact (card_le_card sub).trans (two _)
      have pair : ({p.1.1,p.1.2} : Finset (Fin r)) ⊆ U := by
        intro i hi
        simp only [mem_insert,mem_singleton] at hi
        simp only [U,mem_insert,mem_singleton]
        tauto
      have eq := eq_of_subset_of_card_le pair (by rw [card_pair p.2.ne]; exact small)
      have m1 : p'.1.1 ∈ ({p.1.1,p.1.2} : Finset (Fin r)) := by rw [eq]; simp [U]
      have m2 : p'.1.2 ∈ ({p.1.1,p.1.2} : Finset (Fin r)) := by rw [eq]; simp [U]
      simp only [mem_insert,mem_singleton] at m1 m2
      have lt := p.2
      have lt' := p'.2
      apply ne
      apply Subtype.ext
      apply Prod.ext
      · rcases m1 with h1 | h1 <;> rcases m2 with h2 | h2 <;> first | exact h1.symm | (rw [h1,h2] at lt'; exact absurd lt' (lt_irrefl _)) | (rw [h1,h2] at lt'; exact absurd (lt.trans lt') (lt_irrefl _))
      · rcases m1 with h1 | h1 <;> rcases m2 with h2 | h2 <;> first | exact h2.symm | (rw [h1,h2] at lt'; exact absurd lt' (lt_irrefl _)) | (rw [h1,h2] at lt'; exact absurd (lt.trans lt') (lt_irrefl _))
    subst same
    have hk : e p k = e p k' := Subtype.ext h
    rw [(e p).injective hk]
  have edge (a b : Fin r ⊕ ({p : Fin r × Fin r // p.1 < p.2} × Fin t))
      (h : ∃ i p k, a = Sum.inl i ∧ b = Sum.inr (p,k) ∧ (i = p.1.1 ∨ i = p.1.2)) :
      G.Adj (Sum.elim f g a) (Sum.elim f g b) := by
    obtain ⟨i,p,k,rfl,rfl,hi | hi⟩ := h
    · rw [hi]
      exact left (p,k)
    · rw [hi]
      exact right (p,k)
  refine ⟨⟨⟨Sum.elim f g,?_⟩,?_⟩⟩
  · intro a b h
    rcases ((SimpleGraph.fromRel_adj _ a b).mp h).2 with h | h
    · exact edge a b h
    · exact (edge b a h).symm
  · rintro (i|x) (j|y) h
    · exact congrArg Sum.inl (inj h)
    · exact (fresh y i h).elim
    · exact (fresh x j h.symm).elim
    · exact congrArg Sum.inr (ginj h)

/-- The invariant of the greedy choice: S the chosen main vertices, A the remaining candidates. -/
def Inv (t B : ℕ) (S A : Finset V) : Prop :=
  (∀ u ∈ S, ∀ w ∈ S, ¬G.Adj u w) ∧ (∀ u ∈ S, ∀ w ∈ S, u ≠ w → t ≤ cod G u w) ∧
  (∀ x, (S.filter (fun u => G.Adj x u)).card ≤ 2) ∧
  (∀ a ∈ A, a ∉ S ∧ ∀ u ∈ S, ¬G.Adj a u ∧ t ≤ cod G a u ∧ cod G a u ≤ B) ∧
  (∀ a ∈ A, ∀ x, G.Adj x a → (S.filter (fun u => G.Adj x u)).card ≤ 1)

theorem extend (t B K δ : ℕ) (S A : Finset V) (inv : Inv G t B S A) (maxdeg : ∀ z, G.degree z ≤ δ)
    (v : V) (hv : v ∈ A) (hB : B ≤ K) :
    ∃ A', A' ⊆ A ∧ Inv G t K (insert v S) A' ∧
      (A.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card ≤ A'.card+(1+S.card*B)*δ := by
  obtain ⟨i1,i2,i3,a2,a3⟩ := inv
  have hvS := (a2 v hv).1
  have hvu := (a2 v hv).2
  let Forb : Finset V := G.neighborFinset v ∪
    S.biUnion (fun u => (G.neighborFinset v ∩ G.neighborFinset u).biUnion (fun x => G.neighborFinset x))
  let P := A.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)
  have insertFilter (x : V) : ((insert v S).filter (fun u => G.Adj x u)).card ≤
      (S.filter (fun u => G.Adj x u)).card+(if G.Adj x v then 1 else 0) := by
    rw [filter_insert]
    split_ifs with h
    · exact card_insert_le _ _
    · exact Nat.le_refl _
  refine ⟨P \ Forb,sdiff_subset.trans (filter_subset _ _),⟨?_,?_,?_,?_,?_⟩,?_⟩
  · intro u hu w hw
    rcases mem_insert.mp hu with eu | hu' <;> rcases mem_insert.mp hw with ew | hw'
    · rw [eu,ew]; exact G.irrefl
    · rw [eu]; exact (hvu w hw').1
    · rw [ew]; exact fun h => (hvu u hu').1 h.symm
    · exact i1 u hu' w hw'
  · intro u hu w hw ne
    rcases mem_insert.mp hu with eu | hu' <;> rcases mem_insert.mp hw with ew | hw'
    · exact (ne (eu.trans ew.symm)).elim
    · rw [eu]; exact (hvu w hw').2.1
    · rw [ew,cod_comm]; exact (hvu u hu').2.1
    · exact i2 u hu' w hw' ne
  · intro x
    have h := insertFilter x
    by_cases hx : G.Adj x v
    · rw [if_pos hx] at h
      have := a3 v hv x hx
      omega
    · rw [if_neg hx] at h
      have := i3 x
      omega
  · intro a ha
    obtain ⟨hP,hF⟩ := mem_sdiff.mp ha
    obtain ⟨hA,ne,lo,hi⟩ := mem_filter.mp hP
    have nadj : ¬G.Adj a v := fun h =>
      hF (mem_union_left _ ((G.mem_neighborFinset _ _).mpr h.symm))
    refine ⟨fun h => ?_,fun u hu => ?_⟩
    · rcases mem_insert.mp h with h | h
      · exact ne h
      · exact (a2 a hA).1 h
    · rcases mem_insert.mp hu with eu | hu'
      · rw [eu]; exact ⟨nadj,lo,hi⟩
      · obtain ⟨h1,h2,h3⟩ := (a2 a hA).2 u hu'
        exact ⟨h1,h2,h3.trans hB⟩
  · intro a ha x xa
    obtain ⟨hP,hF⟩ := mem_sdiff.mp ha
    obtain ⟨hA,-,-,-⟩ := mem_filter.mp hP
    have h := insertFilter x
    by_cases hx : G.Adj x v
    · rw [if_pos hx] at h
      have none : S.filter (fun u => G.Adj x u) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro u hu
        obtain ⟨uS,xu⟩ := mem_filter.mp hu
        apply hF
        apply mem_union_right
        refine mem_biUnion.mpr ⟨u,uS,mem_biUnion.mpr ⟨x,mem_inter.mpr ⟨?_,?_⟩,?_⟩⟩
        · exact (G.mem_neighborFinset _ _).mpr hx.symm
        · exact (G.mem_neighborFinset _ _).mpr xu.symm
        · exact (G.mem_neighborFinset _ _).mpr xa
      rw [none,card_empty] at h
      exact h
    · rw [if_neg hx] at h
      exact h.trans (a3 a hA x xa)
  · have forb : Forb.card ≤ (1+S.card*B)*δ := by
      have nb (x : V) : (G.neighborFinset x).card ≤ δ := by
        rw [G.card_neighborFinset_eq_degree]
        exact maxdeg x
      have inner (u) (hu : u ∈ S) : ((G.neighborFinset v ∩ G.neighborFinset u).biUnion
          (fun x => G.neighborFinset x)).card ≤ B*δ := by
        apply card_biUnion_le.trans
        calc _ ≤ ∑ _x ∈ G.neighborFinset v ∩ G.neighborFinset u, δ := sum_le_sum fun x _ => nb x
          _ = (G.neighborFinset v ∩ G.neighborFinset u).card*δ := by rw [sum_const,smul_eq_mul]
          _ ≤ B*δ := Nat.mul_le_mul_right _ (hvu u hu).2.2
      have outer : (S.biUnion (fun u => (G.neighborFinset v ∩ G.neighborFinset u).biUnion
          (fun x => G.neighborFinset x))).card ≤ S.card*(B*δ) := by
        apply card_biUnion_le.trans
        calc _ ≤ ∑ _u ∈ S, B*δ := sum_le_sum inner
          _ = _ := by rw [sum_const,smul_eq_mul]
      have h := (card_union_le _ _).trans (Nat.add_le_add (nb v) outer)
      calc Forb.card ≤ δ+S.card*(B*δ) := h
        _ = _ := by ring
    have h := card_le_card_sdiff_add_card (s:=P) (t:=Forb)
    change P.card ≤ _
    omega

/-- Turán's theorem for a set of vertices, counting ordered adjacent pairs. -/
theorem turan_pairs (Q : SimpleGraph V) (s : ℕ)
    (cf : Q.CliqueFree (s+1)) (C : Finset V) :
    s*(C.offDiag.filter (fun p => Q.Adj p.1 p.2)).card ≤ (s-1)*C.card^2 := by
  let Qc := Q.induce (C : Set V)
  have cfc : Qc.CliqueFree (s+1) := cf.comap ⟨Copy.induce Q (C : Set V)⟩
  have turan : 2*s*Qc.edgeFinset.card ≤ (s-1)*C.card^2 := by
    have h := cfc.card_edgeFinset_le
    simp only at h
    rw [← card_edgeFinset_turanGraph] at h
    have h2 := (Nat.mul_le_mul_left (2*s) h).trans mul_card_edgeFinset_turanGraph_le
    simpa using h2
  have deg (a : (C : Set V)) : Qc.degree a = (Q.neighborFinset a.val ∩ C).card := by
    have mapEq := SimpleGraph.map_neighborFinset_induce (G := Q) (s := (C : Set V)) a
    have count := congrArg Finset.card mapEq
    rw [card_map,card_neighborFinset_eq_degree,Finset.toFinset_coe] at count
    convert! count using 1
    congr!
  have total : ∑ a ∈ C, (Q.neighborFinset a ∩ C).card = 2*Qc.edgeFinset.card := by
    rw [← Qc.sum_degrees_eq_twice_card_edges,← Finset.sum_coe_sort C]
    exact (sum_congr rfl fun a _ => deg a).symm
  have fib : (C.offDiag.filter (fun p => Q.Adj p.1 p.2)).card = ∑ a ∈ C, (Q.neighborFinset a ∩ C).card := by
    rw [card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=C)
      (fun p hp => (mem_offDiag.mp (mem_filter.mp hp).1).1)]
    apply sum_congr rfl
    intro a ha
    have eq : (C.offDiag.filter (fun p => Q.Adj p.1 p.2)).filter (fun p => p.1 = a) =
        (Q.neighborFinset a ∩ C).map ⟨fun b => (a,b),fun b c h => (Prod.ext_iff.mp h).2⟩ := by
      ext ⟨x,y⟩
      constructor
      · intro h
        obtain ⟨h1,h2⟩ := mem_filter.mp h
        obtain ⟨off,adj⟩ := mem_filter.mp h1
        have hx : x = a := h2
        subst hx
        exact mem_map.mpr ⟨y,mem_inter.mpr ⟨(Q.mem_neighborFinset _ _).mpr adj,(mem_offDiag.mp off).2.1⟩,rfl⟩
      · intro h
        obtain ⟨b,hb,e⟩ := mem_map.mp h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
        obtain ⟨adj,hC⟩ := mem_inter.mp hb
        have adj' := (Q.mem_neighborFinset _ _).mp adj
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_offDiag.mpr ⟨ha,hC,adj'.ne⟩,adj'⟩,rfl⟩
    rw [eq,card_map]
  rw [fib,total]
  calc s*(2*Qc.edgeFinset.card) = 2*s*Qc.edgeFinset.card := by ring
    _ ≤ _ := turan

/-- The sum of squared degrees. -/
noncomputable def sig : ℕ := ∑ x, G.degree x^2

theorem filter_univ_adj (x : V) : (univ.filter (fun z => G.Adj x z)).card = G.degree x := by
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext z
  simp

theorem cod_eq (u v : V) : cod G u v = ((G.neighborFinset v).filter (fun z => G.Adj u z)).card := by
  unfold cod
  congr 1
  ext z
  simp only [mem_inter,mem_neighborFinset,mem_filter]
  tauto

theorem cod_self (u : V) : cod G u u = G.degree u := by
  unfold cod
  rw [inter_self,G.card_neighborFinset_eq_degree]

/-- Walks of length two, counted from both ends. -/
theorem walks (A : Finset V) : ∑ v ∈ A, ∑ x ∈ G.neighborFinset v, G.degree x =
    ∑ x, G.degree x*(A.filter (fun z => G.Adj x z)).card := by
  have inner (v : V) : ∑ x ∈ G.neighborFinset v, G.degree x = ∑ x, if G.Adj v x then G.degree x else 0 := by
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext x
    simp
  rw [sum_congr rfl (fun v _ => inner v),sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← sum_filter,sum_const,smul_eq_mul,mul_comm]
  congr 2
  ext v
  simp only [mem_filter]
  exact ⟨fun h => ⟨h.1,h.2.symm⟩,fun h => ⟨h.1,h.2.symm⟩⟩

theorem walks_total : ∑ v, ∑ x ∈ G.neighborFinset v, G.degree x = sig G := by
  rw [walks G univ]
  unfold sig
  apply sum_congr rfl
  intro x _
  rw [filter_univ_adj,pow_two]

/-- The codegree sum over a set B, counted through the common neighbours. -/
theorem codsum (B : Finset V) :
    ∑ x, (B.filter (fun z => G.Adj x z)).card^2 = ∑ v ∈ B, ∑ u ∈ B, cod G u v := by
  have sq (x : V) : (B.filter (fun z => G.Adj x z)).card^2 =
      ∑ v ∈ B, ∑ u ∈ B, if G.Adj x u ∧ G.Adj x v then 1 else 0 := by
    rw [pow_two,card_filter,sum_mul_sum]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro u _
    split_ifs <;> simp_all
  rw [sum_congr rfl (fun x _ => sq x),sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [← card_filter]
  unfold cod
  congr 1
  ext x
  simp only [mem_filter,mem_univ,true_and,mem_inter,mem_neighborFinset]
  exact ⟨fun h => ⟨h.1.symm,h.2.symm⟩,fun h => ⟨h.1.symm,h.2.symm⟩⟩

theorem sig_eq : sig G = ∑ v, ∑ u, cod G u v := by
  rw [← codsum G univ]
  unfold sig
  apply sum_congr rfl
  intro x _
  rw [filter_univ_adj]

/-- Lemma H: Cauchy–Schwarz for the walks starting in B. -/
theorem hereditary (B : Finset V) :
    (∑ v ∈ B, ∑ x ∈ G.neighborFinset v, G.degree x)^2 ≤ sig G*∑ v ∈ B, ∑ u ∈ B, cod G u v := by
  rw [walks,← codsum]
  exact sum_mul_sq_le_sq_mul_sq univ (fun x => G.degree x) (fun x => (B.filter (fun z => G.Adj x z)).card)

theorem edges_sq : (2*G.edgeFinset.card)^2 ≤ Fintype.card V*sig G := by
  have cs := sq_sum_le_card_mul_sum_sq (s:=(univ : Finset V)) (f:=fun v => G.degree v)
  rw [card_univ,G.sum_degrees_eq_twice_card_edges] at cs
  exact cs

/-- Turán inside common neighbourhoods. -/
theorem second_moment (Q : SimpleGraph V) (s K : ℕ) (hs : 0 < s) (cf : Q.CliqueFree (s+1))
    (light : ∀ z z', z ≠ z' → ¬Q.Adj z z' → (univ.filter (fun x => G.Adj x z ∧ G.Adj x z')).card ≤ K)
    (F : Finset V) :
    ∑ x, (F.filter (fun z => G.Adj x z)).card^2 ≤ s*(K*F.card^2+∑ z ∈ F, G.degree z) := by
  have per (x : V) : (F.filter (fun z => G.Adj x z)).card^2 ≤
      s*(((F.offDiag.filter (fun p => ¬Q.Adj p.1 p.2)).bipartiteAbove
        (fun x p => G.Adj x p.1 ∧ G.Adj x p.2) x).card+(F.bipartiteAbove (fun x z => G.Adj x z) x).card) := by
    have tur := turan_pairs Q s cf (F.filter (fun z => G.Adj x z))
    have split := card_filter_add_card_filter_not (s:=(F.filter (fun z => G.Adj x z)).offDiag)
      (fun p => Q.Adj p.1 p.2)
    rw [offDiag_card] at split
    have eqL : (F.filter (fun z => G.Adj x z)).offDiag.filter (fun p => ¬Q.Adj p.1 p.2) =
        (F.offDiag.filter (fun p => ¬Q.Adj p.1 p.2)).bipartiteAbove
          (fun x p => G.Adj x p.1 ∧ G.Adj x p.2) x := by
      ext p
      simp only [mem_filter,mem_offDiag,bipartiteAbove]
      tauto
    have eqC : F.bipartiteAbove (fun x z => G.Adj x z) x = F.filter (fun z => G.Adj x z) := rfl
    rw [← eqL,eqC]
    have le : (F.filter (fun z => G.Adj x z)).card ≤ (F.filter (fun z => G.Adj x z)).card^2 :=
      Nat.le_self_pow (by norm_num) _
    have sq : (F.filter (fun z => G.Adj x z)).card*(F.filter (fun z => G.Adj x z)).card =
        (F.filter (fun z => G.Adj x z)).card^2 := (pow_two _).symm
    rw [sq] at split
    obtain ⟨s',rfl⟩ : ∃ s', s = s'+1 := ⟨s-1,by omega⟩
    simp only [Nat.add_sub_cancel] at tur
    generalize (F.filter (fun z => G.Adj x z)).card^2 = c2 at *
    generalize (F.filter (fun z => G.Adj x z)).card = c at *
    generalize ((F.filter (fun z => G.Adj x z)).offDiag.filter (fun p => Q.Adj p.1 p.2)).card = A at *
    generalize ((F.filter (fun z => G.Adj x z)).offDiag.filter (fun p => ¬Q.Adj p.1 p.2)).card = L at *
    have c2eq : c2 = A+L+c := by omega
    subst c2eq
    nlinarith
  have lightsum : ∑ x, ((F.offDiag.filter (fun p => ¬Q.Adj p.1 p.2)).bipartiteAbove
      (fun x p => G.Adj x p.1 ∧ G.Adj x p.2) x).card ≤ K*F.card^2 := by
    rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc _ ≤ ∑ _p ∈ F.offDiag.filter (fun p => ¬Q.Adj p.1 p.2), K := by
          apply sum_le_sum
          intro p hp
          obtain ⟨off,nq⟩ := mem_filter.mp hp
          exact light p.1 p.2 (mem_offDiag.mp off).2.2 nq
      _ = (F.offDiag.filter (fun p => ¬Q.Adj p.1 p.2)).card*K := by rw [sum_const,smul_eq_mul]
      _ ≤ F.card^2*K := by
          apply Nat.mul_le_mul_right
          apply (card_filter_le _ _).trans
          rw [offDiag_card,pow_two]
          exact Nat.sub_le _ _
      _ = _ := mul_comm _ _
  have degsum : ∑ x, (F.bipartiteAbove (fun x z => G.Adj x z) x).card ≤ ∑ z ∈ F, G.degree z := by
    rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    apply sum_le_sum
    intro z _
    rw [← G.card_neighborFinset_eq_degree]
    apply card_le_card
    intro x hx
    exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hx).2.symm
  calc _ ≤ ∑ x, s*(((F.offDiag.filter (fun p => ¬Q.Adj p.1 p.2)).bipartiteAbove
        (fun x p => G.Adj x p.1 ∧ G.Adj x p.2) x).card+(F.bipartiteAbove (fun x z => G.Adj x z) x).card) :=
        sum_le_sum fun x _ => per x
    _ = s*(∑ x, ((F.offDiag.filter (fun p => ¬Q.Adj p.1 p.2)).bipartiteAbove
        (fun x p => G.Adj x p.1 ∧ G.Adj x p.2) x).card+∑ x, (F.bipartiteAbove (fun x z => G.Adj x z) x).card) := by
        rw [← mul_sum,sum_add_distrib]
    _ ≤ _ := Nat.mul_le_mul_left s (Nat.add_le_add lightsum degsum)

/-- Vertices that pairwise have many common neighbours span K(r,t): choose the witnesses by Hall's theorem. -/
theorem embed (r t : ℕ) (f : Fin r → V) (inj : Function.Injective f)
    (heavy : ∀ i j : Fin r, i < j → r+t*(r*r) ≤ cod G (f i) (f j)) : Fat r t ⊑ G := by
  let C (x : {p : Fin r × Fin r // p.1 < p.2} × Fin t) : Finset V :=
    (G.neighborFinset (f x.1.1.1) ∩ G.neighborFinset (f x.1.1.2)) \ univ.image f
  have big (x) : Fintype.card ({p : Fin r × Fin r // p.1 < p.2} × Fin t) ≤ (C x).card := by
    have h1 : (univ.image f).card ≤ r := card_image_le.trans (by simp)
    have h2 := heavy _ _ x.1.2
    have h3 := le_card_sdiff (univ.image f) (G.neighborFinset (f x.1.1.1) ∩ G.neighborFinset (f x.1.1.2))
    have h4 : Fintype.card ({p : Fin r × Fin r // p.1 < p.2} × Fin t) ≤ t*(r*r) := by
      rw [Fintype.card_prod,Fintype.card_fin,mul_comm]
      apply Nat.mul_le_mul_left
      exact (Fintype.card_subtype_le _).trans (by simp)
    change _ ≤ ((G.neighborFinset (f x.1.1.1) ∩ G.neighborFinset (f x.1.1.2)) \ univ.image f).card
    unfold cod at h2
    omega
  have hall : ∀ T : Finset ({p : Fin r × Fin r // p.1 < p.2} × Fin t), T.card ≤ (T.biUnion C).card := by
    intro T
    rcases T.eq_empty_or_nonempty with rfl | ⟨x,hx⟩
    · simp
    · exact (card_le_univ T).trans ((big x).trans (card_le_card (subset_biUnion_of_mem C hx)))
  obtain ⟨g,ginj,gmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective C).mp hall
  have fresh (x) (i : Fin r) : f i ≠ g x := by
    intro e
    have h := (mem_sdiff.mp (gmem x)).2
    exact h (mem_image.mpr ⟨i,mem_univ _,e⟩)
  have left (x) : G.Adj (f x.1.1.1) (g x) :=
    (G.mem_neighborFinset _ _).mp (mem_inter.mp (mem_sdiff.mp (gmem x)).1).1
  have right (x) : G.Adj (f x.1.1.2) (g x) :=
    (G.mem_neighborFinset _ _).mp (mem_inter.mp (mem_sdiff.mp (gmem x)).1).2
  have edge (a b : Fin r ⊕ ({p : Fin r × Fin r // p.1 < p.2} × Fin t))
      (h : ∃ i p k, a = Sum.inl i ∧ b = Sum.inr (p,k) ∧ (i = p.1.1 ∨ i = p.1.2)) :
      G.Adj (Sum.elim f g a) (Sum.elim f g b) := by
    obtain ⟨i,p,k,rfl,rfl,hi | hi⟩ := h
    · rw [hi]
      exact left (p,k)
    · rw [hi]
      exact right (p,k)
  refine ⟨⟨⟨Sum.elim f g,?_⟩,?_⟩⟩
  · intro a b h
    rcases ((SimpleGraph.fromRel_adj _ a b).mp h).2 with h | h
    · exact edge a b h
    · exact (edge b a h).symm
  · rintro (i|x) (j|y) e
    · exact congrArg Sum.inl (inj e)
    · exact (fresh y i e).elim
    · exact (fresh x j e.symm).elim
    · exact congrArg Sum.inr (ginj e)

/-- The second moment of the codegrees in a graph without K(r,t). -/
theorem moment (r t : ℕ) (hr : 2 ≤ r) (free : (Fat r t).Free G) :
    ∑ v, ∑ u, cod G u v^2 ≤ (r-1)*(r+t*(r*r))*sig G := by
  let Q : SimpleGraph V := SimpleGraph.fromRel (fun z z' => r+t*(r*r) ≤ cod G z z')
  have cf : Q.CliqueFree (r-1+1) := by
    rw [Nat.sub_add_cancel (by omega)]
    intro S hS
    apply free
    let f (i : Fin r) : V := ((Finset.equivFinOfCardEq hS.card_eq).symm i : V)
    have inj : Function.Injective f := fun i j h =>
      (Finset.equivFinOfCardEq hS.card_eq).symm.injective (Subtype.ext h)
    apply embed G r t f inj
    intro i j lt
    have adj : Q.Adj (f i) (f j) :=
      hS.isClique ((Finset.equivFinOfCardEq hS.card_eq).symm i).2
        ((Finset.equivFinOfCardEq hS.card_eq).symm j).2 (fun h => lt.ne (inj h))
    rcases ((SimpleGraph.fromRel_adj _ _ _).mp adj).2 with h | h
    · exact h
    · rwa [cod_comm] at h
  have light : ∀ z z', z ≠ z' → ¬Q.Adj z z' →
      (univ.filter (fun x => G.Adj x z ∧ G.Adj x z')).card ≤ r+t*(r*r)-1 := by
    intro z z' ne nq
    have eq : univ.filter (fun x => G.Adj x z ∧ G.Adj x z') = G.neighborFinset z ∩ G.neighborFinset z' := by
      ext x
      simp only [mem_filter,mem_univ,true_and,mem_inter,mem_neighborFinset]
      exact ⟨fun h => ⟨h.1.symm,h.2.symm⟩,fun h => ⟨h.1.symm,h.2.symm⟩⟩
    rw [eq]
    by_contra big
    exact nq ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨ne,Or.inl (by unfold cod; omega)⟩)
  have per (v : V) : ∑ u, cod G u v^2 ≤
      (r-1)*((r+t*(r*r)-1)*G.degree v^2+∑ z ∈ G.neighborFinset v, G.degree z) := by
    have h := second_moment G Q (r-1) (r+t*(r*r)-1) (by omega) cf light (G.neighborFinset v)
    rw [G.card_neighborFinset_eq_degree] at h
    refine le_trans (le_of_eq ?_) h
    apply sum_congr rfl
    intro u _
    rw [cod_eq]
  calc _ ≤ ∑ v, (r-1)*((r+t*(r*r)-1)*G.degree v^2+∑ z ∈ G.neighborFinset v, G.degree z) :=
        sum_le_sum fun v _ => per v
    _ = (r-1)*((r+t*(r*r)-1)*sig G+sig G) := by
        rw [← mul_sum,sum_add_distrib,← mul_sum,walks_total]
        rfl
    _ = _ := by
        obtain ⟨k,hk⟩ : ∃ k, r+t*(r*r) = k+1 := ⟨r+t*(r*r)-1,by omega⟩
        rw [hk,Nat.add_sub_cancel]
        ring

/-- The squared degrees sum to O(n^2) in a graph without K(r,t). -/
theorem sig_le (r t : ℕ) (hr : 2 ≤ r) (free : (Fat r t).Free G) :
    sig G ≤ (r-1)*(r+t*(r*r))*(Fintype.card V)^2 := by
  have m := moment G r t hr free
  have inner (v : V) : (∑ u, cod G u v)^2 ≤ Fintype.card V*∑ u, cod G u v^2 := by
    have cs := sq_sum_le_card_mul_sum_sq (s:=(univ : Finset V)) (f:=fun u => cod G u v)
    rwa [card_univ] at cs
  have outer : (sig G)^2 ≤ Fintype.card V*∑ v, (∑ u, cod G u v)^2 := by
    have cs := sq_sum_le_card_mul_sum_sq (s:=(univ : Finset V)) (f:=fun v => ∑ u, cod G u v)
    rwa [card_univ,← sig_eq] at cs
  have chain : (sig G)^2 ≤ (r-1)*(r+t*(r*r))*(Fintype.card V)^2*sig G := by
    calc (sig G)^2 ≤ Fintype.card V*∑ v, (∑ u, cod G u v)^2 := outer
      _ ≤ Fintype.card V*∑ v, Fintype.card V*∑ u, cod G u v^2 :=
          Nat.mul_le_mul_left _ (sum_le_sum fun v _ => inner v)
      _ = (Fintype.card V)^2*∑ v, ∑ u, cod G u v^2 := by rw [← mul_sum]; ring
      _ ≤ (Fintype.card V)^2*((r-1)*(r+t*(r*r))*sig G) := Nat.mul_le_mul_left _ m
      _ = _ := by ring
  rcases Nat.eq_zero_or_pos (sig G) with z | pos
  · rw [z]; exact Nat.zero_le _
  · rw [pow_two] at chain
    exact Nat.le_of_mul_le_mul_right chain pos

/-- In a set B some vertex has many partners of medium codegree, unless the codegree sum is small. -/
theorem dense (t K δ M : ℕ) (maxdeg : ∀ z, G.degree z ≤ δ) (hM : ∑ v, ∑ u, cod G u v^2 ≤ M)
    (B : Finset V) (hB : B.Nonempty) :
    ∃ v ∈ B, K*∑ v ∈ B, ∑ u ∈ B, cod G u v ≤ B.card*(K*δ)+B.card*(B.card*(K*(t-1)))+M+
      K*K*(B.card*(B.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card) := by
  obtain ⟨v,hv,best⟩ := exists_max_image B
    (fun v => (B.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card) hB
  refine ⟨v,hv,?_⟩
  have row (w : V) (hw : w ∈ B) : ∑ u ∈ B, K*cod G u w ≤ K*δ+B.card*(K*(t-1))+∑ u ∈ B, cod G u w^2+
      (B.filter (fun u => u ≠ w ∧ t ≤ cod G u w ∧ cod G u w ≤ K)).card*(K*K) := by
    have point (u : V) : K*cod G u w ≤ (if u = w then K*δ else 0)+K*(t-1)+cod G u w^2+
        (if u ≠ w ∧ t ≤ cod G u w ∧ cod G u w ≤ K then K*K else 0) := by
      by_cases e : u = w
      · subst e
        rw [if_pos rfl,cod_self]
        exact (Nat.mul_le_mul_left K (maxdeg u)).trans (by omega)
      · rw [if_neg e]
        by_cases lo : t ≤ cod G u w
        · by_cases hi : cod G u w ≤ K
          · rw [if_pos ⟨e,lo,hi⟩]
            exact (Nat.mul_le_mul_left K hi).trans (by omega)
          · rw [if_neg (fun h => hi h.2.2)]
            have : K*cod G u w ≤ cod G u w^2 := by
              rw [pow_two]
              exact Nat.mul_le_mul_right _ (by omega)
            omega
        · rw [if_neg (fun h => lo h.2.1)]
          have : K*cod G u w ≤ K*(t-1) := Nat.mul_le_mul_left K (by omega)
          omega
    have diag : ∑ u ∈ B, (if u = w then K*δ else 0) ≤ K*δ := by
      rw [sum_ite,sum_const_zero,add_zero,sum_const,smul_eq_mul]
      have one : (B.filter (fun u => u = w)).card ≤ 1 :=
        card_le_one.mpr (fun a ha b hb => (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
      calc _ ≤ 1*(K*δ) := Nat.mul_le_mul_right _ one
        _ = _ := one_mul _
    have med : ∑ u ∈ B, (if u ≠ w ∧ t ≤ cod G u w ∧ cod G u w ≤ K then K*K else 0) =
        (B.filter (fun u => u ≠ w ∧ t ≤ cod G u w ∧ cod G u w ≤ K)).card*(K*K) := by
      rw [sum_ite,sum_const_zero,add_zero,sum_const,smul_eq_mul]
    calc _ ≤ ∑ u ∈ B, ((if u = w then K*δ else 0)+K*(t-1)+cod G u w^2+
          (if u ≠ w ∧ t ≤ cod G u w ∧ cod G u w ≤ K then K*K else 0)) := sum_le_sum fun u _ => point u
      _ = ∑ u ∈ B, (if u = w then K*δ else 0)+B.card*(K*(t-1))+∑ u ∈ B, cod G u w^2+
          (B.filter (fun u => u ≠ w ∧ t ≤ cod G u w ∧ cod G u w ≤ K)).card*(K*K) := by
          rw [sum_add_distrib,sum_add_distrib,sum_add_distrib,med,sum_const,smul_eq_mul]
      _ ≤ _ := by omega
  have sq : ∑ w ∈ B, ∑ u ∈ B, cod G u w^2 ≤ M := by
    refine le_trans ?_ hM
    calc _ ≤ ∑ w ∈ B, ∑ u, cod G u w^2 :=
          sum_le_sum fun w _ => sum_le_sum_of_subset (subset_univ B)
      _ ≤ _ := sum_le_sum_of_subset (subset_univ B)
  calc K*∑ w ∈ B, ∑ u ∈ B, cod G u w = ∑ w ∈ B, ∑ u ∈ B, K*cod G u w := by
        rw [mul_sum]
        exact sum_congr rfl fun w _ => mul_sum _ _ _
    _ ≤ ∑ w ∈ B, (K*δ+B.card*(K*(t-1))+∑ u ∈ B, cod G u w^2+
          (B.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card*(K*K)) := by
        apply sum_le_sum
        intro w hw
        exact (row w hw).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (best w hw)) _)
    _ = B.card*(K*δ)+B.card*(B.card*(K*(t-1)))+∑ w ∈ B, ∑ u ∈ B, cod G u w^2+
          B.card*((B.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card*(K*K)) := by
        rw [sum_add_distrib,sum_add_distrib,sum_add_distrib,sum_const,sum_const,sum_const]
        simp only [smul_eq_mul]
    _ ≤ _ := by
        have e : B.card*((B.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card*(K*K)) =
            K*K*(B.card*(B.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card) := by ring
        omega

/-- The greedy choice of j main vertices inside a set A₀ with hereditary excess. -/
theorem greedy (r t Cm : ℕ) (ht : 1 ≤ t) (η Λ g : ℝ) (hη : 0 < η) (hΛ : 0 < Λ) (hg : 0 < g)
    (j : ℕ) (hj : j ≤ r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ Bd n0 : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      n0 ≤ Fintype.card V →
      (∀ z, (G.degree z : ℝ) ≤ Λ*Real.sqrt (Fintype.card V)) →
      ∑ v, ∑ u, cod G u v^2 ≤ Cm*(Fintype.card V)^2 →
      ∀ A₀ : Finset V,
        (∀ B, B ⊆ A₀ → ((t:ℝ)-1+η)*(B.card:ℝ)^2 ≤ ((∑ v ∈ B, ∑ u ∈ B, cod G u v : ℕ) : ℝ)) →
        g*(Fintype.card V : ℝ) ≤ A₀.card →
        ∃ S A : Finset V, S.card = j ∧ A ⊆ A₀ ∧ Inv G t Bd S A ∧ ρ*(Fintype.card V : ℝ) ≤ A.card := by
  induction j with
  | zero =>
    refine ⟨g,hg,0,0,?_⟩
    intro V _ G _ _ _ A₀ _ big
    refine ⟨∅,A₀,rfl,Subset.refl _,?_,big⟩
    refine ⟨by simp,by simp,by simp,?_,?_⟩
    · intro a _
      exact ⟨notMem_empty a,by simp⟩
    · intro a _ x _
      simp
  | succ j ih =>
    obtain ⟨ρ,hρ,Bd,n0,H⟩ := ih (by omega)
    let K : ℕ := max Bd (max t ⌈8*(Cm:ℝ)/(η*ρ^2)⌉₊)+1
    have KB : Bd ≤ K := (le_max_left _ _).trans (Nat.le_succ _)
    have K1 : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K from Nat.succ_le_succ (Nat.zero_le _))
    have Kpos : (0:ℝ) < K := by linarith
    have KC : 8*(Cm:ℝ)/(η*ρ^2) ≤ K := by
      have hc : ⌈8*(Cm:ℝ)/(η*ρ^2)⌉₊ ≤ K :=
        ((le_max_right t _).trans (le_max_right Bd _)).trans (Nat.le_succ _)
      exact (Nat.le_ceil _).trans (by exact_mod_cast hc)
    have BK : (Bd:ℝ) ≤ K := by exact_mod_cast KB
    let T : ℝ := 4*K*(1+r*K)*Λ/(η*ρ)
    have T0 : 0 ≤ T := by positivity
    refine ⟨η*ρ/(4*K),by positivity,K,max (max n0 1) ⌈T^2⌉₊,?_⟩
    intro V _ G hn cap mom A₀ her big
    have hn0 : n0 ≤ Fintype.card V := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
    have n1 : 1 ≤ Fintype.card V := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
    have nT : T^2 ≤ (Fintype.card V : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
    obtain ⟨S,A,hS,hA,inv,large⟩ := H V G hn0 cap mom A₀ her big
    have npos : (0:ℝ) < Fintype.card V := by exact_mod_cast n1
    have s2 : Real.sqrt (Fintype.card V)^2 = Fintype.card V := Real.sq_sqrt npos.le
    have spos : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.mpr npos
    have sT : T ≤ Real.sqrt (Fintype.card V) := by
      have h := Real.sqrt_le_sqrt nT
      rwa [Real.sqrt_sq T0] at h
    have star : 4*K*(1+r*K)*Λ ≤ η*ρ*Real.sqrt (Fintype.card V) := by
      have h := (div_le_iff₀ (by positivity : 0 < η*ρ)).mp sT
      linarith
    have maxdeg : ∀ z, G.degree z ≤ ⌊Λ*Real.sqrt (Fintype.card V)⌋₊ := fun z => Nat.le_floor (cap z)
    have δle : (⌊Λ*Real.sqrt (Fintype.card V)⌋₊ : ℝ) ≤ Λ*Real.sqrt (Fintype.card V) :=
      Nat.floor_le (by positivity)
    have apos : (0:ℝ) < A.card := lt_of_lt_of_le (by positivity) large
    have Ane : A.Nonempty := card_pos.mp (by exact_mod_cast apos)
    obtain ⟨v,hv,key⟩ := dense G t K ⌊Λ*Real.sqrt (Fintype.card V)⌋₊ (Cm*(Fintype.card V)^2) maxdeg mom A Ane
    obtain ⟨A',sub,inv',cnt⟩ := extend G t Bd K ⌊Λ*Real.sqrt (Fintype.card V)⌋₊ S A inv maxdeg v hv KB
    refine ⟨insert v S,A',?_,sub.trans hA,inv',?_⟩
    · rw [card_insert_of_notMem (inv.2.2.2.1 v hv).1,hS]
    have herA := her A hA
    have keyR := (Nat.cast_le (α:=ℝ)).mpr key
    have cntR := (Nat.cast_le (α:=ℝ)).mpr cnt
    rw [hS] at cntR
    push_cast [Nat.cast_sub ht] at herA keyR cntR
    have p0 : (0:ℝ) ≤ ((A.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card : ℝ) :=
      Nat.cast_nonneg _
    have d0 : (0:ℝ) ≤ (⌊Λ*Real.sqrt (Fintype.card V)⌋₊ : ℝ) := Nat.cast_nonneg _
    have jr : (j:ℝ)+1 ≤ r := by exact_mod_cast hj
    have j0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have r0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
    have B0 : (0:ℝ) ≤ Bd := Nat.cast_nonneg Bd
    have C0 : (0:ℝ) ≤ Cm := Nat.cast_nonneg Cm
    have KC' : 8*(Cm:ℝ) ≤ K*(η*ρ^2) := (div_le_iff₀ (by positivity)).mp KC
    generalize (∑ v ∈ A, ∑ u ∈ A, (cod G u v : ℝ)) = W at herA keyR
    generalize ((A.filter (fun u => u ≠ v ∧ t ≤ cod G u v ∧ cod G u v ≤ K)).card : ℝ) = p at keyR cntR p0
    generalize (⌊Λ*Real.sqrt (Fintype.card V)⌋₊ : ℝ) = d at δle keyR cntR d0
    generalize (A.card : ℝ) = a at herA keyR large apos
    generalize (A'.card : ℝ) = a' at cntR ⊢
    rw [← s2] at large keyR ⊢
    generalize Real.sqrt (Fintype.card V) = s at star δle large keyR spos ⊢
    generalize (K:ℝ) = k at K1 Kpos BK star keyR KC' ⊢
    have L1 : k*η*a^2 ≤ a*k*d+Cm*(s^2)^2+k*k*a*p := by
      linarith [mul_le_mul_of_nonneg_left herA Kpos.le]
    have h1 : 1 ≤ k*(1+r*k) := by
      linarith [mul_nonneg (mul_nonneg r0 Kpos.le) Kpos.le]
    have fourL : 4*Λ ≤ η*ρ*s := by
      linarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 4*Λ)]
    have h3 : η*(ρ*s^2) ≤ η*a := mul_le_mul_of_nonneg_left large hη.le
    have t1 : d ≤ η*a/4 := by
      have h2 : 4*Λ*s ≤ η*ρ*s*s := mul_le_mul_of_nonneg_right fourL spos.le
      linarith
    have t2 : Cm*(s^2)^2 ≤ k*η*a^2/8 := by
      have h4 : (ρ*s^2)^2 ≤ a^2 := pow_le_pow_left₀ (by positivity) large 2
      have h5 : 8*(Cm:ℝ)*(s^2)^2 ≤ k*(η*ρ^2)*(s^2)^2 := mul_le_mul_of_nonneg_right KC' (by positivity)
      have h6 : k*η*(ρ*s^2)^2 ≤ k*η*a^2 := mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
    have t1' : a*k*d ≤ k*η*a^2/4 := by
      have h := mul_le_mul_of_nonneg_left t1 (mul_nonneg apos.le Kpos.le)
      linarith
    have L2 : η*a/2 ≤ k*p := by
      by_contra neg
      push Not at neg
      have h := mul_lt_mul_of_pos_left neg (mul_pos Kpos apos)
      have pos : 0 < k*η*a^2 := by positivity
      linarith
    have t3 : 4*k*((1+j*Bd)*d) ≤ η*ρ*s^2 := by
      have h7 : 1+(j:ℝ)*Bd ≤ 1+r*k := by
        linarith [mul_le_mul (show (j:ℝ) ≤ r by linarith) BK B0 r0]
      have h8 : (1+(j:ℝ)*Bd)*d ≤ (1+r*k)*(Λ*s) := mul_le_mul h7 δle d0 (by positivity)
      have h9 : 4*k*(1+r*k)*Λ*s ≤ η*ρ*s*s := mul_le_mul_of_nonneg_right star spos.le
      linarith [mul_le_mul_of_nonneg_left h8 (by positivity : (0:ℝ) ≤ 4*k)]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_left cntR (by positivity : (0:ℝ) ≤ 4*k)]

/-- Graphs of maximum degree O(sqrt n) without K(r,t). -/
theorem capped (r t : ℕ) (hr : 2 ≤ r) (ht : 2 ≤ t) (ε Λ : ℝ) (hε : 0 < ε) (hΛ : 0 < Λ) :
    ∃ n0 : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), n0 ≤ Fintype.card V → (Fat r t).Free G →
      (∀ z, (G.degree z : ℝ) ≤ Λ*Real.sqrt (Fintype.card V)) →
      2*(G.edgeFinset.card : ℝ) ≤
        (1+ε)*Real.sqrt ((t:ℝ)-1)*((Fintype.card V : ℝ)*Real.sqrt (Fintype.card V)) := by
  have b1 : (1:ℝ) ≤ (t:ℝ)-1 := by
    have : (2:ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have bpos : (0:ℝ) < (t:ℝ)-1 := by linarith
  have sbpos := Real.sqrt_pos.mpr bpos
  have sb2 : Real.sqrt ((t:ℝ)-1)^2 = (t:ℝ)-1 := Real.sq_sqrt bpos.le
  have hη : 0 < ((1+ε/2)^2-1)*((t:ℝ)-1) := by
    apply mul_pos _ bpos
    nlinarith
  have hg : 0 < ε*((t:ℝ)-1)/(2*Λ^2) := by positivity
  obtain ⟨ρ,hρ,Bd,n0,H⟩ := greedy r t (((r-1)*(r+t*(r*r)))^2) (by omega) _ Λ _ hη hΛ hg r le_rfl
  refine ⟨max n0 1,?_⟩
  intro V _ G hn free cap
  by_contra big
  push Not at big
  have n1 : 1 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have npos : (0:ℝ) < Fintype.card V := by exact_mod_cast n1
  have s2 : Real.sqrt (Fintype.card V)^2 = Fintype.card V := Real.sq_sqrt npos.le
  have spos : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.mpr npos
  have SL := sig_le G r t hr free
  have mom : ∑ v, ∑ u, cod G u v^2 ≤ ((r-1)*(r+t*(r*r)))^2*(Fintype.card V)^2 := by
    calc _ ≤ (r-1)*(r+t*(r*r))*sig G := moment G r t hr free
      _ ≤ (r-1)*(r+t*(r*r))*((r-1)*(r+t*(r*r))*(Fintype.card V)^2) := Nat.mul_le_mul_left _ SL
      _ = _ := by ring
  have ER : (2*(G.edgeFinset.card:ℝ))^2 ≤ (Fintype.card V:ℝ)*(sig G:ℝ) := by exact_mod_cast edges_sq G
  have cap0 := cap
  have σ2 : Real.sqrt (sig G : ℝ)^2 = sig G := Real.sq_sqrt (Nat.cast_nonneg _)
  have σ0 : 0 ≤ Real.sqrt (sig G : ℝ) := Real.sqrt_nonneg _
  have total : ∑ v, ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ) = (sig G : ℝ) := by
    have h := congrArg (Nat.cast (R:=ℝ)) (walks_total G)
    push_cast at h
    exact h
  have degcard (v : V) : ((G.neighborFinset v).card : ℝ) = G.degree v := by
    rw [G.card_neighborFinset_eq_degree]
  generalize Real.sqrt (Fintype.card V : ℝ) = s at s2 spos cap big
  generalize Real.sqrt ((t:ℝ)-1) = sb at sbpos sb2 big
  generalize Real.sqrt (sig G : ℝ) = σ at σ2 σ0
  have sig_big : ((1+ε)*sb*(Fintype.card V:ℝ))^2 < (sig G : ℝ) := by
    have h := pow_lt_pow_left₀ big (by positivity) (two_ne_zero)
    have e : ((1+ε)*sb*((Fintype.card V:ℝ)*s))^2 =
        (Fintype.card V:ℝ)*((1+ε)*sb*(Fintype.card V:ℝ))^2 := by
      rw [← s2]
      ring
    rw [e] at h
    exact lt_of_mul_lt_mul_left (h.trans_le ER) npos.le
  have lo : (1+ε)*sb*(Fintype.card V:ℝ) < σ := by
    rw [← σ2] at sig_big
    exact lt_of_pow_lt_pow_left₀ 2 σ0 sig_big
  have σpos : 0 < σ := lt_of_le_of_lt (by positivity) lo
  have Sgpos : (0:ℝ) < sig G := by rw [← σ2]; positivity
  let Good : Finset V := univ.filter
    (fun v => (1+ε/2)*sb*σ ≤ ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ))
  have her : ∀ B, B ⊆ Good → ((t:ℝ)-1+((1+ε/2)^2-1)*((t:ℝ)-1))*(B.card:ℝ)^2 ≤
      ((∑ v ∈ B, ∑ u ∈ B, cod G u v : ℕ) : ℝ) := by
    intro B hB
    have hh : ((∑ v ∈ B, ∑ x ∈ G.neighborFinset v, G.degree x : ℕ) : ℝ)^2 ≤
        (sig G : ℝ)*((∑ v ∈ B, ∑ u ∈ B, cod G u v : ℕ) : ℝ) := by exact_mod_cast hereditary G B
    have low : (B.card:ℝ)*((1+ε/2)*sb*σ) ≤
        ((∑ v ∈ B, ∑ x ∈ G.neighborFinset v, G.degree x : ℕ) : ℝ) := by
      push_cast
      calc (B.card:ℝ)*((1+ε/2)*sb*σ) = ∑ _v ∈ B, (1+ε/2)*sb*σ := by rw [sum_const,nsmul_eq_mul]
        _ ≤ _ := sum_le_sum (fun v hv => (mem_filter.mp (hB hv)).2)
    have sq := pow_le_pow_left₀ (by positivity) low 2
    have e : ((B.card:ℝ)*((1+ε/2)*sb*σ))^2 =
        (sig G : ℝ)*(((t:ℝ)-1+((1+ε/2)^2-1)*((t:ℝ)-1))*(B.card:ℝ)^2) := by
      rw [← σ2,← sb2]
      ring
    rw [e] at sq
    exact le_of_mul_le_mul_left (sq.trans hh) Sgpos
  have bigGood : ε*((t:ℝ)-1)/(2*Λ^2)*(Fintype.card V : ℝ) ≤ Good.card := by
    have up (v : V) : ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ) ≤ (Λ*s)^2 := by
      calc _ ≤ ∑ _x ∈ G.neighborFinset v, Λ*s := sum_le_sum fun x _ => cap x
        _ = (G.degree v : ℝ)*(Λ*s) := by rw [sum_const,nsmul_eq_mul,degcard]
        _ ≤ (Λ*s)*(Λ*s) := mul_le_mul_of_nonneg_right (cap v) (by positivity)
        _ = _ := (pow_two _).symm
    have split := sum_filter_add_sum_filter_not (univ : Finset V)
      (fun v => (1+ε/2)*sb*σ ≤ ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ))
      (fun v => ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ))
    rw [total] at split
    have part1 : ∑ v ∈ Good, ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ) ≤ (Good.card:ℝ)*(Λ*s)^2 := by
      have h := sum_le_card_nsmul Good (fun v => ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ)) ((Λ*s)^2)
        (fun v _ => up v)
      rwa [nsmul_eq_mul] at h
    have part2 : ∑ v ∈ univ.filter
        (fun v => ¬ ((1+ε/2)*sb*σ ≤ ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ))),
        ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ) ≤ (Fintype.card V : ℝ)*((1+ε/2)*sb*σ) := by
      have h := sum_le_card_nsmul (univ.filter
        (fun v => ¬ ((1+ε/2)*sb*σ ≤ ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ))))
        (fun v => ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ)) ((1+ε/2)*sb*σ)
        (fun v hv => (not_le.mp (mem_filter.mp hv).2).le)
      rw [nsmul_eq_mul] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact_mod_cast (card_filter_le _ _).trans (le_of_eq card_univ)
    have main : (sig G : ℝ) ≤ (Good.card:ℝ)*(Λ*s)^2+(Fintype.card V : ℝ)*((1+ε/2)*sb*σ) := by
      rw [← split]
      exact add_le_add part1 part2
    have a1 : σ*((ε/2)*sb*(Fintype.card V : ℝ)) ≤ σ*(σ-(1+ε/2)*sb*(Fintype.card V : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) σpos.le
    have a2 : ((1+ε)*sb*(Fintype.card V : ℝ))*((ε/2)*sb*(Fintype.card V : ℝ)) ≤
        σ*((ε/2)*sb*(Fintype.card V : ℝ)) := mul_le_mul_of_nonneg_right lo.le (by positivity)
    have a3 : (0:ℝ) ≤ ε*(ε/2)*sb^2*(Fintype.card V : ℝ)^2 := by positivity
    have a4 : (Fintype.card V : ℝ)*((ε/2)*((t:ℝ)-1)*(Fintype.card V : ℝ)) ≤
        (Fintype.card V : ℝ)*((Good.card:ℝ)*Λ^2) := by
      rw [← sb2]
      have e : (Good.card:ℝ)*(Λ*s)^2 = (Fintype.card V : ℝ)*((Good.card:ℝ)*Λ^2) := by
        rw [← s2]
        ring
      rw [e,← σ2] at main
      linarith
    have a5 := le_of_mul_le_mul_left a4 npos
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨S,A,hS,-,inv,-⟩ := H V G ((le_max_left _ _).trans hn) cap0 mom Good her bigGood
  exact free (embed2 G r t S hS inv.1 inv.2.1 inv.2.2.1)

/-- The general case: delete the edges at vertices of degree above Λ sqrt(n). -/
theorem upper (r t : ℕ) (hr : 2 ≤ r) (ht : 2 ≤ t) (ε : ℝ) (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), n0 ≤ Fintype.card V → (Fat r t).Free G →
      2*(G.edgeFinset.card : ℝ) ≤
        (1+ε)*Real.sqrt ((t:ℝ)-1)*((Fintype.card V : ℝ)*Real.sqrt (Fintype.card V)) := by
  have bpos : (0:ℝ) < (t:ℝ)-1 := by
    have : (2:ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have sbpos := Real.sqrt_pos.mpr bpos
  obtain ⟨c,hc⟩ : ∃ c : ℝ, c = (((r-1)*(r+t*(r*r)) : ℕ) : ℝ) := ⟨_,rfl⟩
  have c0 : 0 ≤ c := by rw [hc]; exact Nat.cast_nonneg _
  obtain ⟨Λ,hΛdef⟩ : ∃ Λ : ℝ, Λ = 4*c/(ε*Real.sqrt ((t:ℝ)-1))+1 := ⟨_,rfl⟩
  have hΛ : 0 < Λ := by rw [hΛdef]; positivity
  have Λc : 4*c ≤ Λ*(ε*Real.sqrt ((t:ℝ)-1)) := by
    have h : 4*c/(ε*Real.sqrt ((t:ℝ)-1)) ≤ Λ := by rw [hΛdef]; linarith
    exact (div_le_iff₀ (by positivity)).mp h
  obtain ⟨n0,H⟩ := capped r t hr ht (ε/2) Λ (by positivity) hΛ
  refine ⟨max n0 1,?_⟩
  intro V _ G hn free
  have n1 : 1 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have npos : (0:ℝ) < Fintype.card V := by exact_mod_cast n1
  obtain ⟨s,hs⟩ : ∃ s : ℝ, s = Real.sqrt (Fintype.card V) := ⟨_,rfl⟩
  have s2 : s^2 = Fintype.card V := by rw [hs]; exact Real.sq_sqrt npos.le
  have spos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr npos
  rw [← hs]
  obtain ⟨G',hG'⟩ : ∃ G' : SimpleGraph V, ∀ u w, G'.Adj u w ↔
      (G.Adj u w ∧ (G.degree u : ℝ) ≤ Λ*s ∧ (G.degree w : ℝ) ≤ Λ*s) :=
    ⟨{ Adj := fun u w => G.Adj u w ∧ (G.degree u : ℝ) ≤ Λ*s ∧ (G.degree w : ℝ) ≤ Λ*s
       symm := ⟨fun u w h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
       loopless := ⟨fun u h => G.irrefl h.1⟩ },fun _ _ => Iff.rfl⟩
  have le : G' ≤ G := fun u w h => ((hG' u w).mp h).1
  have free' : (Fat r t).Free G' := fun h => free (h.trans (IsContained.of_le le))
  have cap' : ∀ z, (G'.degree z : ℝ) ≤ Λ*s := by
    intro z
    by_cases hz : (G.degree z : ℝ) ≤ Λ*s
    · refine le_trans ?_ hz
      have sub : G'.neighborFinset z ⊆ G.neighborFinset z := by
        intro w hw
        exact (G.mem_neighborFinset _ _).mpr ((hG' _ _).mp ((G'.mem_neighborFinset _ _).mp hw)).1
      have h := card_le_card sub
      rw [G'.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree] at h
      exact_mod_cast h
    · have zero : G'.degree z = 0 := by
        rw [← G'.card_neighborFinset_eq_degree,card_eq_zero]
        apply eq_empty_of_forall_notMem
        intro w hw
        exact hz ((hG' _ _).mp ((G'.mem_neighborFinset _ _).mp hw)).2.1
      rw [zero]
      simpa using (by positivity : 0 ≤ Λ*s)
  have main := H V G' ((le_max_left _ _).trans hn) free' (by rw [← hs]; exact cap')
  rw [← hs] at main
  let Hi : Finset V := univ.filter (fun x => ¬ ((G.degree x : ℝ) ≤ Λ*s))
  have cover : G.edgeFinset ⊆ G'.edgeFinset ∪ Hi.biUnion (fun x => G.incidenceFinset x) := by
    intro e
    induction e using Sym2.ind with
    | _ u w =>
      intro he
      have adj : G.Adj u w := G.mem_edgeFinset.mp he
      by_cases hu : (G.degree u : ℝ) ≤ Λ*s
      · by_cases hw : (G.degree w : ℝ) ≤ Λ*s
        · exact mem_union_left _ (G'.mem_edgeFinset.mpr ((hG' u w).mpr ⟨adj,hu,hw⟩))
        · refine mem_union_right _ (mem_biUnion.mpr ⟨w,mem_filter.mpr ⟨mem_univ _,hw⟩,?_⟩)
          rw [SimpleGraph.mem_incidenceFinset]
          exact G.mk'_mem_incidenceSet_iff.mpr ⟨adj,Or.inr rfl⟩
      · refine mem_union_right _ (mem_biUnion.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hu⟩,?_⟩)
        rw [SimpleGraph.mem_incidenceFinset]
        exact G.mk'_mem_incidenceSet_iff.mpr ⟨adj,Or.inl rfl⟩
  have count : G.edgeFinset.card ≤ G'.edgeFinset.card+∑ x ∈ Hi, G.degree x := by
    refine (card_le_card cover).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
    refine card_biUnion_le.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
    rw [G.card_incidenceFinset_eq_degree]
  have hi : (Λ*s)*(∑ x ∈ Hi, (G.degree x : ℝ)) ≤ (sig G : ℝ) := by
    rw [mul_sum]
    calc _ ≤ ∑ x ∈ Hi, (G.degree x : ℝ)^2 := sum_le_sum (fun x hx => by
            have h := (not_le.mp (mem_filter.mp hx).2).le
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))
      _ ≤ ∑ x, (G.degree x : ℝ)^2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
      _ = (sig G : ℝ) := by
          unfold sig
          push_cast
          rfl
  have SL : (sig G : ℝ) ≤ c*(Fintype.card V : ℝ)^2 := by
    rw [hc]
    exact_mod_cast sig_le G r t hr free
  have countR : (G.edgeFinset.card : ℝ) ≤ G'.edgeFinset.card+∑ x ∈ Hi, (G.degree x : ℝ) := by
    exact_mod_cast count
  have D0 : (0:ℝ) ≤ ∑ x ∈ Hi, (G.degree x : ℝ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  generalize (∑ x ∈ Hi, (G.degree x : ℝ)) = D at hi countR D0
  generalize (G'.edgeFinset.card : ℝ) = e' at main countR
  have e1 : c*(Fintype.card V : ℝ)^2 = s*(c*(Fintype.card V : ℝ)*s) := by
    rw [← s2]
    ring
  have h1 : s*(Λ*D) ≤ s*(c*(Fintype.card V : ℝ)*s) := by linarith
  have h2 := le_of_mul_le_mul_left h1 spos
  have h3 : Λ*(4*D) ≤ Λ*(ε*Real.sqrt ((t:ℝ)-1)*((Fintype.card V : ℝ)*s)) := by
    have h := mul_le_mul_of_nonneg_right Λc (by positivity : 0 ≤ (Fintype.card V : ℝ)*s)
    linarith
  have h4 := le_of_mul_le_mul_left h3 hΛ
  linarith

theorem half (x A B C : ℝ) (h : 2*x ≤ A*B*C) : x ≤ A*(B/2)*C := by linarith

end E713D

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro r t hr ht ε hε
  obtain ⟨n0,H⟩ := E713D.upper r t hr ht ε hε
  filter_upwards [eventually_ge_atTop (max n0 1)] with n hn
  have n1 : 1 ≤ n := (le_max_right _ _).trans hn
  have npos : (0:ℝ) < n := by exact_mod_cast n1
  have bpos : (0:ℝ) < (t:ℝ)-1 := by
    have : (2:ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have power : (n:ℝ)^(3/2:ℝ) = n*Real.sqrt n := by
    rw [show (3/2:ℝ) = 1+(1/2:ℝ) by norm_num,Real.rpow_add npos,Real.rpow_one,← Real.sqrt_eq_rpow]
  have key : (extremalNumber (Fintype.card (Fin n)) (E713D.Fat r t) : ℝ) ≤
      (1+ε)*(Real.sqrt ((t:ℝ)-1)/2)*((n:ℝ)*Real.sqrt n) := by
    rw [extremalNumber_le_iff_of_nonneg _ (by positivity)]
    intro G inst free
    have h := H (Fin n) G (by rw [Fintype.card_fin]; exact (le_max_left _ _).trans hn) free
    simp only [Fintype.card_fin] at h
    have h3 := E713D.half _ _ _ _ h
    convert! h3 using 1
    congr!
  rw [Fintype.card_fin] at key
  rw [power]
  exact key
