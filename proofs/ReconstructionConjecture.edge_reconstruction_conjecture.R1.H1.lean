import OMAReductions.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1

/-!
# Step H1 of the reduction ReconstructionConjecture.edge_reconstruction_conjecture.R1

Reduction of the edge reconstruction conjecture (for graphs with at least 4 edges) to
connected, isolate-free, doubly-hypomorphic (both EdgeHypomorphic and Hypomorphic) pairs,
following Kelly (1957), Greenwell-Hemminger (1969), and Greenwell (1971).

Proof outline:
1. General Edge-Kelly lemma for any isomorphism-invariant predicate on spanning subgraphs
   of a fixed edge count strictly less than m.
2. Star case (a vertex of degree m) is directly edge-reconstructible for m >= 4; otherwise
   counting k-stars via Edge-Kelly and downward binomial inversion shows G and H have the
   same degree multiset, and in particular the same number of isolated vertices.
3. Stripping isolated vertices yields isolate-free graphs G' and H' on W with 4 <= |W|,
   4 <= |E(G')|, EdgeHypomorphic G' H', and an isomorphism lift back to G and H.
4. If G' is disconnected, then H' is also disconnected (using cycle-edge deletion and
   the forest edge bound), and downward induction on component edge counts via Edge-Kelly
   matches connected components class by class to prove Nonempty (G' ≃g H').
5. If G' is connected, Greenwell's theorem (double-counting spanning subgraphs isomorphic
   to X plus an isolated vertex, combined with Edge-Kelly and downward induction on |E(X)|)
   shows Hypomorphic G' H'.
-/

namespace OMA.H1Proof

open SimpleGraph ReconstructionConjecture Finset
open Classical

noncomputable section

section BasicHelpers

private lemma ncard_edgeSet_eq_card_edgeFinset {V : Type} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]

private lemma four_le_card_of_four_le_edgeFinset {V : Type} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (hE : 4 ≤ G.edgeFinset.card) : 4 ≤ Fintype.card V := by
  have hle : 4 ≤ (Fintype.card V).choose 2 := hE.trans G.card_edgeFinset_le_card_choose_two
  by_contra hlt
  have hlt' : Fintype.card V < 4 := Nat.lt_of_not_le hlt
  interval_cases h : Fintype.card V <;> simp_all [Nat.choose]

private lemma edgeHypomorphic_symm {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : EdgeHypomorphic G H) : EdgeHypomorphic H G := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, fun e => ?_⟩
  obtain ⟨φ⟩ := hσ (σ.symm e)
  exact ⟨(by simpa using φ : G.deleteEdges {(σ.symm e).val} ≃g H.deleteEdges {e.val}).symm⟩

private lemma edgeFinset_card_eq_of_iso {U V : Type}
    {G : SimpleGraph U} {H : SimpleGraph V} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (φ : G ≃g H) :
    G.edgeFinset.card = H.edgeFinset.card := by
  rw [← G.card_edgeSet, ← H.card_edgeSet]
  exact Fintype.card_congr φ.mapEdgeSet

private lemma edgeFinset_card_eq_of_edgeHypomorphic {U V : Type}
    {G : SimpleGraph U} {H : SimpleGraph V} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (h : EdgeHypomorphic G H) :
    G.edgeFinset.card = H.edgeFinset.card := by
  obtain ⟨σ, _⟩ := h
  rw [← G.card_edgeSet, ← H.card_edgeSet]
  exact Fintype.card_congr σ

private lemma edgeSet_fromEdgeSet_of_subset {V : Type} {G : SimpleGraph V} [Fintype G.edgeSet]
    {T : Finset (Sym2 V)} (hT : T ⊆ G.edgeFinset) :
    (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).edgeSet = (T : Set (Sym2 V)) := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Finset.mem_coe, and_iff_left_iff_imp]
  intro he
  exact G.not_isDiag_of_mem_edgeSet ((G.mem_edgeFinset).mp (hT he))

private lemma edgeFinset_fromEdgeSet_of_subset {V : Type} {G : SimpleGraph V} [Fintype G.edgeSet]
    {T : Finset (Sym2 V)} [Fintype (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).edgeSet]
    (hT : T ⊆ G.edgeFinset) :
    (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).edgeFinset = T := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, edgeSet_fromEdgeSet_of_subset hT, Finset.mem_coe]

private lemma fromEdgeSet_edgeFinset_eq {V : Type} (G : SimpleGraph V) [Fintype G.edgeSet] :
    SimpleGraph.fromEdgeSet (G.edgeFinset : Set (Sym2 V)) = G := by
  rw [G.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]

private lemma fromEdgeSet_le_of_subset {V : Type} {G : SimpleGraph V} [Fintype G.edgeSet]
    {T : Finset (Sym2 V)} (hT : T ⊆ G.edgeFinset) :
    SimpleGraph.fromEdgeSet (T : Set (Sym2 V)) ≤ G := by
  intro a b hab
  rw [SimpleGraph.fromEdgeSet_adj] at hab
  exact (G.mem_edgeSet).mp ((G.mem_edgeFinset).mp (hT hab.1))

private def fromEdgeSet_image_iso {U V : Type} (e : U ≃ V) (T : Finset (Sym2 U)) :
    SimpleGraph.fromEdgeSet (T : Set (Sym2 U)) ≃g
      SimpleGraph.fromEdgeSet ((T.image (Sym2.map e) : Finset (Sym2 V)) : Set (Sym2 V)) where
  toEquiv := e
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, Finset.mem_image, ne_eq]
    constructor
    · rintro ⟨⟨x, hx, hxe⟩, hne⟩
      refine ⟨?_, fun h => hne (congrArg e h)⟩
      have hmap : Sym2.map e s(a, b) = Sym2.map e x := by
        rw [Sym2.map_mk, hxe]
      have hEq : s(a, b) = x := Sym2.map.injective e.injective hmap
      rwa [hEq]
    · rintro ⟨hab, hne⟩
      refine ⟨⟨s(a, b), hab, Sym2.map_mk _ _ _⟩, fun h => hne (e.injective h)⟩

private lemma edgeFinset_deleteEdges_singleton {V : Type} (G : SimpleGraph V)
    [Fintype G.edgeSet] (e : Sym2 V) [Fintype (G.deleteEdges {e}).edgeSet] :
    (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
  ext x
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
    Set.mem_singleton_iff, Finset.mem_erase, and_comm]

private lemma degree_eq_zero_iff_no_adj {V : Type} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    G.degree v = 0 ↔ ∀ u : V, ¬ G.Adj v u := by
  rw [← G.card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp only [SimpleGraph.mem_neighborFinset]

private lemma degree_pos_iff_exists_adj {V : Type} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    0 < G.degree v ↔ ∃ u : V, G.Adj v u := by
  rw [Nat.pos_iff_ne_zero, ne_eq, degree_eq_zero_iff_no_adj]
  push Not
  rfl

private def isoCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun v : V => ∀ u : V, ¬ G.Adj v u)).card

private lemma isoCount_eq_card_degree_zero {V : Type} [Fintype V] (G : SimpleGraph V)
    [∀ v, Fintype (G.neighborSet v)] :
    isoCount G = (Finset.univ.filter (fun v : V => G.degree v = 0)).card := by
  unfold isoCount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, degree_eq_zero_iff_no_adj]

private lemma isoCount_eq_of_iso {U V : Type} [Fintype U] [Fintype V]
    {G : SimpleGraph U} {H : SimpleGraph V} (φ : G ≃g H) :
    isoCount G = isoCount H := by
  unfold isoCount
  refine Finset.card_bij (fun v _ => φ v) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro w hadj
    have h1 : G.Adj v (φ.symm w) := by
      rw [← φ.map_rel_iff, φ.apply_symm_apply]
      exact hadj
    exact hv (φ.symm w) h1
  · intro v₁ _ v₂ _ h
    exact φ.injective h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro u hadj
    have h1 : H.Adj w (φ u) := by
      have := φ.map_rel_iff.mpr hadj
      rwa [φ.apply_symm_apply] at this
    exact hw (φ u) h1

private lemma degree_deleteEdges_singleton_of_adj {V : Type} [Fintype V] (G : SimpleGraph V)
    {u v : V} (hadj : G.Adj u v) (x : V) :
    (G.deleteEdges {s(u, v)}).degree x =
      if x = u ∨ x = v then G.degree x - 1 else G.degree x := by
  have hnf : (G.deleteEdges {s(u, v)}).neighborFinset x =
      if x = u then (G.neighborFinset u).erase v
      else if x = v then (G.neighborFinset v).erase u
      else G.neighborFinset x := by
    by_cases hxu : x = u
    · subst hxu
      rw [if_pos rfl]
      ext y
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
        Set.mem_singleton_iff, Finset.mem_erase, ne_eq]
      constructor
      · rintro ⟨hxy, hne⟩
        exact ⟨fun hy => hne (by rw [hy]), hxy⟩
      · rintro ⟨hy, hxy⟩
        refine ⟨hxy, fun h => ?_⟩
        rw [Sym2.eq_iff] at h
        rcases h with ⟨_, hyx⟩ | ⟨_, hyx⟩
        · exact hy hyx
        · exact hxy.ne hyx.symm
    · rw [if_neg hxu]
      by_cases hxv : x = v
      · subst hxv
        rw [if_pos rfl]
        ext y
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
          Set.mem_singleton_iff, Finset.mem_erase, ne_eq]
        constructor
        · rintro ⟨hxy, hne⟩
          exact ⟨fun hy => hne (by rw [hy, Sym2.eq_swap]), hxy⟩
        · rintro ⟨hy, hxy⟩
          refine ⟨hxy, fun h => ?_⟩
          rw [Sym2.eq_iff] at h
          rcases h with ⟨hvu, _⟩ | ⟨_, hyu⟩
          · exact hxu hvu
          · exact hy hyu
      · rw [if_neg hxv]
        ext y
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
          Set.mem_singleton_iff]
        constructor
        · exact fun h => h.1
        · intro hxy
          refine ⟨hxy, fun h => ?_⟩
          rw [Sym2.eq_iff] at h
          rcases h with ⟨hx, _⟩ | ⟨hx, _⟩
          · exact hxu hx
          · exact hxv hx
  have hmemu : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hadj
  have hmemv : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hadj.symm
  rw [SimpleGraph.degree, hnf]
  by_cases hxu : x = u
  · subst hxu
    rw [if_pos rfl, if_pos (Or.inl rfl), Finset.card_erase_of_mem hmemu,
      G.card_neighborFinset_eq_degree]
  · rw [if_neg hxu]
    by_cases hxv : x = v
    · subst hxv
      rw [if_pos rfl, if_pos (Or.inr rfl), Finset.card_erase_of_mem hmemv,
        G.card_neighborFinset_eq_degree]
    · have hnot : ¬ (x = u ∨ x = v) := by tauto
      rw [if_neg hxv, if_neg hnot, G.card_neighborFinset_eq_degree]

private lemma degree_le_edgeFinset_card {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) :
    G.degree v ≤ G.edgeFinset.card := by
  rw [← G.card_incidenceFinset_eq_degree]
  exact Finset.card_le_card (G.incidenceFinset_subset v)

end BasicHelpers

section CombinatorialBijection

private lemma exists_iso_equiv_of_finset_count_eq
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {F : ι → Type} (G : ∀ i, SimpleGraph (F i))
    {F' : κ → Type} (H : ∀ j, SimpleGraph (F' j)) :
    ∀ n : ℕ, ∀ (s : Finset ι) (t : Finset κ), s.card = n →
      (∀ i ∈ s, (s.filter (fun i' => Nonempty (G i' ≃g G i))).card =
        (t.filter (fun j => Nonempty (H j ≃g G i))).card) →
      (∀ j ∈ t, (s.filter (fun i => Nonempty (G i ≃g H j))).card =
        (t.filter (fun j' => Nonempty (H j' ≃g H j))).card) →
      ∃ e : {i // i ∈ s} ≃ {j // j ∈ t}, ∀ i : {i // i ∈ s}, Nonempty (G i.1 ≃g H (e i).1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s t hscard hs ht
    by_cases hne : s.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hne
      let s₁ : Finset ι := s.filter (fun i => Nonempty (G i ≃g G i₀))
      let t₁ : Finset κ := t.filter (fun j => Nonempty (H j ≃g G i₀))
      have hcard1 : s₁.card = t₁.card := hs i₀ hi₀
      have hi₀_mem : i₀ ∈ s₁ := Finset.mem_filter.mpr ⟨hi₀, ⟨SimpleGraph.Iso.refl⟩⟩
      let s₂ : Finset ι := s \ s₁
      let t₂ : Finset κ := t \ t₁
      have hs₂_lt : s₂.card < n := by
        have hsub : s₁ ⊆ s := Finset.filter_subset _ _
        have hpos : 0 < s₁.card := Finset.card_pos.mpr ⟨i₀, hi₀_mem⟩
        have hsum : s₂.card + s₁.card = s.card := Finset.card_sdiff_add_card_eq_card hsub
        omega
      have hs₂ : ∀ i ∈ s₂, (s₂.filter (fun i' => Nonempty (G i' ≃g G i))).card =
          (t₂.filter (fun j => Nonempty (H j ≃g G i))).card := by
        intro i hi
        have hi_s : i ∈ s := (Finset.mem_sdiff.mp hi).1
        have hi_not : ¬ Nonempty (G i ≃g G i₀) := by
          intro h
          exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨hi_s, h⟩)
        have hfs : s₂.filter (fun i' => Nonempty (G i' ≃g G i)) =
            s.filter (fun i' => Nonempty (G i' ≃g G i)) := by
          ext i'
          simp only [s₂, s₁, Finset.mem_filter, Finset.mem_sdiff, not_and]
          constructor
          · rintro ⟨⟨hi's, _⟩, h⟩
            exact ⟨hi's, h⟩
          · rintro ⟨hi's, ⟨φ⟩⟩
            refine ⟨⟨hi's, fun _ ⟨ψ⟩ => hi_not ⟨φ.symm.trans ψ⟩⟩, ⟨φ⟩⟩
        have hft : t₂.filter (fun j => Nonempty (H j ≃g G i)) =
            t.filter (fun j => Nonempty (H j ≃g G i)) := by
          ext j
          simp only [t₂, t₁, Finset.mem_filter, Finset.mem_sdiff, not_and]
          constructor
          · rintro ⟨⟨hjt, _⟩, h⟩
            exact ⟨hjt, h⟩
          · rintro ⟨hjt, ⟨φ⟩⟩
            refine ⟨⟨hjt, fun _ ⟨ψ⟩ => hi_not ⟨φ.symm.trans ψ⟩⟩, ⟨φ⟩⟩
        rw [hfs, hft]
        exact hs i hi_s
      have ht₂ : ∀ j ∈ t₂, (s₂.filter (fun i => Nonempty (G i ≃g H j))).card =
          (t₂.filter (fun j' => Nonempty (H j' ≃g H j))).card := by
        intro j hj
        have hj_t : j ∈ t := (Finset.mem_sdiff.mp hj).1
        have hj_not : ¬ Nonempty (H j ≃g G i₀) := by
          intro h
          exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨hj_t, h⟩)
        have hfs : s₂.filter (fun i => Nonempty (G i ≃g H j)) =
            s.filter (fun i => Nonempty (G i ≃g H j)) := by
          ext i
          simp only [s₂, s₁, Finset.mem_filter, Finset.mem_sdiff, not_and]
          constructor
          · rintro ⟨⟨his, _⟩, h⟩
            exact ⟨his, h⟩
          · rintro ⟨his, ⟨φ⟩⟩
            refine ⟨⟨his, fun _ ⟨ψ⟩ => hj_not ⟨φ.symm.trans ψ⟩⟩, ⟨φ⟩⟩
        have hft : t₂.filter (fun j' => Nonempty (H j' ≃g H j)) =
            t.filter (fun j' => Nonempty (H j' ≃g H j)) := by
          ext j'
          simp only [t₂, t₁, Finset.mem_filter, Finset.mem_sdiff, not_and]
          constructor
          · rintro ⟨⟨hj't, _⟩, h⟩
            exact ⟨hj't, h⟩
          · rintro ⟨hj't, ⟨φ⟩⟩
            refine ⟨⟨hj't, fun _ ⟨ψ⟩ => hj_not ⟨φ.symm.trans ψ⟩⟩, ⟨φ⟩⟩
        rw [hfs, hft]
        exact ht j hj_t
      obtain ⟨e₂, he₂⟩ := ih s₂.card hs₂_lt s₂ t₂ rfl hs₂ ht₂
      have hcard1' : Fintype.card {i // i ∈ s₁} = Fintype.card {j // j ∈ t₁} := by
        simpa [Fintype.card_coe] using hcard1
      let e₁ : {i // i ∈ s₁} ≃ {j // j ∈ t₁} := Fintype.equivOfCardEq hcard1'
      let toF : {i // i ∈ s} → {j // j ∈ t} := fun x =>
        if hx : x.1 ∈ s₁ then ⟨(e₁ ⟨x.1, hx⟩).1, (Finset.mem_filter.mp (e₁ ⟨x.1, hx⟩).2).1⟩
        else ⟨(e₂ ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).1,
          (Finset.mem_sdiff.mp (e₂ ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).2).1⟩
      let invF : {j // j ∈ t} → {i // i ∈ s} := fun y =>
        if hy : y.1 ∈ t₁ then ⟨(e₁.symm ⟨y.1, hy⟩).1, (Finset.mem_filter.mp (e₁.symm ⟨y.1, hy⟩).2).1⟩
        else ⟨(e₂.symm ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).1,
          (Finset.mem_sdiff.mp (e₂.symm ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).2).1⟩
      have hleft : ∀ x, invF (toF x) = x := by
        intro x
        apply Subtype.ext
        dsimp only [toF, invF]
        by_cases hx : x.1 ∈ s₁
        · rw [dif_pos hx, dif_pos (e₁ ⟨x.1, hx⟩).2]
          simp [Subtype.coe_eta]
        · rw [dif_neg hx]
          have hmem2 := (e₂ ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).2
          rw [dif_neg (Finset.mem_sdiff.mp hmem2).2]
          simp [Subtype.coe_eta]
      have hright : ∀ y, toF (invF y) = y := by
        intro y
        apply Subtype.ext
        dsimp only [toF, invF]
        by_cases hy : y.1 ∈ t₁
        · rw [dif_pos hy, dif_pos (e₁.symm ⟨y.1, hy⟩).2]
          simp [Subtype.coe_eta]
        · rw [dif_neg hy]
          have hmem2 := (e₂.symm ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).2
          rw [dif_neg (Finset.mem_sdiff.mp hmem2).2]
          simp [Subtype.coe_eta]
      let e : {i // i ∈ s} ≃ {j // j ∈ t} := ⟨toF, invF, hleft, hright⟩
      refine ⟨e, fun x => ?_⟩
      change Nonempty (G x.1 ≃g H (toF x).1)
      dsimp only [toF]
      by_cases hx : x.1 ∈ s₁
      · rw [dif_pos hx]
        obtain ⟨φ₁⟩ := (Finset.mem_filter.mp hx).2
        obtain ⟨φ₂⟩ := (Finset.mem_filter.mp (e₁ ⟨x.1, hx⟩).2).2
        exact ⟨φ₁.trans φ₂.symm⟩
      · rw [dif_neg hx]
        exact he₂ ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      have ht_empty : t = ∅ := by
        by_contra hne_t
        obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne_t
        have hpos : 0 < (t.filter (fun j' => Nonempty (H j' ≃g H j₀))).card :=
          Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨hj₀, ⟨SimpleGraph.Iso.refl⟩⟩⟩
        have hzero := ht j₀ hj₀
        simp at hzero
        omega
      subst ht_empty
      refine ⟨{ toFun := fun x => False.elim (Finset.notMem_empty x.1 x.2)
                invFun := fun y => False.elim (Finset.notMem_empty y.1 y.2)
                left_inv := fun x => False.elim (Finset.notMem_empty x.1 x.2)
                right_inv := fun y => False.elim (Finset.notMem_empty y.1 y.2) },
        fun x => False.elim (Finset.notMem_empty x.1 x.2)⟩

private lemma exists_iso_equiv_of_count_eq
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {F : ι → Type} (G : ∀ i, SimpleGraph (F i))
    {F' : κ → Type} (H : ∀ j, SimpleGraph (F' j))
    (h1 : ∀ i : ι, (Finset.univ.filter (fun i' => Nonempty (G i' ≃g G i))).card =
      (Finset.univ.filter (fun j => Nonempty (H j ≃g G i))).card)
    (h2 : ∀ j : κ, (Finset.univ.filter (fun i => Nonempty (G i ≃g H j))).card =
      (Finset.univ.filter (fun j' => Nonempty (H j' ≃g H j))).card) :
    ∃ e : ι ≃ κ, ∀ i : ι, Nonempty (G i ≃g H (e i)) := by
  obtain ⟨e, he⟩ := exists_iso_equiv_of_finset_count_eq G H (Finset.univ : Finset ι).card
    Finset.univ Finset.univ rfl (fun i _ => h1 i) (fun j _ => h2 j)
  let e' : ι ≃ κ := (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans
    (e.trans (Equiv.subtypeUnivEquiv Finset.mem_univ))
  exact ⟨e', fun i => he ⟨i, Finset.mem_univ i⟩⟩

end CombinatorialBijection

section EdgeKelly

private def edgeSubCnt {V : Type} (G : SimpleGraph V) [Fintype G.edgeSet]
    (P : SimpleGraph V → Prop) : ℕ :=
  (G.edgeFinset.powerset.filter
    (fun T : Finset (Sym2 V) => P (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))))).card

private lemma edgeSubCnt_eq_of_iso {V W : Type}
    {G : SimpleGraph V} {H : SimpleGraph W} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (φ : G ≃g H)
    {PV : SimpleGraph V → Prop} {PW : SimpleGraph W → Prop}
    (hiso : ∀ (S₁ : SimpleGraph V) (S₂ : SimpleGraph W), Nonempty (S₁ ≃g S₂) → (PV S₁ ↔ PW S₂)) :
    edgeSubCnt G PV = edgeSubCnt H PW := by
  unfold edgeSubCnt
  refine Finset.card_bij (fun (T : Finset (Sym2 V)) _ => T.image (Sym2.map φ.toEquiv)) ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hxG : x ∈ G.edgeSet := (G.mem_edgeFinset).mp (hT.1 hx)
      rw [H.mem_edgeFinset]
      exact (φ.mapEdgeSet ⟨x, hxG⟩).2
    · exact (hiso _ _ ⟨fromEdgeSet_image_iso φ.toEquiv T⟩).mp hT.2
  · intro T₁ _ T₂ _ h
    ext x
    have hiff : Sym2.map φ.toEquiv x ∈ T₁.image (Sym2.map φ.toEquiv) ↔
        Sym2.map φ.toEquiv x ∈ T₂.image (Sym2.map φ.toEquiv) := by rw [h]
    simpa [Finset.mem_image, (Sym2.map.injective φ.injective).eq_iff] using hiff
  · intro T' hT'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
    let T : Finset (Sym2 V) := T'.image (Sym2.map φ.symm.toEquiv)
    have himg : T.image (Sym2.map φ.toEquiv) = T' := by
      ext y
      simp only [T, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        have hcomp : Sym2.map φ.toEquiv (Sym2.map φ.symm.toEquiv z) = z := by
          rw [Sym2.map_map]
          have : φ.toEquiv ∘ φ.symm.toEquiv = id := funext φ.apply_symm_apply
          rw [this, Sym2.map_id, id_eq]
        rwa [hcomp]
      · intro hy
        refine ⟨Sym2.map φ.symm.toEquiv y, ⟨y, hy, rfl⟩, ?_⟩
        rw [Sym2.map_map]
        have : φ.toEquiv ∘ φ.symm.toEquiv = id := funext φ.apply_symm_apply
        rw [this, Sym2.map_id, id_eq]
    refine ⟨T, ?_, himg⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hyH : y ∈ H.edgeSet := (H.mem_edgeFinset).mp (hT'.1 hy)
      rw [G.mem_edgeFinset]
      exact (φ.symm.mapEdgeSet ⟨y, hyH⟩).2
    · have hisoT : SimpleGraph.fromEdgeSet (T : Set (Sym2 V)) ≃g
          SimpleGraph.fromEdgeSet (T' : Set (Sym2 W)) := by
        have h0 := fromEdgeSet_image_iso φ.toEquiv T
        rwa [himg] at h0
      exact (hiso _ _ ⟨hisoT⟩).mpr hT'.2

private lemma edgeSubCnt_double_count {V : Type} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (P : SimpleGraph V → Prop) (q : ℕ)
    (hcard : ∀ (S : SimpleGraph V) [Fintype S.edgeSet], P S → S.edgeFinset.card = q) :
    ∑ e ∈ G.edgeFinset, edgeSubCnt (G.deleteEdges {e}) P =
      (G.edgeFinset.card - q) * edgeSubCnt G P := by
  unfold edgeSubCnt
  have hrew : ∀ e ∈ G.edgeFinset,
      ((G.deleteEdges {e}).edgeFinset.powerset.filter
        (fun T : Finset (Sym2 V) => P (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))))).card =
      (G.edgeFinset.powerset.filter
        (fun T : Finset (Sym2 V) => P (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))) ∧ e ∉ T)).card := by
    intro e _
    congr 1
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, edgeFinset_deleteEdges_singleton]
    constructor
    · rintro ⟨hsub, hP⟩
      refine ⟨hsub.trans (Finset.erase_subset _ _), hP, fun he => (Finset.mem_erase.mp (hsub he)).1 rfl⟩
    · rintro ⟨hsub, hP, hne⟩
      refine ⟨fun x hx => Finset.mem_erase.mpr ⟨fun hxe => hne (hxe ▸ hx), hsub hx⟩, hP⟩
  rw [Finset.sum_congr rfl hrew]
  let S₀ : Finset (Finset (Sym2 V)) :=
    G.edgeFinset.powerset.filter (fun T : Finset (Sym2 V) => P (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))))
  have hrew2 : ∀ e ∈ G.edgeFinset,
      (G.edgeFinset.powerset.filter
        (fun T : Finset (Sym2 V) => P (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))) ∧ e ∉ T)).card =
      (S₀.filter (fun T => e ∉ T)).card := by
    intro e _
    congr 1
    ext T
    simp only [S₀, Finset.mem_filter, and_assoc]
  rw [Finset.sum_congr rfl hrew2]
  have hswap := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := G.edgeFinset) (t := S₀) (r := fun e T => e ∉ T)
  calc
    ∑ e ∈ G.edgeFinset, (S₀.filter (fun T => e ∉ T)).card
        = ∑ T ∈ S₀, (G.edgeFinset.filter (fun e => e ∉ T)).card := hswap
    _ = ∑ _T ∈ S₀, (G.edgeFinset.card - q) := by
        refine Finset.sum_congr rfl fun T hT => ?_
        have hTsub : T ⊆ G.edgeFinset := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
        have hTP : P (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))) := (Finset.mem_filter.mp hT).2
        have hTcard : T.card = q := by
          have := hcard _ hTP
          rwa [edgeFinset_fromEdgeSet_of_subset hTsub] at this
        have hfilt : G.edgeFinset.filter (fun e => e ∉ T) = G.edgeFinset \ T := by
          ext e
          simp [Finset.mem_sdiff]
        rw [hfilt, Finset.card_sdiff_of_subset hTsub, hTcard]
    _ = (G.edgeFinset.card - q) * S₀.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

private lemma edgeSubCnt_eq_of_edgeHypomorphic {V : Type} [Fintype V]
    {G H : SimpleGraph V} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (hEH : EdgeHypomorphic G H)
    (P : SimpleGraph V → Prop) (q : ℕ)
    (hiso : ∀ S₁ S₂ : SimpleGraph V, Nonempty (S₁ ≃g S₂) → (P S₁ ↔ P S₂))
    (hcard : ∀ (S : SimpleGraph V) [Fintype S.edgeSet], P S → S.edgeFinset.card = q)
    (hq : q < G.edgeFinset.card) :
    edgeSubCnt G P = edgeSubCnt H P := by
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := edgeFinset_card_eq_of_edgeHypomorphic hEH
  obtain ⟨σ, hσ⟩ := hEH
  have hsum : ∑ e ∈ G.edgeFinset, edgeSubCnt (G.deleteEdges {e}) P =
      ∑ e ∈ H.edgeFinset, edgeSubCnt (H.deleteEdges {e}) P := by
    refine Finset.sum_bij
      (fun e he => (σ ⟨e, (G.mem_edgeFinset).mp he⟩).1) ?_ ?_ ?_ ?_
    · intro e he
      exact (H.mem_edgeFinset).mpr (σ ⟨e, (G.mem_edgeFinset).mp he⟩).2
    · intro e₁ he₁ e₂ he₂ heq
      have hsub : σ ⟨e₁, (G.mem_edgeFinset).mp he₁⟩ = σ ⟨e₂, (G.mem_edgeFinset).mp he₂⟩ :=
        Subtype.ext heq
      exact congrArg Subtype.val (σ.injective hsub)
    · intro e' he'
      let e := σ.symm ⟨e', (H.mem_edgeFinset).mp he'⟩
      refine ⟨e.1, (G.mem_edgeFinset).mpr e.2, ?_⟩
      simp [e]
    · intro e he
      obtain ⟨φ⟩ := hσ ⟨e, (G.mem_edgeFinset).mp he⟩
      exact edgeSubCnt_eq_of_iso φ hiso
  rw [edgeSubCnt_double_count G P q hcard, edgeSubCnt_double_count H P q hcard, hm_eq] at hsum
  have hpos : 0 < H.edgeFinset.card - q := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos hsum

end EdgeKelly

section StarAndDegrees

private lemma star_iso_of_deg_eq_edges {V : Type} [Fintype V]
    {G H : SimpleGraph V} (hm : G.edgeFinset.card = H.edgeFinset.card)
    {v w : V} (hv : G.degree v = G.edgeFinset.card) (hw : H.degree w = H.edgeFinset.card) :
    Nonempty (G ≃g H) := by
  have hincG : G.incidenceFinset v = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le (G.incidenceFinset_subset v) (by rw [G.card_incidenceFinset_eq_degree, hv])
  have hincH : H.incidenceFinset w = H.edgeFinset :=
    Finset.eq_of_subset_of_card_le (H.incidenceFinset_subset w) (by rw [H.card_incidenceFinset_eq_degree, hw])
  have hadjG : ∀ x y : V, G.Adj x y ↔ (x = v ∧ y ∈ G.neighborFinset v) ∨ (y = v ∧ x ∈ G.neighborFinset v) := by
    intro x y
    constructor
    · intro hxy
      have hmem : s(x, y) ∈ G.incidenceFinset v := by
        rw [hincG, G.mem_edgeFinset]
        exact hxy
      rw [G.mem_incidenceFinset] at hmem
      rcases Sym2.mem_iff.mp hmem.2 with rfl | rfl
      · exact Or.inl ⟨rfl, (G.mem_neighborFinset _ _).mpr hxy⟩
      · exact Or.inr ⟨rfl, (G.mem_neighborFinset _ _).mpr hxy.symm⟩
    · rintro (⟨rfl, hy⟩ | ⟨rfl, hx⟩)
      · exact (G.mem_neighborFinset _ _).mp hy
      · exact ((G.mem_neighborFinset _ _).mp hx).symm
  have hadjH : ∀ x y : V, H.Adj x y ↔ (x = w ∧ y ∈ H.neighborFinset w) ∨ (y = w ∧ x ∈ H.neighborFinset w) := by
    intro x y
    constructor
    · intro hxy
      have hmem : s(x, y) ∈ H.incidenceFinset w := by
        rw [hincH, H.mem_edgeFinset]
        exact hxy
      rw [H.mem_incidenceFinset] at hmem
      rcases Sym2.mem_iff.mp hmem.2 with rfl | rfl
      · exact Or.inl ⟨rfl, (H.mem_neighborFinset _ _).mpr hxy⟩
      · exact Or.inr ⟨rfl, (H.mem_neighborFinset _ _).mpr hxy.symm⟩
    · rintro (⟨rfl, hy⟩ | ⟨rfl, hx⟩)
      · exact (H.mem_neighborFinset _ _).mp hy
      · exact ((H.mem_neighborFinset _ _).mp hx).symm
  let NG := G.neighborFinset v
  let NH := H.neighborFinset w
  have hNcard : NG.card = NH.card := by
    simp only [NG, NH, SimpleGraph.card_neighborFinset_eq_degree, hv, hw, hm]
  let RG : Finset V := Finset.univ \ insert v NG
  let RH : Finset V := Finset.univ \ insert w NH
  have hv_not : v ∉ NG := by simp [NG]
  have hw_not : w ∉ NH := by simp [NH]
  have hRcard : RG.card = RH.card := by
    have h1 : (insert v NG).card = NG.card + 1 := Finset.card_insert_of_notMem hv_not
    have h2 : (insert w NH).card = NH.card + 1 := Finset.card_insert_of_notMem hw_not
    have hs1 := Finset.card_sdiff_of_subset (Finset.subset_univ (insert v NG))
    have hs2 := Finset.card_sdiff_of_subset (Finset.subset_univ (insert w NH))
    simp only [RG, RH, hs1, hs2, h1, h2, hNcard]
  let eN : {x // x ∈ NG} ≃ {y // y ∈ NH} := Fintype.equivOfCardEq (by simpa [Fintype.card_coe] using hNcard)
  let eR : {x // x ∈ RG} ≃ {y // y ∈ RH} := Fintype.equivOfCardEq (by simpa [Fintype.card_coe] using hRcard)
  have hmemR : ∀ x : V, x ≠ v → x ∉ NG → x ∈ RG := fun x h1 h2 => by
    simp [RG, h1, h2]
  have hmemRH : ∀ y : V, y ≠ w → y ∉ NH → y ∈ RH := fun y h1 h2 => by
    simp [RH, h1, h2]
  let f : V → V := fun x =>
    if hxv : x = v then w
    else if hx : x ∈ NG then (eN ⟨x, hx⟩).1
    else (eR ⟨x, hmemR x hxv hx⟩).1
  let g : V → V := fun y =>
    if hyw : y = w then v
    else if hy : y ∈ NH then (eN.symm ⟨y, hy⟩).1
    else (eR.symm ⟨y, hmemRH y hyw hy⟩).1
  have hfg : ∀ x, g (f x) = x := by
    intro x
    dsimp only [f, g]
    by_cases hxv : x = v
    · subst hxv
      simp
    · rw [dif_neg hxv]
      by_cases hxN : x ∈ NG
      · rw [dif_pos hxN]
        have h1 : (eN ⟨x, hxN⟩).1 ≠ w := fun heq => hw_not (heq ▸ (eN ⟨x, hxN⟩).2)
        rw [dif_neg h1, dif_pos (eN ⟨x, hxN⟩).2]
        exact congrArg Subtype.val (eN.symm_apply_apply ⟨x, hxN⟩)
      · rw [dif_neg hxN]
        have hRmem := (eR ⟨x, hmemR x hxv hxN⟩).2
        simp only [RH, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, true_and, not_or] at hRmem
        rw [dif_neg hRmem.1, dif_neg hRmem.2]
        exact congrArg Subtype.val (eR.symm_apply_apply ⟨x, hmemR x hxv hxN⟩)
  have hgf : ∀ y, f (g y) = y := by
    intro y
    dsimp only [f, g]
    by_cases hyw : y = w
    · subst hyw
      simp
    · rw [dif_neg hyw]
      by_cases hyN : y ∈ NH
      · rw [dif_pos hyN]
        have h1 : (eN.symm ⟨y, hyN⟩).1 ≠ v := fun heq => hv_not (heq ▸ (eN.symm ⟨y, hyN⟩).2)
        rw [dif_neg h1, dif_pos (eN.symm ⟨y, hyN⟩).2]
        exact congrArg Subtype.val (eN.apply_symm_apply ⟨y, hyN⟩)
      · rw [dif_neg hyN]
        have hRmem := (eR.symm ⟨y, hmemRH y hyw hyN⟩).2
        simp only [RG, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, true_and, not_or] at hRmem
        rw [dif_neg hRmem.1, dif_neg hRmem.2]
        exact congrArg Subtype.val (eR.apply_symm_apply ⟨y, hmemRH y hyw hyN⟩)
  let eqv : V ≃ V := ⟨f, g, hfg, hgf⟩
  have hf_eq_w : ∀ x, f x = w ↔ x = v := by
    intro x
    constructor
    · intro h
      have := congrArg g h
      rw [hfg] at this
      simpa [g] using this
    · rintro rfl
      simp [f]
  have hf_mem_NH : ∀ x, f x ∈ NH ↔ x ∈ NG := by
    intro x
    dsimp only [f]
    by_cases hxv : x = v
    · subst hxv
      simp [hv_not, hw_not]
    · rw [dif_neg hxv]
      by_cases hxN : x ∈ NG
      · rw [dif_pos hxN]
        exact iff_of_true (eN ⟨x, hxN⟩).2 hxN
      · rw [dif_neg hxN]
        have hRmem := (eR ⟨x, hmemR x hxv hxN⟩).2
        simp only [RH, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, true_and, not_or] at hRmem
        exact iff_of_false hRmem.2 hxN
  refine ⟨⟨eqv, ?_⟩⟩
  intro x y
  change H.Adj (f x) (f y) ↔ G.Adj x y
  rw [hadjH, hadjG]
  simp only [hf_eq_w, hf_mem_NH, NG, NH]

private lemma star_edge_reconstructible {V : Type} [Fintype V]
    {G H : SimpleGraph V} (hE : 4 ≤ G.edgeFinset.card) (hEH : EdgeHypomorphic G H)
    {v : V} (hv : G.degree v = G.edgeFinset.card) :
    Nonempty (G ≃g H) := by
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := edgeFinset_card_eq_of_edgeHypomorphic hEH
  set m := G.edgeFinset.card
  obtain ⟨σ, hσ⟩ := hEH
  have hH_card_max : ∀ e' : H.edgeSet, ∃ w : V, (H.deleteEdges {e'.val}).degree w = m - 1 := by
    intro e'
    let e := σ.symm e'
    have hsim : Nonempty (G.deleteEdges {e.val} ≃g H.deleteEdges {e'.val}) := by
      simpa [e] using hσ e
    obtain ⟨φ⟩ := hsim
    obtain ⟨a, b, hab⟩ : ∃ a b, e.val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e.val
    have hadj : G.Adj a b := (G.mem_edgeSet).mp (hab ▸ e.2)
    have hincG : G.incidenceFinset v = G.edgeFinset :=
      Finset.eq_of_subset_of_card_le (G.incidenceFinset_subset v) (by rw [G.card_incidenceFinset_eq_degree, hv])
    have hv_mem : v ∈ s(a, b) := by
      have : s(a, b) ∈ G.incidenceFinset v := by
        rw [hincG, G.mem_edgeFinset]
        exact hadj
      exact (G.mem_incidenceFinset v _).mp this |>.2
    have hdeg_v : (G.deleteEdges {e.val}).degree v = m - 1 := by
      rw [hab, degree_deleteEdges_singleton_of_adj G hadj v, hv]
      have hdisj : v = a ∨ v = b := Sym2.mem_iff.mp hv_mem
      rw [if_pos hdisj]
    refine ⟨φ v, ?_⟩
    rw [φ.degree_eq v, hdeg_v]
  have hHne : H.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e₁val, he₁mem⟩ := hHne
  let e₁ : H.edgeSet := ⟨e₁val, (H.mem_edgeFinset).mp he₁mem⟩
  obtain ⟨w, hw_del⟩ := hH_card_max e₁
  have hw_le : H.degree w ≤ m := by
    rw [hm_eq]
    exact degree_le_edgeFinset_card H w
  have hw_ge : m - 1 ≤ H.degree w := by
    have hle : (H.deleteEdges {e₁.val}).degree w ≤ H.degree w :=
      SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)
    omega
  by_cases hwm : H.degree w = m
  · exact star_iso_of_deg_eq_edges hm_eq hv (hwm.trans hm_eq)
  · exfalso
    have hwm1 : H.degree w = m - 1 := by omega
    obtain ⟨a, b, hab⟩ : ∃ a b, e₁.val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₁.val
    have hadj1 : H.Adj a b := (H.mem_edgeSet).mp (hab ▸ e₁.2)
    have hw_not_e₁ : w ≠ a ∧ w ≠ b := by
      have hdeg := degree_deleteEdges_singleton_of_adj H hadj1 w
      rw [← hab, hw_del, hwm1] at hdeg
      by_contra hnot
      have hor : w = a ∨ w = b := by tauto
      rw [if_pos hor] at hdeg
      omega
    have hincH : H.incidenceFinset w = H.edgeFinset.erase e₁.val := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_erase]
        refine ⟨?_, H.incidenceFinset_subset w hx⟩
        intro hxe
        have hmem := (H.mem_incidenceFinset w x).mp hx |>.2
        rw [hxe, hab, Sym2.mem_iff] at hmem
        rcases hmem with rfl | rfl
        · exact hw_not_e₁.1 rfl
        · exact hw_not_e₁.2 rfl
      · rw [H.card_incidenceFinset_eq_degree, hwm1, Finset.card_erase_of_mem he₁mem, ← hm_eq]
    have hother_le : ∀ x : V, x ≠ w → H.degree x ≤ 2 := by
      intro x hxw
      have hsub : H.incidenceFinset x ⊆ {s(x, w), e₁.val} := by
        intro e he
        have heH : e ∈ H.edgeFinset := H.incidenceFinset_subset x he
        by_cases he1 : e = e₁.val
        · simp [he1]
        · have hew : e ∈ H.incidenceFinset w := by
            rw [hincH]
            exact Finset.mem_erase.mpr ⟨he1, heH⟩
          have hx_in : x ∈ e := (H.mem_incidenceFinset x e).mp he |>.2
          have hw_in : w ∈ e := (H.mem_incidenceFinset w e).mp hew |>.2
          obtain ⟨p, q, rfl⟩ : ∃ p q, e = s(p, q) := Sym2.ind (fun p q => ⟨p, q, rfl⟩) e
          rw [Sym2.mem_iff] at hx_in hw_in
          have heq : s(p, q) = s(x, w) := by
            rcases hx_in with rfl | rfl <;> rcases hw_in with rfl | rfl
            · exact False.elim (hxw rfl)
            · rfl
            · exact Sym2.eq_swap
            · exact False.elim (hxw rfl)
          simp [heq]
      rw [← H.card_incidenceFinset_eq_degree]
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    have hNw_ne : (H.neighborFinset w).Nonempty := by
      rw [← Finset.card_pos, H.card_neighborFinset_eq_degree, hwm1]
      omega
    obtain ⟨u, hu⟩ := hNw_ne
    have hadj_wu : H.Adj w u := (H.mem_neighborFinset w u).mp hu
    let e₂ : H.edgeSet := ⟨s(w, u), (H.mem_edgeSet).mpr hadj_wu⟩
    obtain ⟨z, hz⟩ := hH_card_max e₂
    by_cases hzw : z = w
    · subst hzw
      have hdeg := degree_deleteEdges_singleton_of_adj H hadj_wu z
      change (H.deleteEdges {s(z, u)}).degree z = m - 1 at hz
      rw [hdeg, if_pos (Or.inl rfl), hwm1] at hz
      omega
    · have hle : (H.deleteEdges {e₂.val}).degree z ≤ H.degree z :=
        SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)
      have hle2 := hother_le z hzw
      omega

private def starGraph (n k : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ k) ∨ (j.val = 0 ∧ 1 ≤ i.val ∧ i.val ≤ k)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨h0, h1, _⟩ | ⟨h0, h1, _⟩ <;> omega⟩

private lemma starGraph_degree_zero {n k : ℕ} (hkn : k + 1 ≤ n) :
    (starGraph n k).degree ⟨0, by omega⟩ = k := by
  rw [← (starGraph n k).card_neighborFinset_eq_degree]
  have hcard : ((starGraph n k).neighborFinset ⟨0, by omega⟩).card =
      (Finset.Icc 1 k).card := by
    refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
    · intro j hj
      rw [SimpleGraph.mem_neighborFinset] at hj
      rcases hj with ⟨_, h1, h2⟩ | ⟨h0, h1, _⟩
      · exact Finset.mem_Icc.mpr ⟨h1, h2⟩
      · dsimp only at h1
        omega
    · intro j₁ _ j₂ _ h
      exact Fin.ext h
    · intro a ha
      rw [Finset.mem_Icc] at ha
      refine ⟨⟨a, by omega⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact Or.inl ⟨rfl, ha.1, ha.2⟩
  rw [hcard, Nat.card_Icc]
  omega

private lemma starGraph_degree_other {n k : ℕ} (_hkn : k + 1 ≤ n) (i : Fin n) (hi : i.val ≠ 0) :
    (starGraph n k).degree i = if i.val ≤ k then 1 else 0 := by
  rw [← (starGraph n k).card_neighborFinset_eq_degree]
  by_cases hik : i.val ≤ k
  · rw [if_pos hik]
    have hnf : (starGraph n k).neighborFinset i = {⟨0, by omega⟩} := by
      ext j
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      change ((i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ k) ∨ (j.val = 0 ∧ 1 ≤ i.val ∧ i.val ≤ k)) ↔
        j = ⟨0, by omega⟩
      constructor
      · rintro (⟨h0, _, _⟩ | ⟨h0, _, _⟩)
        · exact False.elim (hi h0)
        · exact Fin.ext h0
      · rintro rfl
        exact Or.inr ⟨rfl, by omega, hik⟩
    rw [hnf, Finset.card_singleton]
  · rw [if_neg hik, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    rcases hj with ⟨h0, _, _⟩ | ⟨_, _, hle⟩
    · exact hi h0
    · exact hik hle

private lemma starGraph_edgeFinset_card {n k : ℕ} (hkn : k + 1 ≤ n) :
    (starGraph n k).edgeFinset.card = k := by
  have hsum : ∑ i : Fin n, (starGraph n k).degree i = 2 * k := by
    let z : Fin n := ⟨0, by omega⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
    rw [starGraph_degree_zero hkn]
    have hrest : ∑ i ∈ Finset.univ.erase z, (starGraph n k).degree i = k := by
      have hcongr : ∀ i ∈ Finset.univ.erase z,
          (starGraph n k).degree i = if i.val ≤ k then 1 else 0 := by
        intro i hi
        have hne : i.val ≠ 0 := by
          intro h0
          exact (Finset.mem_erase.mp hi).1 (Fin.ext h0)
        exact starGraph_degree_other hkn i hne
      rw [Finset.sum_congr rfl hcongr, Finset.sum_boole, Nat.cast_id]
      have hbij : ((Finset.univ.erase z).filter (fun i : Fin n => i.val ≤ k)).card =
          (Finset.Icc 1 k).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hi
          have hne : i.val ≠ 0 := fun h0 => hi.1 (Fin.ext h0)
          exact Finset.mem_Icc.mpr ⟨by omega, hi.2⟩
        · intro i₁ _ i₂ _ h
          exact Fin.ext h
        · intro a ha
          rw [Finset.mem_Icc] at ha
          refine ⟨⟨a, by omega⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
          refine ⟨fun h => ?_, ha.2⟩
          have : a = 0 := congrArg Fin.val h
          omega
      rw [hbij, Nat.card_Icc]
      omega
    omega
  have hhs := (starGraph n k).sum_degrees_eq_twice_card_edges
  omega

private lemma star_edgeSubCnt_eq_sum_choose {V : Type} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (hk2 : 2 ≤ k) (hkn : k + 1 ≤ Fintype.card V) :
    edgeSubCnt G (fun S => Nonempty (S ≃g starGraph (Fintype.card V) k)) =
      ∑ v : V, (G.degree v).choose k := by
  unfold edgeSubCnt
  have hrhs : ∑ v : V, (G.degree v).choose k =
      ((Finset.univ : Finset V).sigma (fun v => (G.neighborFinset v).powersetCard k)).card := by
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_powersetCard, G.card_neighborFinset_eq_degree]
  rw [hrhs]
  let n := Fintype.card V
  have hpair_iso : ∀ (v : V) (A : Finset V), A ∈ (G.neighborFinset v).powersetCard k →
      let T : Finset (Sym2 V) := A.image (fun u => s(v, u))
      T ⊆ G.edgeFinset ∧
      (∀ x y : V, (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Adj x y ↔
        (x = v ∧ y ∈ A) ∨ (y = v ∧ x ∈ A)) ∧
      Nonempty (SimpleGraph.fromEdgeSet (T : Set (Sym2 V)) ≃g starGraph n k) := by
    intro v A hA
    rw [Finset.mem_powersetCard] at hA
    obtain ⟨hAsub, hAcard⟩ := hA
    dsimp only
    set T : Finset (Sym2 V) := A.image (fun u => s(v, u))
    set S : SimpleGraph V := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
    have hv_notA : v ∉ A := fun hv => (G.mem_neighborFinset v v).mp (hAsub hv) |>.ne rfl
    have hTsub : T ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
      exact (G.mem_edgeFinset).mpr ((G.mem_neighborFinset v u).mp (hAsub hu))
    have hSadj : ∀ x y : V, S.Adj x y ↔ (x = v ∧ y ∈ A) ∨ (y = v ∧ x ∈ A) := by
      intro x y
      simp only [S, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, T, Finset.mem_image]
      constructor
      · rintro ⟨⟨u, hu, heq⟩, hne⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, hu⟩
        · exact Or.inr ⟨rfl, hu⟩
      · rintro (⟨rfl, hy⟩ | ⟨rfl, hx⟩)
        · exact ⟨⟨y, hy, rfl⟩, fun h => hv_notA (h ▸ hy)⟩
        · exact ⟨⟨x, hx, Sym2.eq_swap⟩, fun h => hv_notA (h.symm ▸ hx)⟩
    have hiso : Nonempty (S ≃g starGraph n k) := by
      have hcardA : Fintype.card {u // u ∈ A} = Fintype.card {j : Fin n // 1 ≤ j.val ∧ j.val ≤ k} := by
        rw [Fintype.card_coe, hAcard]
        have h2 : Fintype.card {j : Fin n // 1 ≤ j.val ∧ j.val ≤ k} = (Finset.Icc 1 k).card := by
          rw [Fintype.card_subtype]
          refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact Finset.mem_Icc.mpr hj
          · intro j₁ _ j₂ _ h
            exact Fin.ext h
          · intro a ha
            rw [Finset.mem_Icc] at ha
            refine ⟨⟨a, by omega⟩, ?_, rfl⟩
            simp [ha]
        rw [h2, Nat.card_Icc]
        omega
      let RV : Finset V := Finset.univ \ insert v A
      let RF : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => k < j.val)
      have hcardR : Fintype.card {x // x ∈ RV} = Fintype.card {j // j ∈ RF} := by
        rw [Fintype.card_coe, Fintype.card_coe]
        have h1 : RV.card = n - (k + 1) := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
            Finset.card_insert_of_notMem hv_notA, hAcard]
        have h2 : RF.card = n - (k + 1) := by
          have hbij : RF.card = (Finset.Ico (k + 1) n).card := by
            refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
            · intro j hj
              simp only [RF, Finset.mem_filter, Finset.mem_univ, true_and] at hj
              exact Finset.mem_Ico.mpr ⟨by omega, j.isLt⟩
            · intro j₁ _ j₂ _ h
              exact Fin.ext h
            · intro a ha
              rw [Finset.mem_Ico] at ha
              refine ⟨⟨a, ha.2⟩, ?_, rfl⟩
              simp [RF]
              omega
          rw [hbij, Nat.card_Ico]
        rw [h1, h2]
      let eA : {u // u ∈ A} ≃ {j : Fin n // 1 ≤ j.val ∧ j.val ≤ k} := Fintype.equivOfCardEq hcardA
      let eR : {x // x ∈ RV} ≃ {j // j ∈ RF} := Fintype.equivOfCardEq hcardR
      have hmemRV : ∀ x : V, x ≠ v → x ∉ A → x ∈ RV := fun x h1 h2 => by simp [RV, h1, h2]
      have hmemRF : ∀ j : Fin n, j.val ≠ 0 → ¬ (1 ≤ j.val ∧ j.val ≤ k) → j ∈ RF := fun j h1 h2 => by
        simp only [RF, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      let f : V → Fin n := fun x =>
        if hxv : x = v then ⟨0, by omega⟩
        else if hx : x ∈ A then (eA ⟨x, hx⟩).1
        else (eR ⟨x, hmemRV x hxv hx⟩).1
      let g : Fin n → V := fun j =>
        if hj0 : j.val = 0 then v
        else if hj : 1 ≤ j.val ∧ j.val ≤ k then (eA.symm ⟨j, hj⟩).1
        else (eR.symm ⟨j, hmemRF j hj0 hj⟩).1
      have hfg : ∀ x, g (f x) = x := by
        intro x
        dsimp only [f, g]
        by_cases hxv : x = v
        · subst hxv
          simp
        · rw [dif_neg hxv]
          by_cases hxA : x ∈ A
          · rw [dif_pos hxA]
            have hp := (eA ⟨x, hxA⟩).2
            rw [dif_neg (by omega : (eA ⟨x, hxA⟩).1.val ≠ 0), dif_pos hp]
            exact congrArg Subtype.val (eA.symm_apply_apply ⟨x, hxA⟩)
          · rw [dif_neg hxA]
            have hp := (Finset.mem_filter.mp (eR ⟨x, hmemRV x hxv hxA⟩).2).2
            rw [dif_neg (by omega : (eR ⟨x, hmemRV x hxv hxA⟩).1.val ≠ 0),
              dif_neg (by omega : ¬ (1 ≤ (eR ⟨x, hmemRV x hxv hxA⟩).1.val ∧
                (eR ⟨x, hmemRV x hxv hxA⟩).1.val ≤ k))]
            exact congrArg Subtype.val (eR.symm_apply_apply ⟨x, hmemRV x hxv hxA⟩)
      have hgf : ∀ j, f (g j) = j := by
        intro j
        dsimp only [f, g]
        by_cases hj0 : j.val = 0
        · rw [dif_pos hj0, dif_pos rfl]
          exact Fin.ext hj0.symm
        · rw [dif_neg hj0]
          by_cases hjA : 1 ≤ j.val ∧ j.val ≤ k
          · rw [dif_pos hjA]
            have h1 : (eA.symm ⟨j, hjA⟩).1 ≠ v := fun h => hv_notA (h ▸ (eA.symm ⟨j, hjA⟩).2)
            rw [dif_neg h1, dif_pos (eA.symm ⟨j, hjA⟩).2]
            exact congrArg Subtype.val (eA.apply_symm_apply ⟨j, hjA⟩)
          · rw [dif_neg hjA]
            have hR := (eR.symm ⟨j, hmemRF j hj0 hjA⟩).2
            simp only [RV, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, true_and, not_or] at hR
            rw [dif_neg hR.1, dif_neg hR.2]
            exact congrArg Subtype.val (eR.apply_symm_apply ⟨j, hmemRF j hj0 hjA⟩)
      have hf0 : ∀ x, (f x).val = 0 ↔ x = v := by
        intro x
        constructor
        · intro h
          have h' : f x = ⟨0, by omega⟩ := Fin.ext h
          have := congrArg g h'
          rw [hfg] at this
          simpa [g] using this
        · rintro rfl
          simp [f]
      have hfA : ∀ x, (1 ≤ (f x).val ∧ (f x).val ≤ k) ↔ x ∈ A := by
        intro x
        dsimp only [f]
        by_cases hxv : x = v
        · subst hxv
          simp [hv_notA]
        · rw [dif_neg hxv]
          by_cases hxA : x ∈ A
          · rw [dif_pos hxA]
            exact iff_of_true (eA ⟨x, hxA⟩).2 hxA
          · rw [dif_neg hxA]
            have hp := (Finset.mem_filter.mp (eR ⟨x, hmemRV x hxv hxA⟩).2).2
            exact iff_of_false (by omega) hxA
      refine ⟨⟨⟨f, g, hfg, hgf⟩, ?_⟩⟩
      intro x y
      change (starGraph n k).Adj (f x) (f y) ↔ S.Adj x y
      rw [hSadj]
      simp only [starGraph, hf0, hfA]
    exact ⟨hTsub, hSadj, hiso⟩
  symm
  refine Finset.card_bij (fun p _ => p.2.image (fun u => s(p.1, u))) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma] at hp
    have h := hpair_iso p.1 p.2 hp.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2.2⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_sigma] at hp₁ hp₂
    have h1 := hpair_iso p₁.1 p₁.2 hp₁.2
    have h2 := hpair_iso p₂.1 p₂.2 hp₂.2
    have hA1card : p₁.2.card = k := (Finset.mem_powersetCard.mp hp₁.2).2
    have hv_eq : p₁.1 = p₂.1 := by
      by_contra hne
      have h2lt : 1 < p₁.2.card := by omega
      obtain ⟨u₁, hu₁, u₂, hu₂, hu12⟩ := Finset.one_lt_card.mp h2lt
      have hm1 : s(p₁.1, u₁) ∈ p₂.2.image (fun u => s(p₂.1, u)) := by
        rw [← heq]
        exact Finset.mem_image_of_mem _ hu₁
      have hm2 : s(p₁.1, u₂) ∈ p₂.2.image (fun u => s(p₂.1, u)) := by
        rw [← heq]
        exact Finset.mem_image_of_mem _ hu₂
      obtain ⟨w₁, _, hw1⟩ := Finset.mem_image.mp hm1
      obtain ⟨w₂, _, hw2⟩ := Finset.mem_image.mp hm2
      rw [Sym2.eq_iff] at hw1 hw2
      have h1' : u₁ = p₂.1 := by
        rcases hw1 with ⟨h, _⟩ | ⟨h, _⟩
        · exact False.elim (hne h.symm)
        · exact h.symm
      have h2' : u₂ = p₂.1 := by
        rcases hw2 with ⟨h, _⟩ | ⟨h, _⟩
        · exact False.elim (hne h.symm)
        · exact h.symm
      exact hu12 (h1'.trans h2'.symm)
    cases p₁ with
    | mk v₁ A₁ =>
      cases p₂ with
      | mk v₂ A₂ =>
        dsimp only at hv_eq heq h1 h2
        subst hv_eq
        have hAeq : A₁ = A₂ := by
          ext u
          have hadj1 := h1.2.1 v₁ u
          have hadj2 := h2.2.1 v₁ u
          have hveq : (SimpleGraph.fromEdgeSet ((A₁.image (fun u => s(v₁, u)) : Finset (Sym2 V)) : Set (Sym2 V))).Adj v₁ u ↔
              (SimpleGraph.fromEdgeSet ((A₂.image (fun u => s(v₁, u)) : Finset (Sym2 V)) : Set (Sym2 V))).Adj v₁ u := by
            rw [heq]
          have hv1_not1 : v₁ ∉ A₁ := fun h => (G.mem_neighborFinset v₁ v₁).mp ((Finset.mem_powersetCard.mp hp₁.2).1 h) |>.ne rfl
          have hv1_not2 : v₁ ∉ A₂ := fun h => (G.mem_neighborFinset v₁ v₁).mp ((Finset.mem_powersetCard.mp hp₂.2).1 h) |>.ne rfl
          constructor
          · intro hu
            have h' := hadj2.mp (hveq.mp (hadj1.mpr (Or.inl ⟨rfl, hu⟩)))
            rcases h' with ⟨_, h⟩ | ⟨rfl, h⟩
            · exact h
            · exact False.elim (hv1_not2 h)
          · intro hu
            have h' := hadj1.mp (hveq.mpr (hadj2.mpr (Or.inl ⟨rfl, hu⟩)))
            rcases h' with ⟨_, h⟩ | ⟨rfl, h⟩
            · exact h
            · exact False.elim (hv1_not1 h)
        subst hAeq
        rfl
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTsub, ⟨φ⟩⟩ := hT
    set S := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
    let c : V := φ.symm ⟨0, by omega⟩
    let A : Finset V := S.neighborFinset c
    have hdeg_c : S.degree c = k := by
      have h := φ.degree_eq c
      have hfc : φ c = ⟨0, by omega⟩ := φ.apply_symm_apply ⟨0, by omega⟩
      rw [hfc, starGraph_degree_zero hkn] at h
      exact h.symm
    have hAcard : A.card = k := by
      rw [S.card_neighborFinset_eq_degree, hdeg_c]
    have hAsub : A ⊆ G.neighborFinset c := by
      intro u hu
      rw [G.mem_neighborFinset]
      exact fromEdgeSet_le_of_subset hTsub ((S.mem_neighborFinset c u).mp hu)
    have hTeq : A.image (fun u => s(c, u)) = T := by
      have hsub : A.image (fun u => s(c, u)) ⊆ T := by
        intro e he
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
        have hadj : S.Adj c u := (S.mem_neighborFinset c u).mp hu
        rw [← edgeFinset_fromEdgeSet_of_subset hTsub, S.mem_edgeFinset]
        exact hadj
      have hcard_img : (A.image (fun u => s(c, u))).card = k := by
        rw [Finset.card_image_of_injOn, hAcard]
        intro u₁ _ u₂ _ heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact h2.trans h1
      have hTcard : T.card = k := by
        rw [← edgeFinset_fromEdgeSet_of_subset hTsub, edgeFinset_card_eq_of_iso φ,
          starGraph_edgeFinset_card hkn]
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_img, hTcard])
    refine ⟨⟨c, A⟩, ?_, hTeq⟩
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_univ c, Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩⟩

private lemma degCount_eq_of_not_star {V : Type} [Fintype V]
    {G H : SimpleGraph V} (hEH : EdgeHypomorphic G H)
    (hG : ∀ v : V, G.degree v < G.edgeFinset.card)
    (hH : ∀ v : V, H.degree v < H.edgeFinset.card) :
    ∀ d : ℕ, (Finset.univ.filter (fun v : V => G.degree v = d)).card =
      (Finset.univ.filter (fun v : V => H.degree v = d)).card := by
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := edgeFinset_card_eq_of_edgeHypomorphic hEH
  set n := Fintype.card V
  set m := G.edgeFinset.card
  have hchoose : ∀ k : ℕ, 1 ≤ k →
      ∑ v : V, (G.degree v).choose k = ∑ v : V, (H.degree v).choose k := by
    intro k hk1
    by_cases hk1_eq : k = 1
    · subst hk1_eq
      simp only [Nat.choose_one_right, G.sum_degrees_eq_twice_card_edges,
        H.sum_degrees_eq_twice_card_edges]
      change 2 * m = 2 * H.edgeFinset.card
      rw [hm_eq]
    · have hk2 : 2 ≤ k := by omega
      by_cases hkm : k < m
      · by_cases hkn : k + 1 ≤ n
        · rw [← star_edgeSubCnt_eq_sum_choose G k hk2 hkn,
            ← star_edgeSubCnt_eq_sum_choose H k hk2 hkn]
          refine edgeSubCnt_eq_of_edgeHypomorphic hEH _ k ?_ ?_ hkm
          · intro S₁ S₂ ⟨φ⟩
            exact ⟨fun ⟨ψ⟩ => ⟨φ.symm.trans ψ⟩, fun ⟨ψ⟩ => ⟨φ.trans ψ⟩⟩
          · intro S _ ⟨φ⟩
            rw [edgeFinset_card_eq_of_iso φ, starGraph_edgeFinset_card hkn]
        · have hzeroG : ∀ v : V, (G.degree v).choose k = 0 := fun v =>
            Nat.choose_eq_zero_of_lt (lt_of_lt_of_le (G.degree_lt_card_verts v) (by omega))
          have hzeroH : ∀ v : V, (H.degree v).choose k = 0 := fun v =>
            Nat.choose_eq_zero_of_lt (lt_of_lt_of_le (H.degree_lt_card_verts v) (by omega))
          simp [hzeroG, hzeroH]
      · have hzeroG : ∀ v : V, (G.degree v).choose k = 0 := fun v =>
          Nat.choose_eq_zero_of_lt (lt_of_lt_of_le (hG v) (by omega))
        have hzeroH : ∀ v : V, (H.degree v).choose k = 0 := fun v =>
          Nat.choose_eq_zero_of_lt (lt_of_lt_of_le (hH v) (by omega))
        simp [hzeroG, hzeroH]
  let dcG : ℕ → ℕ := fun d => (Finset.univ.filter (fun v : V => G.degree v = d)).card
  let dcH : ℕ → ℕ := fun d => (Finset.univ.filter (fun v : V => H.degree v = d)).card
  have hsum_group : ∀ (X : SimpleGraph V) (k : ℕ),
      ∑ v : V, (X.degree v).choose k =
        ∑ d ∈ Finset.range n, (Finset.univ.filter (fun v : V => X.degree v = d)).card * d.choose k := by
    intro X k
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset V)) (t := Finset.range n) (g := fun v => X.degree v)
      (f := fun v => (X.degree v).choose k)
      (fun v _ => Finset.mem_range.mpr (X.degree_lt_card_verts v))
    rw [← hfib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.mp hv).2]),
      Finset.sum_const, smul_eq_mul]
  have hpos_d : ∀ t : ℕ, ∀ d : ℕ, 1 ≤ d → n - t ≤ d → dcG d = dcH d := by
    intro t
    induction t with
    | zero =>
      intro d _ hd
      have h0G : dcG d = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro v _
        exact ne_of_lt (lt_of_lt_of_le (G.degree_lt_card_verts v) (by omega))
      have h0H : dcH d = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro v _
        exact ne_of_lt (lt_of_lt_of_le (H.degree_lt_card_verts v) (by omega))
      rw [h0G, h0H]
    | succ t ih =>
      intro d hd1 hd
      by_cases hge : n - t ≤ d
      · exact ih d hd1 hge
      · have hdn : d < n := by omega
        have heq := hchoose d hd1
        rw [hsum_group G d, hsum_group H d] at heq
        have hsplit : ∀ (f : ℕ → ℕ),
            ∑ x ∈ Finset.range n, f x * x.choose d =
              f d + ∑ x ∈ (Finset.range n).erase d, f x * x.choose d := by
          intro f
          rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hdn), Nat.choose_self, mul_one]
        rw [hsplit dcG, hsplit dcH] at heq
        have htail : ∑ x ∈ (Finset.range n).erase d, dcG x * x.choose d =
            ∑ x ∈ (Finset.range n).erase d, dcH x * x.choose d := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxne : x ≠ d := (Finset.mem_erase.mp hx).1
          by_cases hxd : x < d
          · simp [Nat.choose_eq_zero_of_lt hxd]
          · rw [ih x (by omega) (by omega)]
        omega
  intro d
  change dcG d = dcH d
  by_cases hd0 : d = 0
  · subst hd0
    have htotG : ∑ x ∈ Finset.range n, dcG x = n := by
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset V)) (t := Finset.range n) (g := fun v => G.degree v)
        (f := fun _ => 1) (fun v _ => Finset.mem_range.mpr (G.degree_lt_card_verts v))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at hfib
      exact hfib
    have htotH : ∑ x ∈ Finset.range n, dcH x = n := by
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset V)) (t := Finset.range n) (g := fun v => H.degree v)
        (f := fun _ => 1) (fun v _ => Finset.mem_range.mpr (H.degree_lt_card_verts v))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at hfib
      exact hfib
    by_cases hn0 : n = 0
    · have h0G : dcG 0 = 0 := by
        have := Finset.card_le_univ (Finset.univ.filter (fun v : V => G.degree v = 0))
        change dcG 0 ≤ n at this
        omega
      have h0H : dcH 0 = 0 := by
        have := Finset.card_le_univ (Finset.univ.filter (fun v : V => H.degree v = 0))
        change dcH 0 ≤ n at this
        omega
      rw [h0G, h0H]
    · have h0mem : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ h0mem] at htotG htotH
      have hrest : ∑ x ∈ (Finset.range n).erase 0, dcG x =
          ∑ x ∈ (Finset.range n).erase 0, dcH x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxne : x ≠ 0 := (Finset.mem_erase.mp hx).1
        exact hpos_d n x (by omega) (by omega)
      omega
  · exact hpos_d n d (by omega) (by omega)

end StarAndDegrees

section StripIsolates

private lemma iso_of_strip_isolates {α β : Type} [Fintype α] [Fintype β]
    {A : SimpleGraph α} {B : SimpleGraph β}
    (P : α → Prop) (Q : β → Prop)
    (hP : ∀ a : α, ¬ P a → ∀ x : α, ¬ A.Adj a x)
    (hQ : ∀ b : β, ¬ Q b → ∀ y : β, ¬ B.Adj b y)
    (hcard : (Finset.univ.filter (fun a : α => ¬ P a)).card =
      (Finset.univ.filter (fun b : β => ¬ Q b)).card)
    (hiso : Nonempty (A ≃g B)) :
    Nonempty (A.induce {a | P a} ≃g B.induce {b | Q b}) := by
  obtain ⟨φ⟩ := hiso
  let AP := {a : α // P a}
  let BQ := {b : β // Q b}
  let A_iso : Finset AP := Finset.univ.filter (fun x : AP => ∀ u : α, ¬ A.Adj x.1 u)
  let B_iso : Finset BQ := Finset.univ.filter (fun y : BQ => ∀ v : β, ¬ B.Adj y.1 v)
  have hφ_Q : ∀ x : AP, (∃ u : α, A.Adj x.1 u) → Q (φ x.1) := by
    rintro x ⟨u, hu⟩
    by_contra hnot
    exact hQ (φ x.1) hnot (φ u) (φ.map_rel_iff.mpr hu)
  have hφ_P : ∀ y : BQ, (∃ v : β, B.Adj y.1 v) → P (φ.symm y.1) := by
    rintro y ⟨v, hv⟩
    by_contra hnot
    have h1 : A.Adj (φ.symm y.1) (φ.symm v) := φ.symm.map_rel_iff.mpr hv
    exact hP (φ.symm y.1) hnot (φ.symm v) h1
  have htot_iso : isoCount A = isoCount B := isoCount_eq_of_iso φ
  have hsplitA : isoCount A = A_iso.card + (Finset.univ.filter (fun a : α => ¬ P a)).card := by
    unfold isoCount
    have h1 : A_iso.card = (Finset.univ.filter (fun a : α => (∀ u, ¬ A.Adj a u) ∧ P a)).card := by
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro x hx
        simp only [A_iso, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨hx, x.2⟩
      · intro x₁ _ x₂ _ h
        exact Subtype.ext h
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ⟨⟨a, ha.2⟩, by simp [A_iso, ha.1], rfl⟩
    have h2 : (Finset.univ.filter (fun a : α => ¬ P a)).card =
        (Finset.univ.filter (fun a : α => (∀ u, ¬ A.Adj a u) ∧ ¬ P a)).card := by
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hn => ⟨hP a hn, hn⟩, fun h => h.2⟩
    rw [h1, h2, ← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_filter]
      intro a _ h1' h2'
      exact h2'.2 h1'.2
  have hsplitB : isoCount B = B_iso.card + (Finset.univ.filter (fun b : β => ¬ Q b)).card := by
    unfold isoCount
    have h1 : B_iso.card = (Finset.univ.filter (fun b : β => (∀ v, ¬ B.Adj b v) ∧ Q b)).card := by
      refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
      · intro y hy
        simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact ⟨hy, y.2⟩
      · intro y₁ _ y₂ _ h
        exact Subtype.ext h
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        exact ⟨⟨b, hb.2⟩, by simp [B_iso, hb.1], rfl⟩
    have h2 : (Finset.univ.filter (fun b : β => ¬ Q b)).card =
        (Finset.univ.filter (fun b : β => (∀ v, ¬ B.Adj b v) ∧ ¬ Q b)).card := by
      congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hn => ⟨hQ b hn, hn⟩, fun h => h.2⟩
    rw [h1, h2, ← Finset.card_union_of_disjoint]
    · congr 1
      ext b
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_filter]
      intro b _ h1' h2'
      exact h2'.2 h1'.2
  have hiso_card : A_iso.card = B_iso.card := by omega
  let eIso : {x : AP // x ∈ A_iso} ≃ {y : BQ // y ∈ B_iso} :=
    Fintype.equivOfCardEq (by simpa [Fintype.card_coe] using hiso_card)
  have hmemAiso : ∀ x : AP, ¬ (∃ u : α, A.Adj x.1 u) → x ∈ A_iso := by
    intro x hx
    push Not at hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
  have hmemBiso : ∀ y : BQ, ¬ (∃ v : β, B.Adj y.1 v) → y ∈ B_iso := by
    intro y hy
    push Not at hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
  let f : AP → BQ := fun x =>
    if hx : ∃ u : α, A.Adj x.1 u then ⟨φ x.1, hφ_Q x hx⟩
    else (eIso ⟨x, hmemAiso x hx⟩).1
  let g : BQ → AP := fun y =>
    if hy : ∃ v : β, B.Adj y.1 v then ⟨φ.symm y.1, hφ_P y hy⟩
    else (eIso.symm ⟨y, hmemBiso y hy⟩).1
  have hfg : ∀ x, g (f x) = x := by
    intro x
    dsimp only [f, g]
    by_cases hx : ∃ u : α, A.Adj x.1 u
    · rw [dif_pos hx]
      obtain ⟨u, hu⟩ := hx
      have hy : ∃ v : β, B.Adj (φ x.1) v := ⟨φ u, φ.map_rel_iff.mpr hu⟩
      rw [dif_pos hy]
      exact Subtype.ext (φ.symm_apply_apply x.1)
    · rw [dif_neg hx]
      have h0 : ∀ v : β, ¬ B.Adj (eIso ⟨x, hmemAiso x hx⟩).1.1 v :=
        (Finset.mem_filter.mp (eIso ⟨x, hmemAiso x hx⟩).2).2
      have hnot : ¬ (∃ v : β, B.Adj (eIso ⟨x, hmemAiso x hx⟩).1.1 v) := by
        rintro ⟨v, hv⟩
        exact h0 v hv
      rw [dif_neg hnot]
      exact congrArg Subtype.val (eIso.symm_apply_apply ⟨x, hmemAiso x hx⟩)
  have hgf : ∀ y, f (g y) = y := by
    intro y
    dsimp only [f, g]
    by_cases hy : ∃ v : β, B.Adj y.1 v
    · rw [dif_pos hy]
      obtain ⟨v, hv⟩ := hy
      have hx : ∃ u : α, A.Adj (φ.symm y.1) u := ⟨φ.symm v, φ.symm.map_rel_iff.mpr hv⟩
      rw [dif_pos hx]
      exact Subtype.ext (φ.apply_symm_apply y.1)
    · rw [dif_neg hy]
      have h0 : ∀ u : α, ¬ A.Adj (eIso.symm ⟨y, hmemBiso y hy⟩).1.1 u :=
        (Finset.mem_filter.mp (eIso.symm ⟨y, hmemBiso y hy⟩).2).2
      have hnot : ¬ (∃ u : α, A.Adj (eIso.symm ⟨y, hmemBiso y hy⟩).1.1 u) := by
        rintro ⟨u, hu⟩
        exact h0 u hu
      rw [dif_neg hnot]
      exact congrArg Subtype.val (eIso.apply_symm_apply ⟨y, hmemBiso y hy⟩)
  refine ⟨⟨⟨f, g, hfg, hgf⟩, ?_⟩⟩
  intro x₁ x₂
  change B.Adj (f x₁).1 (f x₂).1 ↔ A.Adj x₁.1 x₂.1
  dsimp only [f]
  by_cases h1 : ∃ u : α, A.Adj x₁.1 u
  · rw [dif_pos h1]
    by_cases h2 : ∃ u : α, A.Adj x₂.1 u
    · rw [dif_pos h2]
      exact φ.map_rel_iff
    · rw [dif_neg h2]
      have hB0 : ∀ v : β, ¬ B.Adj (eIso ⟨x₂, hmemAiso x₂ h2⟩).1.1 v :=
        (Finset.mem_filter.mp (eIso ⟨x₂, hmemAiso x₂ h2⟩).2).2
      exact iff_of_false
        (fun h => hB0 (φ x₁.1) h.symm)
        (fun h => h2 ⟨x₁.1, h.symm⟩)
  · rw [dif_neg h1]
    have hB0 : ∀ v : β, ¬ B.Adj (eIso ⟨x₁, hmemAiso x₁ h1⟩).1.1 v :=
      (Finset.mem_filter.mp (eIso ⟨x₁, hmemAiso x₁ h1⟩).2).2
    exact iff_of_false (hB0 _) (fun h => h1 ⟨x₂.1, h⟩)

private def actSubgraph {V : Type} (G : SimpleGraph V) :
    SimpleGraph {v : V // ∃ u : V, G.Adj v u} :=
  G.induce {v : V | ∃ u : V, G.Adj v u}

private def edgeSet_actSubgraph_equiv {V : Type} (G : SimpleGraph V) :
    (actSubgraph G).edgeSet ≃ G.edgeSet := by
  have hmem : ∀ e : (actSubgraph G).edgeSet, Sym2.map Subtype.val e.1 ∈ G.edgeSet := by
    rintro ⟨e, he⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
    exact he
  have hlift : Function.Surjective (fun e : (actSubgraph G).edgeSet =>
      (⟨Sym2.map Subtype.val e.1, hmem e⟩ : G.edgeSet)) := by
    rintro ⟨e, he⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
    have hadj : G.Adj a b := (G.mem_edgeSet).mp he
    exact ⟨⟨s(⟨a, ⟨b, hadj⟩⟩, ⟨b, ⟨a, hadj.symm⟩⟩), hadj⟩, Subtype.ext rfl⟩
  have hinj : Function.Injective (fun e : (actSubgraph G).edgeSet =>
      (⟨Sym2.map Subtype.val e.1, hmem e⟩ : G.edgeSet)) := by
    intro e₁ e₂ h
    exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
  exact Equiv.ofBijective _ ⟨hinj, hlift⟩

private lemma strip_isolates {V : Type} [Fintype V]
    {G H : SimpleGraph V} (hE : 4 ≤ G.edgeFinset.card) (hEH : EdgeHypomorphic G H)
    (hiso_eq : isoCount G = isoCount H) :
    ∃ (W : Type) (_ : Fintype W) (G' H' : SimpleGraph W),
      4 ≤ Fintype.card W ∧ 4 ≤ G'.edgeSet.ncard ∧
      (∀ w : W, ∃ u : W, G'.Adj w u) ∧ (∀ w : W, ∃ u : W, H'.Adj w u) ∧
      EdgeHypomorphic G' H' ∧ (Nonempty (G' ≃g H') → Nonempty (G ≃g H)) := by
  let W := {v : V // ∃ u : V, G.Adj v u}
  let WH := {v : V // ∃ u : V, H.Adj v u}
  have hcardW : Fintype.card W = Fintype.card WH := by
    have h1 : Fintype.card W + isoCount G = Fintype.card V := by
      unfold isoCount
      rw [Fintype.card_subtype]
      have hcompl : Finset.univ.filter (fun v : V => ∃ u : V, G.Adj v u) =
          (Finset.univ.filter (fun v : V => ∀ u : V, ¬ G.Adj v u))ᶜ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
        push Not
        rfl
      rw [hcompl, add_comm, Finset.card_add_card_compl]
    have h2 : Fintype.card WH + isoCount H = Fintype.card V := by
      unfold isoCount
      rw [Fintype.card_subtype]
      have hcompl : Finset.univ.filter (fun v : V => ∃ u : V, H.Adj v u) =
          (Finset.univ.filter (fun v : V => ∀ u : V, ¬ H.Adj v u))ᶜ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
        push Not
        rfl
      rw [hcompl, add_comm, Finset.card_add_card_compl]
    omega
  let eAct : W ≃ WH := Fintype.equivOfCardEq hcardW
  let G' : SimpleGraph W := actSubgraph G
  let H_act : SimpleGraph WH := actSubgraph H
  let H' : SimpleGraph W := H_act.comap eAct
  let φH : H' ≃g H_act := ⟨eAct, fun {_ _} => Iff.rfl⟩
  have hE'card : G'.edgeFinset.card = G.edgeFinset.card := by
    rw [← G'.card_edgeSet, ← G.card_edgeSet]
    exact Fintype.card_congr (edgeSet_actSubgraph_equiv G)
  have hE' : 4 ≤ G'.edgeSet.ncard := by
    rw [ncard_edgeSet_eq_card_edgeFinset G', hE'card]
    exact hE
  have h4W : 4 ≤ Fintype.card W := four_le_card_of_four_le_edgeFinset G' (hE'card ▸ hE)
  have hNoIsoG : ∀ w : W, ∃ u : W, G'.Adj w u := by
    intro w
    obtain ⟨u, hu⟩ := w.2
    exact ⟨⟨u, ⟨w.1, hu.symm⟩⟩, hu⟩
  have hNoIsoH : ∀ w : W, ∃ u : W, H'.Adj w u := by
    intro w
    obtain ⟨u, hu⟩ := (eAct w).2
    refine ⟨eAct.symm ⟨u, ⟨(eAct w).1, hu.symm⟩⟩, ?_⟩
    change H.Adj (eAct w).1 (eAct (eAct.symm ⟨u, _⟩)).1
    rw [eAct.apply_symm_apply]
    exact hu
  have hcard_not : (Finset.univ.filter (fun v : V => ¬ (∃ u : V, G.Adj v u))).card =
      (Finset.univ.filter (fun v : V => ¬ (∃ u : V, H.Adj v u))).card := by
    have h1 : (Finset.univ.filter (fun v : V => ¬ (∃ u : V, G.Adj v u))).card = isoCount G := by
      unfold isoCount
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      push Not
      rfl
    have h2 : (Finset.univ.filter (fun v : V => ¬ (∃ u : V, H.Adj v u))).card = isoCount H := by
      unfold isoCount
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      push Not
      rfl
    rw [h1, h2, hiso_eq]
  have hEH' : EdgeHypomorphic G' H' := by
    obtain ⟨σ, hσ⟩ := hEH
    let eG := edgeSet_actSubgraph_equiv G
    let eH := edgeSet_actSubgraph_equiv H
    let σ' : G'.edgeSet ≃ H'.edgeSet :=
      eG.trans (σ.trans (eH.symm.trans φH.symm.mapEdgeSet))
    refine ⟨σ', fun e' => ?_⟩
    let eG0 : G.edgeSet := eG e'
    let eH0 : H.edgeSet := σ eG0
    have hdelG : (G.deleteEdges {eG0.1}).induce {v : V | ∃ u : V, G.Adj v u} =
        G'.deleteEdges {e'.1} := by
      ext a b
      simp only [SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
      refine and_congr Iff.rfl (not_congr ?_)
      have hmap : eG0.1 = Sym2.map Subtype.val e'.1 := rfl
      rw [hmap]
      constructor
      · intro h
        exact Sym2.map.injective Subtype.val_injective (by simpa [Sym2.map_mk] using h)
      · intro h
        rw [← h, Sym2.map_mk]
    let eH_act : H_act.edgeSet := eH.symm eH0
    have hdelH : (H.deleteEdges {eH0.1}).induce {v : V | ∃ u : V, H.Adj v u} =
        H_act.deleteEdges {eH_act.1} := by
      ext a b
      simp only [SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
      refine and_congr Iff.rfl (not_congr ?_)
      have hmap : eH0.1 = Sym2.map Subtype.val eH_act.1 := by
        have := eH.apply_symm_apply eH0
        exact congrArg Subtype.val this.symm
      rw [hmap]
      constructor
      · intro h
        exact Sym2.map.injective Subtype.val_injective (by simpa [Sym2.map_mk] using h)
      · intro h
        rw [← h, Sym2.map_mk]
    have hdelH' : H_act.deleteEdges {eH_act.1} ≃g H'.deleteEdges {(σ' e').1} := by
      refine ⟨φH.symm.toEquiv, ?_⟩
      intro a b
      simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
      refine and_congr φH.symm.map_rel_iff (not_congr ?_)
      have hσ'eq : (σ' e').1 = Sym2.map φH.symm.toEquiv eH_act.1 := rfl
      rw [hσ'eq]
      constructor
      · intro h
        exact Sym2.map.injective φH.symm.injective (by simpa [Sym2.map_mk] using h)
      · intro h
        rw [← h, Sym2.map_mk]
    have hiso_ind : Nonempty ((G.deleteEdges {eG0.1}).induce {v : V | ∃ u : V, G.Adj v u} ≃g
        (H.deleteEdges {eH0.1}).induce {v : V | ∃ u : V, H.Adj v u}) := by
      refine iso_of_strip_isolates (fun v => ∃ u, G.Adj v u) (fun v => ∃ u, H.Adj v u)
        ?_ ?_ (by convert hcard_not) (hσ eG0)
      · intro v hv x hdx
        exact hv ⟨x, SimpleGraph.deleteEdges_le _ hdx⟩
      · intro v hv x hdx
        exact hv ⟨x, SimpleGraph.deleteEdges_le _ hdx⟩
    obtain ⟨ψ⟩ := hiso_ind
    rw [hdelG, hdelH] at ψ
    exact ⟨ψ.trans hdelH'⟩
  have hLift : Nonempty (G' ≃g H') → Nonempty (G ≃g H) := by
    rintro ⟨φ⟩
    let φ₁ : G' ≃g H_act := φ.trans φH
    have hcard_iso_sub : Fintype.card {v : V // ¬ (∃ u : V, G.Adj v u)} =
        Fintype.card {v : V // ¬ (∃ u : V, H.Adj v u)} := by
      simpa only [Fintype.card_subtype] using hcard_not
    let eIso : {v : V // ¬ (∃ u : V, G.Adj v u)} ≃ {v : V // ¬ (∃ u : V, H.Adj v u)} :=
      Fintype.equivOfCardEq hcard_iso_sub
    let f : V → V := fun v =>
      if hv : ∃ u : V, G.Adj v u then (φ₁ ⟨v, hv⟩).1 else (eIso ⟨v, hv⟩).1
    let g : V → V := fun w =>
      if hw : ∃ u : V, H.Adj w u then (φ₁.symm ⟨w, hw⟩).1 else (eIso.symm ⟨w, hw⟩).1
    have hfg : ∀ v, g (f v) = v := by
      intro v
      dsimp only [f, g]
      by_cases hv : ∃ u : V, G.Adj v u
      · rw [dif_pos hv, dif_pos (φ₁ ⟨v, hv⟩).2]
        exact congrArg Subtype.val (φ₁.symm_apply_apply ⟨v, hv⟩)
      · rw [dif_neg hv, dif_neg (eIso ⟨v, hv⟩).2]
        exact congrArg Subtype.val (eIso.symm_apply_apply ⟨v, hv⟩)
    have hgf : ∀ w, f (g w) = w := by
      intro w
      dsimp only [f, g]
      by_cases hw : ∃ u : V, H.Adj w u
      · rw [dif_pos hw, dif_pos (φ₁.symm ⟨w, hw⟩).2]
        exact congrArg Subtype.val (φ₁.apply_symm_apply ⟨w, hw⟩)
      · rw [dif_neg hw, dif_neg (eIso.symm ⟨w, hw⟩).2]
        exact congrArg Subtype.val (eIso.apply_symm_apply ⟨w, hw⟩)
    refine ⟨⟨⟨f, g, hfg, hgf⟩, ?_⟩⟩
    intro x y
    change H.Adj (f x) (f y) ↔ G.Adj x y
    dsimp only [f]
    by_cases hx : ∃ u : V, G.Adj x u
    · rw [dif_pos hx]
      by_cases hy : ∃ u : V, G.Adj y u
      · rw [dif_pos hy]
        exact φ₁.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
      · rw [dif_neg hy]
        exact iff_of_false
          (fun h => (eIso ⟨y, hy⟩).2 ⟨(φ₁ ⟨x, hx⟩).1, h.symm⟩)
          (fun h => hy ⟨x, h.symm⟩)
    · rw [dif_neg hx]
      exact iff_of_false
        (fun h => (eIso ⟨x, hx⟩).2 ⟨_, h⟩)
        (fun h => hx ⟨y, h⟩)
  exact ⟨W, inferInstance, G', H', h4W, hE', hNoIsoG, hNoIsoH, hEH', hLift⟩

end StripIsolates

section DisconnectedCase

private def compGraph {W : Type} (G : SimpleGraph W) (C : G.ConnectedComponent) :
    SimpleGraph {w : W // G.connectedComponentMk w = C} :=
  G.induce {w : W | G.connectedComponentMk w = C}

private lemma walk_lift_compGraph {W : Type} {G : SimpleGraph W} {C : G.ConnectedComponent}
    {x y : W} (hx : G.connectedComponentMk x = C) (p : G.Walk x y) :
    ∃ (hy : G.connectedComponentMk y = C),
      Nonempty ((compGraph G C).Walk ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction p with
  | nil => exact ⟨hx, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons a b c hab p ih =>
    have hb : G.connectedComponentMk b = C := by
      rw [← hx]
      exact SimpleGraph.ConnectedComponent.eq.mpr hab.reachable.symm
    obtain ⟨hc, ⟨q⟩⟩ := ih hb
    have hab' : (compGraph G C).Adj ⟨a, hx⟩ ⟨b, hb⟩ := hab
    exact ⟨hc, ⟨SimpleGraph.Walk.cons hab' q⟩⟩

private lemma compGraph_connected {W : Type} (G : SimpleGraph W) (C : G.ConnectedComponent) :
    (compGraph G C).Connected := by
  obtain ⟨w₀, hw₀⟩ := Quot.exists_rep C
  have : Nonempty {w : W // G.connectedComponentMk w = C} := ⟨⟨w₀, hw₀⟩⟩
  refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩
  have hreach : G.Reachable x y := SimpleGraph.ConnectedComponent.eq.mp (hx.trans hy.symm)
  obtain ⟨p⟩ := hreach
  obtain ⟨_, ⟨q⟩⟩ := walk_lift_compGraph hx p
  exact ⟨q⟩

private lemma walk_map_subtype_isCycle {W : Type} {G : SimpleGraph W} {S : Set W}
    {x : S} {p : (G.induce S).Walk x x} (hp : p.IsCycle) :
    (p.map (SimpleGraph.Embedding.induce S).toHom).IsCycle := by
  refine SimpleGraph.Walk.IsCycle.mk ?_ ?_
  · refine SimpleGraph.Walk.IsCircuit.mk ?_ ?_
    · refine SimpleGraph.Walk.IsTrail.mk ?_
      rw [SimpleGraph.Walk.edges_map]
      exact hp.isTrail.edges_nodup.map (Sym2.map.injective Subtype.val_injective)
    · intro hnil
      apply hp.ne_nil
      cases p with
      | nil => rfl
      | cons _ _ => cases hnil
  · rw [SimpleGraph.Walk.support_map]
    change (p.support.map Subtype.val).tail.Nodup
    have htail : (p.support.map Subtype.val).tail = p.support.tail.map Subtype.val := by
      cases p.support <;> rfl
    rw [htail]
    exact hp.support_nodup.map Subtype.val_injective

private lemma compGraph_isAcyclic {W : Type} {G : SimpleGraph W} (ha : G.IsAcyclic)
    (C : G.ConnectedComponent) : (compGraph G C).IsAcyclic := by
  intro x p hp
  exact ha (p.map (SimpleGraph.Embedding.induce _).toHom) (walk_map_subtype_isCycle hp)

private lemma walk_lift_deleteEdges {W : Type} {G : SimpleGraph W} {e : Sym2 W}
    {x y : W} (p : G.Walk x y) (he : e ∉ p.edges) :
    ∃ q : (G.deleteEdges {e}).Walk x y, q.support = p.support ∧ q.edges = p.edges := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl, rfl⟩
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at he
    obtain ⟨q, hsup, hed⟩ := ih he.2
    have hab' : (G.deleteEdges {e}).Adj a b :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hab, Ne.symm he.1⟩
    refine ⟨SimpleGraph.Walk.cons hab' q, ?_, ?_⟩
    · simp [hsup]
    · simp [hed]

private lemma walk_lift_deleteEdges_isCycle {W : Type} {G : SimpleGraph W} {e : Sym2 W}
    {x : W} (p : G.Walk x x) (hp : p.IsCycle) (he : e ∉ p.edges) :
    ¬ (G.deleteEdges {e}).IsAcyclic := by
  obtain ⟨q, hsup, hed⟩ := walk_lift_deleteEdges p he
  intro ha
  apply ha q
  refine SimpleGraph.Walk.IsCycle.mk ?_ ?_
  · refine SimpleGraph.Walk.IsCircuit.mk ?_ ?_
    · exact SimpleGraph.Walk.IsTrail.mk (hed ▸ hp.isTrail.edges_nodup)
    · intro hnil
      apply hp.ne_nil
      have : q.edges = [] := by rw [hnil]; rfl
      rw [hed] at this
      cases p with
      | nil => rfl
      | cons _ _ => simp at this
  · rw [hsup]
    exact hp.support_nodup

private lemma connected_deleteEdges_of_not_isAcyclic {W : Type} {H : SimpleGraph W}
    (hc : H.Connected) (hna : ¬ H.IsAcyclic) :
    ∃ e : H.edgeSet, (H.deleteEdges {e.val}).Connected := by
  unfold SimpleGraph.IsAcyclic at hna
  push Not at hna
  obtain ⟨v, p, hp⟩ := hna
  cases p with
  | nil => exact False.elim (hp.ne_nil rfl)
  | @cons _ u _ hadj q =>
    have hnodup := hp.isTrail.edges_nodup
    rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
    obtain ⟨q', _, _⟩ := walk_lift_deleteEdges q hnodup.1
    refine ⟨⟨s(v, u), (H.mem_edgeSet).mpr hadj⟩, ?_⟩
    have : Nonempty W := hc.nonempty
    refine ⟨fun x y => ?_⟩
    obtain ⟨w⟩ := hc x y
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab w ih =>
      by_cases heq : s(a, b) = s(v, u)
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (SimpleGraph.Walk.reachable q'.reverse).trans ih
        · exact (SimpleGraph.Walk.reachable q').trans ih
      · have hab' : (H.deleteEdges {s(v, u)}).Adj a b :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hab, heq⟩
        exact hab'.reachable.trans ih

private lemma sum_compGraph_edgeFinset_card {W : Type} [Fintype W] (G : SimpleGraph W) :
    ∑ C : G.ConnectedComponent, (compGraph G C).edgeFinset.card = G.edgeFinset.card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => Sym2.map Subtype.val p.2) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨a, b, hab⟩ : ∃ a b, p.2 = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) p.2
    rw [hab, SimpleGraph.mem_edgeFinset] at hp
    rw [hab, Sym2.map_mk, SimpleGraph.mem_edgeFinset]
    exact hp.2
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_sigma] at hp₁ hp₂
    obtain ⟨a₁, b₁, h1⟩ : ∃ a b, p₁.2 = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) p₁.2
    obtain ⟨a₂, b₂, h2⟩ : ∃ a b, p₂.2 = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) p₂.2
    rw [h1, h2, Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at heq
    have hCeq : p₁.1 = p₂.1 := by
      rcases heq with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact a₁.2.symm.trans (ha ▸ a₂.2)
      · exact a₁.2.symm.trans (ha ▸ b₂.2)
    cases p₁ with
    | mk C₁ e₁ =>
      cases p₂ with
      | mk C₂ e₂ =>
        dsimp only at hCeq h1 h2 heq
        subst hCeq
        congr 1
        rw [h1, h2, Sym2.eq_iff]
        rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨Subtype.ext ha, Subtype.ext hb⟩
        · exact Or.inr ⟨Subtype.ext ha, Subtype.ext hb⟩
  · intro e he
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
    have hadj : G.Adj a b := (G.mem_edgeFinset).mp he
    let C := G.connectedComponentMk a
    have hbC : G.connectedComponentMk b = C := SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable.symm
    refine ⟨⟨C, s(⟨a, rfl⟩, ⟨b, hbC⟩)⟩, ?_, rfl⟩
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_univ C, (compGraph G C).mem_edgeFinset.mpr hadj⟩

private lemma not_connected_of_not_connected {W : Type} [Fintype W]
    {G H : SimpleGraph W} (hNoIso : ∀ w : W, ∃ u : W, G.Adj w u)
    (hEH : EdgeHypomorphic G H) (hGnc : ¬ G.Connected) :
    ¬ H.Connected := by
  intro hHc
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := edgeFinset_card_eq_of_edgeHypomorphic hEH
  by_cases hHa : H.IsAcyclic
  · have hHtree : H.IsTree := ⟨hHc, hHa⟩
    have hcardH : H.edgeFinset.card + 1 = Fintype.card W := hHtree.card_edgeFinset
    have hGna : ¬ G.IsAcyclic := by
      intro hGa
      have hsum_e : ∑ C : G.ConnectedComponent, (compGraph G C).edgeFinset.card +
          Fintype.card G.ConnectedComponent = Fintype.card W := by
        have hcomp_tree : ∀ C : G.ConnectedComponent,
            (compGraph G C).edgeFinset.card + 1 =
              Fintype.card {w : W // G.connectedComponentMk w = C} := fun C =>
          SimpleGraph.IsTree.card_edgeFinset ⟨compGraph_connected G C, compGraph_isAcyclic hGa C⟩
        have hsum_v : ∑ C : G.ConnectedComponent,
            Fintype.card {w : W // G.connectedComponentMk w = C} = Fintype.card W := by
          simp_rw [Fintype.card_subtype]
          have := Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset W)) (t := Finset.univ) (g := G.connectedComponentMk)
            (f := fun _ => 1) (fun _ _ => Finset.mem_univ _)
          simpa using this
        calc
          ∑ C : G.ConnectedComponent, (compGraph G C).edgeFinset.card +
              Fintype.card G.ConnectedComponent
              = ∑ C : G.ConnectedComponent, ((compGraph G C).edgeFinset.card + 1) := by
                rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
          _ = ∑ C : G.ConnectedComponent, Fintype.card {w : W // G.connectedComponentMk w = C} :=
                Finset.sum_congr rfl fun C _ => hcomp_tree C
          _ = Fintype.card W := hsum_v
      rw [sum_compGraph_edgeFinset_card G] at hsum_e
      have h2comp : 2 ≤ Fintype.card G.ConnectedComponent := by
        have : Nonempty W := hHc.nonempty
        have hnotpre : ¬ G.Preconnected := fun hp => hGnc ⟨hp⟩
        unfold SimpleGraph.Preconnected at hnotpre
        push Not at hnotpre
        obtain ⟨x, y, hxy⟩ := hnotpre
        have hneC : G.connectedComponentMk x ≠ G.connectedComponentMk y :=
          fun heq => hxy (SimpleGraph.ConnectedComponent.eq.mp heq)
        have hsub : ({G.connectedComponentMk x, G.connectedComponentMk y} : Finset G.ConnectedComponent) ⊆
            Finset.univ := Finset.subset_univ _
        have hcard2 := Finset.card_le_card hsub
        rw [Finset.card_pair hneC, Finset.card_univ] at hcard2
        exact hcard2
      omega
    unfold SimpleGraph.IsAcyclic at hGna
    push Not at hGna
    obtain ⟨v₀, c, hc⟩ := hGna
    have hex_unreach : ∃ w₀ : W, ¬ G.Reachable v₀ w₀ := by
      by_contra hall
      push Not at hall
      have : Nonempty W := ⟨v₀⟩
      apply hGnc
      exact ⟨fun x y => (hall x).symm.trans (hall y)⟩
    obtain ⟨w₀, hw₀⟩ := hex_unreach
    obtain ⟨w₁, hadj_w⟩ := hNoIso w₀
    let e : G.edgeSet := ⟨s(w₀, w₁), (G.mem_edgeSet).mpr hadj_w⟩
    have he_not_c : e.1 ∉ c.edges := by
      intro hmem
      have hw0_sup : w₀ ∈ c.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges c hmem
      exact hw₀ ⟨c.takeUntil w₀ hw0_sup⟩
    have hdel_na : ¬ (G.deleteEdges {e.1}).IsAcyclic :=
      walk_lift_deleteEdges_isCycle c hc he_not_c
    obtain ⟨σ, hσ⟩ := hEH
    obtain ⟨φ⟩ := hσ e
    have hHdel_a : (H.deleteEdges {(σ e).1}).IsAcyclic :=
      hHa.anti (SimpleGraph.deleteEdges_le _)
    exact hdel_na (φ.isAcyclic_iff.mpr hHdel_a)
  · obtain ⟨e', he'_conn⟩ := connected_deleteEdges_of_not_isAcyclic hHc hHa
    obtain ⟨σ, hσ⟩ := hEH
    obtain ⟨φ⟩ := hσ (σ.symm e')
    have hGdel_conn : (G.deleteEdges {(σ.symm e').1}).Connected := by
      have φ' : G.deleteEdges {(σ.symm e').1} ≃g H.deleteEdges {e'.1} := by simpa using φ
      exact φ'.connected_iff.mpr he'_conn
    exact hGnc (hGdel_conn.mono (SimpleGraph.deleteEdges_le _))

private def actSubgraph_iso_of_iso {U V : Type}
    {G : SimpleGraph U} {H : SimpleGraph V} (φ : G ≃g H) :
    actSubgraph G ≃g actSubgraph H where
  toEquiv := Equiv.subtypeEquiv φ.toEquiv (fun x => by
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨φ u, φ.map_rel_iff.mpr hu⟩
    · rintro ⟨v, hv⟩
      exact ⟨φ.symm v, by
        have := φ.symm.map_rel_iff.mpr hv
        simpa using this⟩)
  map_rel_iff' := by
    intro a b
    exact φ.map_rel_iff

private lemma actSubgraph_edgeFinset_card {V : Type} (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype (actSubgraph G).edgeSet] :
    (actSubgraph G).edgeFinset.card = G.edgeFinset.card := by
  rw [← (actSubgraph G).card_edgeSet, ← G.card_edgeSet]
  exact Fintype.card_congr (edgeSet_actSubgraph_equiv G)

private def compSubCnt {U V : Type}
    (K : SimpleGraph U) (G : SimpleGraph V) [Fintype G.edgeSet] : ℕ :=
  edgeSubCnt G (fun S => Nonempty (actSubgraph S ≃g K))

private lemma compSubCnt_eq_of_iso {U V₁ V₂ : Type}
    (K : SimpleGraph U) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] (φ : G₁ ≃g G₂) :
    compSubCnt K G₁ = compSubCnt K G₂ := by
  unfold compSubCnt
  refine edgeSubCnt_eq_of_iso φ ?_
  intro S₁ S₂ ⟨ψ⟩
  have hact := actSubgraph_iso_of_iso ψ
  exact ⟨fun ⟨τ⟩ => ⟨hact.symm.trans τ⟩, fun ⟨τ⟩ => ⟨hact.trans τ⟩⟩

private lemma compSubCnt_eq_of_edgeHypomorphic {U W : Type} [Fintype W]
    (K : SimpleGraph U) [Fintype K.edgeSet]
    {G H : SimpleGraph W} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (hEH : EdgeHypomorphic G H)
    (hq : K.edgeFinset.card < G.edgeFinset.card) :
    compSubCnt K G = compSubCnt K H := by
  unfold compSubCnt
  refine edgeSubCnt_eq_of_edgeHypomorphic hEH _ K.edgeFinset.card ?_ ?_ hq
  · intro S₁ S₂ ⟨ψ⟩
    have hact := actSubgraph_iso_of_iso ψ
    exact ⟨fun ⟨τ⟩ => ⟨hact.symm.trans τ⟩, fun ⟨τ⟩ => ⟨hact.trans τ⟩⟩
  · intro S _ ⟨τ⟩
    have : Fintype (actSubgraph S).edgeSet := Fintype.ofEquiv S.edgeSet (edgeSet_actSubgraph_equiv S).symm
    rw [← actSubgraph_edgeFinset_card S, edgeFinset_card_eq_of_iso τ]

private lemma compSubCnt_le_card {U V : Type} [Fintype V]
    (K : SimpleGraph U) [Fintype K.edgeSet]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (hNoIso : ∀ v : V, ∃ u : V, G.Adj v u) :
    (G.edgeFinset.card < K.edgeFinset.card → compSubCnt K G = 0) ∧
    (G.edgeFinset.card = K.edgeFinset.card →
      compSubCnt K G = if Nonempty (G ≃g K) then 1 else 0) := by
  have hGact : Nonempty (actSubgraph G ≃g G) := by
    refine ⟨⟨Equiv.subtypeUnivEquiv hNoIso, ?_⟩⟩
    intro a b
    exact Iff.rfl
  constructor
  · intro hlt
    unfold compSubCnt edgeSubCnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro T hT ⟨φ⟩
    have hTsub : T ⊆ G.edgeFinset := Finset.mem_powerset.mp hT
    have hcard : T.card = K.edgeFinset.card := by
      rw [← edgeFinset_fromEdgeSet_of_subset hTsub, ← actSubgraph_edgeFinset_card,
        edgeFinset_card_eq_of_iso φ]
    have hle := Finset.card_le_card hTsub
    omega
  · intro heq
    unfold compSubCnt edgeSubCnt
    have hfilt : G.edgeFinset.powerset.filter
        (fun T : Finset (Sym2 V) => Nonempty (actSubgraph (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))) ≃g K)) =
        if Nonempty (G ≃g K) then {G.edgeFinset} else ∅ := by
      split_ifs with hGK
      · ext T
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · rintro ⟨hTsub, ⟨φ⟩⟩
          have hcard : T.card = K.edgeFinset.card := by
            rw [← edgeFinset_fromEdgeSet_of_subset hTsub, ← actSubgraph_edgeFinset_card,
              edgeFinset_card_eq_of_iso φ]
          exact Finset.eq_of_subset_of_card_le hTsub (by omega)
        · rintro rfl
          refine ⟨Finset.Subset.refl _, ?_⟩
          rw [fromEdgeSet_edgeFinset_eq]
          obtain ⟨φ₁⟩ := hGact
          obtain ⟨φ₂⟩ := hGK
          exact ⟨φ₁.trans φ₂⟩
      · rw [Finset.filter_eq_empty_iff]
        intro T hT ⟨φ⟩
        have hTsub : T ⊆ G.edgeFinset := Finset.mem_powerset.mp hT
        have hcard : T.card = K.edgeFinset.card := by
          rw [← edgeFinset_fromEdgeSet_of_subset hTsub, ← actSubgraph_edgeFinset_card,
            edgeFinset_card_eq_of_iso φ]
        have hTeq : T = G.edgeFinset := Finset.eq_of_subset_of_card_le hTsub (by omega)
        subst hTeq
        rw [fromEdgeSet_edgeFinset_eq] at φ
        obtain ⟨φ₁⟩ := hGact
        exact hGK ⟨φ₁.symm.trans φ⟩
    rw [hfilt]
    split_ifs <;> simp

private lemma actSubgraph_fromEdgeSet_image_subtype {W : Type} {P : W → Prop}
    (T₀ : Finset (Sym2 {w : W // P w})) :
    Nonempty (actSubgraph (SimpleGraph.fromEdgeSet (T₀ : Set (Sym2 {w : W // P w}))) ≃g
      actSubgraph (SimpleGraph.fromEdgeSet ((T₀.image (Sym2.map Subtype.val) : Finset (Sym2 W)) : Set (Sym2 W)))) := by
  set S₀ := SimpleGraph.fromEdgeSet (T₀ : Set (Sym2 {w : W // P w}))
  set T := T₀.image (Sym2.map Subtype.val)
  set S := SimpleGraph.fromEdgeSet (T : Set (Sym2 W))
  have hadj_iff : ∀ a b : {w : W // P w}, S.Adj a.1 b.1 ↔ S₀.Adj a b := by
    intro a b
    simp only [S, S₀, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, T, Finset.mem_image, ne_eq]
    constructor
    · rintro ⟨⟨e, he, hmap⟩, hne⟩
      have heq : s(a, b) = e := Sym2.map.injective Subtype.val_injective (by rw [Sym2.map_mk, hmap])
      exact ⟨heq ▸ he, fun h => hne (congrArg Subtype.val h)⟩
    · rintro ⟨hab, hne⟩
      exact ⟨⟨s(a, b), hab, rfl⟩, fun h => hne (Subtype.ext h)⟩
  have hzero_out : ∀ w : W, ¬ P w → ∀ u : W, ¬ S.Adj w u := by
    intro w hnw u hadj
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨e, _, hmap⟩ := Finset.mem_image.mp hadj.1
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨ha, _⟩ | ⟨_, hb⟩
    · exact hnw (ha ▸ a.2)
    · exact hnw (hb ▸ b.2)
  have hact_P : ∀ w : W, (∃ u : W, S.Adj w u) → P w := by
    rintro w ⟨u, hu⟩
    by_contra hnw
    exact hzero_out w hnw u hu
  have hact_deg : ∀ a : {w : W // P w}, (∃ b, S₀.Adj a b) ↔ (∃ u, S.Adj a.1 u) := by
    intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b.1, (hadj_iff a b).mpr hb⟩
    · rintro ⟨u, hu⟩
      have huP : P u := by
        by_contra hnu
        exact hzero_out u hnu a.1 hu.symm
      exact ⟨⟨u, huP⟩, (hadj_iff a ⟨u, huP⟩).mp hu⟩
  let f : {a : {w : W // P w} // ∃ b, S₀.Adj a b} → {w : W // ∃ u, S.Adj w u} :=
    fun x => ⟨x.1.1, (hact_deg x.1).mp x.2⟩
  let g : {w : W // ∃ u, S.Adj w u} → {a : {w : W // P w} // ∃ b, S₀.Adj a b} :=
    fun y => ⟨⟨y.1, hact_P y.1 y.2⟩, (hact_deg ⟨y.1, hact_P y.1 y.2⟩).mpr y.2⟩
  refine ⟨⟨⟨f, g, fun x => rfl, fun y => rfl⟩, ?_⟩⟩
  intro x y
  exact hadj_iff x.1 y.1

private lemma compSubCnt_eq_sum_components {U W : Type} [Fintype U] [Fintype W]
    (K : SimpleGraph U) (hKc : K.Connected) (hKe : 1 ≤ K.edgeFinset.card)
    (G : SimpleGraph W) :
    compSubCnt K G = ∑ C : G.ConnectedComponent, compSubCnt K (compGraph G C) := by
  unfold compSubCnt edgeSubCnt
  rw [← Finset.card_sigma]
  symm
  refine Finset.card_bij (fun p _ => p.2.image (Sym2.map Subtype.val)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma] at hp
    have hT0 := Finset.mem_filter.mp hp.2
    have hT0sub : p.2 ⊆ (compGraph G p.1).edgeFinset := Finset.mem_powerset.mp hT0.1
    obtain ⟨φ₁⟩ := actSubgraph_fromEdgeSet_image_subtype p.2
    obtain ⟨φ₂⟩ := hT0.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ⟨φ₁.symm.trans φ₂⟩⟩
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a, b, rfl⟩ : ∃ a b, e₀ = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₀
    have hadj : (compGraph G p.1).Adj a b := (compGraph G p.1).mem_edgeFinset.mp (hT0sub he₀)
    exact (G.mem_edgeFinset).mpr hadj
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_sigma] at hp₁ hp₂
    have hT1 := Finset.mem_filter.mp hp₁.2
    have hT1sub : p₁.2 ⊆ (compGraph G p₁.1).edgeFinset := Finset.mem_powerset.mp hT1.1
    obtain ⟨φ₁⟩ := hT1.2
    have hcard1 : p₁.2.card = K.edgeFinset.card := by
      rw [← edgeFinset_fromEdgeSet_of_subset hT1sub, ← actSubgraph_edgeFinset_card,
        edgeFinset_card_eq_of_iso φ₁]
    have hne1 : p₁.2.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e₁, he₁⟩ := hne1
    have hmem2 : Sym2.map Subtype.val e₁ ∈ p₂.2.image (Sym2.map Subtype.val) := by
      rw [← heq]
      exact Finset.mem_image_of_mem _ he₁
    obtain ⟨e₂, _, he12⟩ := Finset.mem_image.mp hmem2
    obtain ⟨a₁, b₁, rfl⟩ : ∃ a b, e₁ = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₁
    obtain ⟨a₂, b₂, rfl⟩ : ∃ a b, e₂ = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₂
    rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at he12
    have hCeq : p₁.1 = p₂.1 := by
      rcases he12 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact a₁.2.symm.trans (ha ▸ a₂.2)
      · exact a₁.2.symm.trans (hb ▸ b₂.2)
    cases p₁ with
    | mk C₁ T₁ =>
      cases p₂ with
      | mk C₂ T₂ =>
        dsimp only at hCeq heq
        subst hCeq
        congr 1
        ext e
        have hiff : Sym2.map Subtype.val e ∈ T₁.image (Sym2.map Subtype.val) ↔
            Sym2.map Subtype.val e ∈ T₂.image (Sym2.map Subtype.val) := by rw [heq]
        simpa [Finset.mem_image, (Sym2.map.injective Subtype.val_injective).eq_iff] using hiff
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTsub, ⟨φ⟩⟩ := hT
    set S := SimpleGraph.fromEdgeSet (T : Set (Sym2 W))
    have hTcard : T.card = K.edgeFinset.card := by
      rw [← edgeFinset_fromEdgeSet_of_subset hTsub, ← actSubgraph_edgeFinset_card,
        edgeFinset_card_eq_of_iso φ]
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e₀, he₀⟩ := hTne
    obtain ⟨x₀, y₀, rfl⟩ : ∃ a b, e₀ = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₀
    have hadj0 : S.Adj x₀ y₀ := by
      rw [← S.mem_edgeSet, edgeSet_fromEdgeSet_of_subset hTsub]
      exact he₀
    have hx0_act : ∃ u : W, S.Adj x₀ u := ⟨y₀, hadj0⟩
    let C : G.ConnectedComponent := G.connectedComponentMk x₀
    have hact_conn : (actSubgraph S).Connected := φ.connected_iff.mpr hKc
    have hall_C : ∀ x : W, (∃ u : W, S.Adj x u) → G.connectedComponentMk x = C := by
      intro x hx
      obtain ⟨p⟩ := hact_conn ⟨x₀, hx0_act⟩ ⟨x, hx⟩
      have hreachS : S.Reachable x₀ x :=
        ⟨p.map (SimpleGraph.Embedding.induce _).toHom⟩
      have hreachG : G.Reachable x₀ x :=
        hreachS.mono (fromEdgeSet_le_of_subset hTsub)
      exact SimpleGraph.ConnectedComponent.eq.mpr hreachG.symm
    have hT_in_C : ∀ e ∈ T, ∃ e₀ : Sym2 {w : W // G.connectedComponentMk w = C},
        Sym2.map Subtype.val e₀ = e ∧ e₀ ∈ (compGraph G C).edgeFinset := by
      intro e he
      obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
      have hadjS : S.Adj a b := by
        rw [← S.mem_edgeSet, edgeSet_fromEdgeSet_of_subset hTsub]
        exact he
      have haC : G.connectedComponentMk a = C := hall_C a ⟨b, hadjS⟩
      have hbC : G.connectedComponentMk b = C := hall_C b ⟨a, hadjS.symm⟩
      refine ⟨s(⟨a, haC⟩, ⟨b, hbC⟩), rfl, ?_⟩
      rw [SimpleGraph.mem_edgeFinset]
      exact fromEdgeSet_le_of_subset hTsub hadjS
    let T₀ : Finset (Sym2 {w : W // G.connectedComponentMk w = C}) :=
      (compGraph G C).edgeFinset.filter (fun e₀ => Sym2.map Subtype.val e₀ ∈ T)
    have hT0sub : T₀ ⊆ (compGraph G C).edgeFinset := Finset.filter_subset _ _
    have hT0img : T₀.image (Sym2.map Subtype.val) = T := by
      ext e
      simp only [Finset.mem_image, T₀, Finset.mem_filter]
      constructor
      · rintro ⟨e₀, ⟨_, heT⟩, rfl⟩
        exact heT
      · intro heT
        obtain ⟨e₀, rfl, he₀C⟩ := hT_in_C e heT
        exact ⟨e₀, ⟨he₀C, heT⟩, rfl⟩
    obtain ⟨φ₁⟩ := actSubgraph_fromEdgeSet_image_subtype T₀
    rw [hT0img] at φ₁
    refine ⟨⟨C, T₀⟩, ?_, hT0img⟩
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_univ C, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT0sub, ⟨φ₁.trans φ⟩⟩⟩

private lemma disconnected_iso {W : Type} [Fintype W]
    {G H : SimpleGraph W} (hE : 4 ≤ G.edgeFinset.card)
    (hNoIsoG : ∀ w : W, ∃ u : W, G.Adj w u) (hNoIsoH : ∀ w : W, ∃ u : W, H.Adj w u)
    (hEH : EdgeHypomorphic G H) (hGnc : ¬ G.Connected) :
    Nonempty (G ≃g H) := by
  have hHnc : ¬ H.Connected := not_connected_of_not_connected hNoIsoG hEH hGnc
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := edgeFinset_card_eq_of_edgeHypomorphic hEH
  set m := G.edgeFinset.card
  have hcomp_pos_G : ∀ C : G.ConnectedComponent, 1 ≤ (compGraph G C).edgeFinset.card := by
    intro C
    obtain ⟨w, hw⟩ := Quot.exists_rep C
    obtain ⟨u, hu⟩ := hNoIsoG w
    have huC : G.connectedComponentMk u = C :=
      (SimpleGraph.ConnectedComponent.eq.mpr hu.reachable.symm).trans hw
    exact Finset.card_pos.mpr ⟨s(⟨w, hw⟩, ⟨u, huC⟩), (compGraph G C).mem_edgeFinset.mpr hu⟩
  have hcomp_pos_H : ∀ D : H.ConnectedComponent, 1 ≤ (compGraph H D).edgeFinset.card := by
    intro D
    obtain ⟨w, hw⟩ := Quot.exists_rep D
    obtain ⟨u, hu⟩ := hNoIsoH w
    have huD : H.connectedComponentMk u = D :=
      (SimpleGraph.ConnectedComponent.eq.mpr hu.reachable.symm).trans hw
    exact Finset.card_pos.mpr ⟨s(⟨w, hw⟩, ⟨u, huD⟩), (compGraph H D).mem_edgeFinset.mpr hu⟩
  have hcomp_lt_G : ∀ C : G.ConnectedComponent, (compGraph G C).edgeFinset.card < m := by
    intro C
    have h2 : ∃ C' : G.ConnectedComponent, C' ≠ C := by
      by_contra hno
      push Not at hno
      obtain ⟨w₀, _⟩ := Quot.exists_rep C
      have : Nonempty W := ⟨w₀⟩
      apply hGnc
      exact ⟨fun x y => SimpleGraph.ConnectedComponent.eq.mp ((hno _).trans (hno _).symm)⟩
    obtain ⟨C', hne⟩ := h2
    have hsum := sum_compGraph_edgeFinset_card G
    have hle : (compGraph G C).edgeFinset.card + (compGraph G C').edgeFinset.card ≤
        ∑ X : G.ConnectedComponent, (compGraph G X).edgeFinset.card := by
      have hsub : ({C, C'} : Finset G.ConnectedComponent) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset hsub (f := fun X => (compGraph G X).edgeFinset.card)
      rwa [Finset.sum_pair hne.symm] at this
    have hpos' := hcomp_pos_G C'
    omega
  have hcomp_lt_H : ∀ D : H.ConnectedComponent, (compGraph H D).edgeFinset.card < m := by
    intro D
    have h2 : ∃ D' : H.ConnectedComponent, D' ≠ D := by
      by_contra hno
      push Not at hno
      obtain ⟨w₀, _⟩ := Quot.exists_rep D
      have : Nonempty W := ⟨w₀⟩
      apply hHnc
      exact ⟨fun x y => SimpleGraph.ConnectedComponent.eq.mp ((hno _).trans (hno _).symm)⟩
    obtain ⟨D', hne⟩ := h2
    have hsum := sum_compGraph_edgeFinset_card H
    have hle : (compGraph H D).edgeFinset.card + (compGraph H D').edgeFinset.card ≤
        ∑ X : H.ConnectedComponent, (compGraph H X).edgeFinset.card := by
      have hsub : ({D, D'} : Finset H.ConnectedComponent) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset hsub (f := fun X => (compGraph H X).edgeFinset.card)
      rwa [Finset.sum_pair hne.symm] at this
    have hpos' := hcomp_pos_H D'
    omega
  have hcomp_noIso_G : ∀ (C : G.ConnectedComponent) (x : {w : W // G.connectedComponentMk w = C}),
      ∃ y : {w : W // G.connectedComponentMk w = C}, (compGraph G C).Adj x y := by
    intro C x
    obtain ⟨u, hu⟩ := hNoIsoG x.1
    have huC : G.connectedComponentMk u = C :=
      (SimpleGraph.ConnectedComponent.eq.mpr hu.reachable.symm).trans x.2
    exact ⟨⟨u, huC⟩, hu⟩
  have hcomp_noIso_H : ∀ (D : H.ConnectedComponent) (x : {w : W // H.connectedComponentMk w = D}),
      ∃ y : {w : W // H.connectedComponentMk w = D}, (compGraph H D).Adj x y := by
    intro D x
    obtain ⟨u, hu⟩ := hNoIsoH x.1
    have huD : H.connectedComponentMk u = D :=
      (SimpleGraph.ConnectedComponent.eq.mpr hu.reachable.symm).trans x.2
    exact ⟨⟨u, huD⟩, hu⟩
  have hind : ∀ t : ℕ, ∀ {U : Type} [Fintype U] (K : SimpleGraph U),
      K.Connected → 1 ≤ K.edgeFinset.card → m - t ≤ K.edgeFinset.card →
      (Finset.univ.filter (fun C : G.ConnectedComponent => Nonempty (compGraph G C ≃g K))).card =
      (Finset.univ.filter (fun D : H.ConnectedComponent => Nonempty (compGraph H D ≃g K))).card := by
    intro t
    induction t with
    | zero =>
      intro U _ K _ _ hKge
      have h0G : (Finset.univ.filter (fun C : G.ConnectedComponent => Nonempty (compGraph G C ≃g K))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro C _ ⟨φ⟩
        have := edgeFinset_card_eq_of_iso φ
        have := hcomp_lt_G C
        omega
      have h0H : (Finset.univ.filter (fun D : H.ConnectedComponent => Nonempty (compGraph H D ≃g K))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro D _ ⟨φ⟩
        have := edgeFinset_card_eq_of_iso φ
        have := hcomp_lt_H D
        omega
      rw [h0G, h0H]
    | succ t ih =>
      intro U _ K hKc hKpos hKge
      by_cases hge : m - t ≤ K.edgeFinset.card
      · exact ih K hKc hKpos hge
      · have hKlt : K.edgeFinset.card < m := by omega
        have hkelly : compSubCnt K G = compSubCnt K H :=
          compSubCnt_eq_of_edgeHypomorphic K hEH hKlt
        rw [compSubCnt_eq_sum_components K hKc hKpos G,
          compSubCnt_eq_sum_components K hKc hKpos H] at hkelly
        let SG := Finset.univ.filter (fun C : G.ConnectedComponent => K.edgeFinset.card < (compGraph G C).edgeFinset.card)
        let SH := Finset.univ.filter (fun D : H.ConnectedComponent => K.edgeFinset.card < (compGraph H D).edgeFinset.card)
        have hsplitG : ∑ C : G.ConnectedComponent, compSubCnt K (compGraph G C) =
            (Finset.univ.filter (fun C : G.ConnectedComponent => Nonempty (compGraph G C ≃g K))).card +
            ∑ C ∈ SG, compSubCnt K (compGraph G C) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun C : G.ConnectedComponent => K.edgeFinset.card < (compGraph G C).edgeFinset.card)]
          rw [add_comm]
          congr 1
          have hle_sum : ∑ C ∈ Finset.univ.filter (fun C : G.ConnectedComponent =>
              ¬ (K.edgeFinset.card < (compGraph G C).edgeFinset.card)), compSubCnt K (compGraph G C) =
              ∑ C ∈ Finset.univ.filter (fun C : G.ConnectedComponent =>
                ¬ (K.edgeFinset.card < (compGraph G C).edgeFinset.card)),
                if Nonempty (compGraph G C ≃g K) then 1 else 0 := by
            refine Finset.sum_congr rfl fun C hC => ?_
            have hle : (compGraph G C).edgeFinset.card ≤ K.edgeFinset.card := by
              have := (Finset.mem_filter.mp hC).2
              omega
            by_cases hlt : (compGraph G C).edgeFinset.card < K.edgeFinset.card
            · rw [(compSubCnt_le_card K (compGraph G C) (hcomp_noIso_G C)).1 hlt]
              rw [if_neg]
              rintro ⟨φ⟩
              have := edgeFinset_card_eq_of_iso φ
              omega
            · exact (compSubCnt_le_card K (compGraph G C) (hcomp_noIso_G C)).2 (by omega)
          rw [hle_sum, Finset.sum_boole, Nat.cast_id]
          congr 1
          ext C
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          constructor
          · exact fun h => h.2
          · rintro ⟨φ⟩
            exact ⟨le_of_eq (edgeFinset_card_eq_of_iso φ), ⟨φ⟩⟩
        have hsplitH : ∑ D : H.ConnectedComponent, compSubCnt K (compGraph H D) =
            (Finset.univ.filter (fun D : H.ConnectedComponent => Nonempty (compGraph H D ≃g K))).card +
            ∑ D ∈ SH, compSubCnt K (compGraph H D) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun D : H.ConnectedComponent => K.edgeFinset.card < (compGraph H D).edgeFinset.card)]
          rw [add_comm]
          congr 1
          have hle_sum : ∑ D ∈ Finset.univ.filter (fun D : H.ConnectedComponent =>
              ¬ (K.edgeFinset.card < (compGraph H D).edgeFinset.card)), compSubCnt K (compGraph H D) =
              ∑ D ∈ Finset.univ.filter (fun D : H.ConnectedComponent =>
                ¬ (K.edgeFinset.card < (compGraph H D).edgeFinset.card)),
                if Nonempty (compGraph H D ≃g K) then 1 else 0 := by
            refine Finset.sum_congr rfl fun D hD => ?_
            have hle : (compGraph H D).edgeFinset.card ≤ K.edgeFinset.card := by
              have := (Finset.mem_filter.mp hD).2
              omega
            by_cases hlt : (compGraph H D).edgeFinset.card < K.edgeFinset.card
            · rw [(compSubCnt_le_card K (compGraph H D) (hcomp_noIso_H D)).1 hlt]
              rw [if_neg]
              rintro ⟨φ⟩
              have := edgeFinset_card_eq_of_iso φ
              omega
            · exact (compSubCnt_le_card K (compGraph H D) (hcomp_noIso_H D)).2 (by omega)
          rw [hle_sum, Finset.sum_boole, Nat.cast_id]
          congr 1
          ext D
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          constructor
          · exact fun h => h.2
          · rintro ⟨φ⟩
            exact ⟨le_of_eq (edgeFinset_card_eq_of_iso φ), ⟨φ⟩⟩
        have hgt_eq : ∑ C ∈ SG, compSubCnt K (compGraph G C) =
            ∑ D ∈ SH, compSubCnt K (compGraph H D) := by
          obtain ⟨e, he⟩ := exists_iso_equiv_of_finset_count_eq
            (fun C : G.ConnectedComponent => compGraph G C)
            (fun D : H.ConnectedComponent => compGraph H D)
            SG.card SG SH rfl
            (fun C hC => by
              have hCgt : K.edgeFinset.card < (compGraph G C).edgeFinset.card :=
                (Finset.mem_filter.mp hC).2
              have h1 : SG.filter (fun C' => Nonempty (compGraph G C' ≃g compGraph G C)) =
                  Finset.univ.filter (fun C' => Nonempty (compGraph G C' ≃g compGraph G C)) := by
                ext C'
                simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hCgt, ⟨φ⟩⟩⟩
              have h2 : SH.filter (fun D => Nonempty (compGraph H D ≃g compGraph G C)) =
                  Finset.univ.filter (fun D => Nonempty (compGraph H D ≃g compGraph G C)) := by
                ext D
                simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hCgt, ⟨φ⟩⟩⟩
              rw [h1, h2]
              exact ih (compGraph G C) (compGraph_connected G C) (hcomp_pos_G C) (by omega))
            (fun D hD => by
              have hDgt : K.edgeFinset.card < (compGraph H D).edgeFinset.card :=
                (Finset.mem_filter.mp hD).2
              have h1 : SG.filter (fun C => Nonempty (compGraph G C ≃g compGraph H D)) =
                  Finset.univ.filter (fun C => Nonempty (compGraph G C ≃g compGraph H D)) := by
                ext C
                simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hDgt, ⟨φ⟩⟩⟩
              have h2 : SH.filter (fun D' => Nonempty (compGraph H D' ≃g compGraph H D)) =
                  Finset.univ.filter (fun D' => Nonempty (compGraph H D' ≃g compGraph H D)) := by
                ext D'
                simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hDgt, ⟨φ⟩⟩⟩
              rw [h1, h2]
              exact ih (compGraph H D) (compGraph_connected H D) (hcomp_pos_H D) (by omega))
          refine Finset.sum_bij (fun C hC => (e ⟨C, hC⟩).1) ?_ ?_ ?_ ?_
          · intro C hC
            exact (e ⟨C, hC⟩).2
          · intro C₁ hC₁ C₂ hC₂ heq
            exact congrArg Subtype.val (e.injective (Subtype.ext heq))
          · intro D hD
            exact ⟨(e.symm ⟨D, hD⟩).1, (e.symm ⟨D, hD⟩).2, congrArg Subtype.val (e.apply_symm_apply ⟨D, hD⟩)⟩
          · intro C hC
            obtain ⟨φ⟩ := he ⟨C, hC⟩
            exact compSubCnt_eq_of_iso K φ
        rw [hsplitG, hsplitH, hgt_eq] at hkelly
        omega
  obtain ⟨eComp, heComp⟩ := exists_iso_equiv_of_count_eq
    (fun C : G.ConnectedComponent => compGraph G C)
    (fun D : H.ConnectedComponent => compGraph H D)
    (fun C => hind m (compGraph G C) (compGraph_connected G C) (hcomp_pos_G C) (by omega))
    (fun D => hind m (compGraph H D) (compGraph_connected H D) (hcomp_pos_H D) (by omega))
  let ψ : ∀ C : G.ConnectedComponent, compGraph G C ≃g compGraph H (eComp C) :=
    fun C => Classical.choice (heComp C)
  let f : W → W := fun w => (ψ (G.connectedComponentMk w) ⟨w, rfl⟩).1
  let g : W → W := fun y => ((ψ (eComp.symm (H.connectedComponentMk y))).symm
    ⟨y, by rw [eComp.apply_symm_apply]⟩).1
  have hf_comp : ∀ w : W, H.connectedComponentMk (f w) = eComp (G.connectedComponentMk w) :=
    fun w => (ψ (G.connectedComponentMk w) ⟨w, rfl⟩).2
  have hg_comp : ∀ y : W, G.connectedComponentMk (g y) = eComp.symm (H.connectedComponentMk y) :=
    fun y => ((ψ (eComp.symm (H.connectedComponentMk y))).symm ⟨y, by rw [eComp.apply_symm_apply]⟩).2
  have hfg : ∀ w : W, g (f w) = w := by
    intro w
    dsimp only [g]
    have hC : eComp.symm (H.connectedComponentMk (f w)) = G.connectedComponentMk w := by
      rw [hf_comp, eComp.symm_apply_apply]
    generalize_proofs hp1
    have hsub : ∀ (C₁ C₂ : G.ConnectedComponent) (hEq : C₁ = C₂)
        (a : {y : W // H.connectedComponentMk y = eComp C₁})
        (b : {y : W // H.connectedComponentMk y = eComp C₂}),
        a.1 = b.1 → ((ψ C₁).symm a).1 = ((ψ C₂).symm b).1 := by
      rintro C₁ _ rfl a b hab
      rw [Subtype.ext hab]
    have hstep := hsub (eComp.symm (H.connectedComponentMk (f w))) (G.connectedComponentMk w) hC
      ⟨f w, hp1⟩ (ψ (G.connectedComponentMk w) ⟨w, rfl⟩) rfl
    rw [hstep]
    exact congrArg Subtype.val ((ψ (G.connectedComponentMk w)).symm_apply_apply ⟨w, rfl⟩)
  have hgf : ∀ y : W, f (g y) = y := by
    intro y
    dsimp only [f]
    have hC : G.connectedComponentMk (g y) = eComp.symm (H.connectedComponentMk y) := hg_comp y
    have hsub : ∀ (C₁ C₂ : G.ConnectedComponent) (hEq : C₁ = C₂)
        (a : {w : W // G.connectedComponentMk w = C₁})
        (b : {w : W // G.connectedComponentMk w = C₂}),
        a.1 = b.1 → (ψ C₁ a).1 = (ψ C₂ b).1 := by
      rintro C₁ _ rfl a b hab
      rw [Subtype.ext hab]
    have hstep := hsub (G.connectedComponentMk (g y)) (eComp.symm (H.connectedComponentMk y)) hC
      ⟨g y, rfl⟩ ((ψ (eComp.symm (H.connectedComponentMk y))).symm ⟨y, by rw [eComp.apply_symm_apply]⟩) rfl
    rw [hstep]
    exact congrArg Subtype.val ((ψ (eComp.symm (H.connectedComponentMk y))).apply_symm_apply _)
  refine ⟨⟨⟨f, g, hfg, hgf⟩, ?_⟩⟩
  intro x y
  change H.Adj (f x) (f y) ↔ G.Adj x y
  constructor
  · intro hadj
    have hcompH : H.connectedComponentMk (f x) = H.connectedComponentMk (f y) :=
      SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
    rw [hf_comp, hf_comp] at hcompH
    have hcompG : G.connectedComponentMk x = G.connectedComponentMk y := eComp.injective hcompH
    let C := G.connectedComponentMk x
    have hfy : f y = (ψ C ⟨y, hcompG.symm⟩).1 := by
      dsimp only [f]
      have hsub : ∀ (C₁ C₂ : G.ConnectedComponent) (hEq : C₁ = C₂)
          (a : {w : W // G.connectedComponentMk w = C₁})
          (b : {w : W // G.connectedComponentMk w = C₂}),
          a.1 = b.1 → (ψ C₁ a).1 = (ψ C₂ b).1 := by
        rintro C₁ _ rfl a b hab
        rw [Subtype.ext hab]
      exact hsub (G.connectedComponentMk y) C hcompG.symm ⟨y, rfl⟩ ⟨y, hcompG.symm⟩ rfl
    have hadjC : (compGraph H (eComp C)).Adj (ψ C ⟨x, rfl⟩) (ψ C ⟨y, hcompG.symm⟩) := by
      change H.Adj (f x) (ψ C ⟨y, hcompG.symm⟩).1
      rwa [← hfy]
    exact (ψ C).map_rel_iff.mp hadjC
  · intro hadj
    have hcompG : G.connectedComponentMk x = G.connectedComponentMk y :=
      SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
    let C := G.connectedComponentMk x
    have hfy : f y = (ψ C ⟨y, hcompG.symm⟩).1 := by
      dsimp only [f]
      have hsub : ∀ (C₁ C₂ : G.ConnectedComponent) (hEq : C₁ = C₂)
          (a : {w : W // G.connectedComponentMk w = C₁})
          (b : {w : W // G.connectedComponentMk w = C₂}),
          a.1 = b.1 → (ψ C₁ a).1 = (ψ C₂ b).1 := by
        rintro C₁ _ rfl a b hab
        rw [Subtype.ext hab]
      exact hsub (G.connectedComponentMk y) C hcompG.symm ⟨y, rfl⟩ ⟨y, hcompG.symm⟩ rfl
    rw [hfy]
    exact (ψ C).map_rel_iff.mpr (show (compGraph G C).Adj ⟨x, rfl⟩ ⟨y, hcompG.symm⟩ from hadj)

end DisconnectedCase

section GreenwellTheorem

private def addIso {U : Type} (X : SimpleGraph U) : SimpleGraph (Option U) where
  Adj a b :=
    match a, b with
    | some x, some y => X.Adj x y
    | _, _ => False
  symm := ⟨fun a b h => by
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun a h => by
    cases a
    · exact h
    · exact X.loopless.irrefl _ h⟩

private lemma addIso_no_adj_none {U : Type} (X : SimpleGraph U) (u : Option U) :
    ¬ (addIso X).Adj none u := by
  cases u <;> simp [addIso]

private lemma addIso_isoCount {U : Type} [Fintype U] (X : SimpleGraph U) :
    isoCount (addIso X) = isoCount X + 1 := by
  unfold isoCount
  have hmem : none ∈ Finset.univ.filter (fun y : Option U => ∀ z, ¬ (addIso X).Adj y z) := by
    simp [addIso_no_adj_none]
  rw [← Finset.card_erase_add_one hmem]
  congr 1
  refine Finset.card_bij (fun y hy => y.get (by
    cases y with
    | none => exact False.elim ((Finset.mem_erase.mp hy).1 rfl)
    | some _ => rfl)) ?_ ?_ ?_
  · intro y hy
    cases y with
    | none => exact False.elim ((Finset.mem_erase.mp hy).1 rfl)
    | some u =>
      have h0 := (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).2
      simp only [Option.get_some, Finset.mem_filter, Finset.mem_univ, true_and]
      intro z hz
      exact h0 (some z) hz
  · intro y₁ hy₁ y₂ hy₂ heq
    cases y₁ with
    | none => exact False.elim ((Finset.mem_erase.mp hy₁).1 rfl)
    | some u₁ =>
      cases y₂ with
      | none => exact False.elim ((Finset.mem_erase.mp hy₂).1 rfl)
      | some u₂ =>
        simp only [Option.get_some] at heq
        rw [heq]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨some u, ?_, rfl⟩
    simp only [Finset.mem_erase, ne_eq, reduceCtorEq, not_false_eq_true, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro z hz
    cases z with
    | none => simp [addIso] at hz
    | some w => exact hu w hz

private lemma addIso_edgeFinset_card {U : Type} [Fintype U] (X : SimpleGraph U) :
    (addIso X).edgeFinset.card = X.edgeFinset.card := by
  symm
  refine Finset.card_bij (fun e _ => Sym2.map Option.some e) ?_ ?_ ?_
  · intro e he
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
    have hadj : X.Adj a b := (X.mem_edgeFinset).mp he
    rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset]
    exact hadj
  · intro e₁ _ e₂ _ h
    exact Sym2.map.injective (Option.some_injective U) h
  · intro e he
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
    have hadj : (addIso X).Adj a b := (addIso X).mem_edgeFinset.mp he
    cases a with
    | none => simp [addIso] at hadj
    | some x =>
      cases b with
      | none => simp [addIso] at hadj
      | some y =>
        exact ⟨s(x, y), (X.mem_edgeFinset).mpr hadj, rfl⟩

private def swap_isolated_aut {V : Type} (A : SimpleGraph V)
    {x y : V} (hx : ∀ z, ¬ A.Adj x z) (hy : ∀ z, ¬ A.Adj y z) :
    A ≃g A where
  toEquiv := Equiv.swap x y
  map_rel_iff' := by
    intro a b
    by_cases hax : a = x
    · subst hax
      rw [Equiv.swap_apply_left]
      exact iff_of_false (hy _) (hx _)
    · by_cases hay : a = y
      · subst hay
        rw [Equiv.swap_apply_right]
        exact iff_of_false (hx _) (hy _)
      · rw [Equiv.swap_apply_of_ne_of_ne hax hay]
        by_cases hbx : b = x
        · subst hbx
          rw [Equiv.swap_apply_left]
          exact iff_of_false (fun h => hy _ h.symm) (fun h => hx _ h.symm)
        · by_cases hby : b = y
          · subst hby
            rw [Equiv.swap_apply_right]
            exact iff_of_false (fun h => hx _ h.symm) (fun h => hy _ h.symm)
          · rw [Equiv.swap_apply_of_ne_of_ne hbx hby]

private lemma iso_addIso_iff_of_isolated {U W : Type}
    {S : SimpleGraph W} {X : SimpleGraph U} {v : W} (hv : ∀ u : W, ¬ S.Adj v u) :
    Nonempty (S ≃g addIso X) ↔ Nonempty (S.induce {v}ᶜ ≃g X) := by
  constructor
  · rintro ⟨ψ⟩
    have hψv_iso : ∀ z : Option U, ¬ (addIso X).Adj (ψ v) z := by
      intro z hz
      have h1 : S.Adj v (ψ.symm z) := by
        rw [← ψ.map_rel_iff, ψ.apply_symm_apply]
        exact hz
      exact hv (ψ.symm z) h1
    let ψ' : S ≃g addIso X := ψ.trans (swap_isolated_aut (addIso X) hψv_iso (addIso_no_adj_none X))
    have hψ'v : ψ' v = none := by
      simp [ψ', swap_isolated_aut]
    have hsome : ∀ x : ({v}ᶜ : Set W), (ψ' x.1).isSome := by
      intro x
      cases h : ψ' x.1 with
      | none =>
        have hxv : x.1 = v := ψ'.injective (h.trans hψ'v.symm)
        exact False.elim (x.2 hxv)
      | some _ => rfl
    let f : ({v}ᶜ : Set W) → U := fun x => (ψ' x.1).get (hsome x)
    have hne_v : ∀ u : U, ψ'.symm (some u) ≠ v := by
      intro u heq
      have := congrArg ψ' heq
      rw [ψ'.apply_symm_apply, hψ'v] at this
      exact Option.some_ne_none u this
    let g : U → ({v}ᶜ : Set W) := fun u => ⟨ψ'.symm (some u), hne_v u⟩
    have hfg : ∀ x, g (f x) = x := by
      intro x
      apply Subtype.ext
      dsimp only [f, g]
      rw [Option.some_get]
      exact ψ'.symm_apply_apply x.1
    have hgf : ∀ u, f (g u) = u := by
      intro u
      dsimp only [f, g]
      have h1 : ψ' (ψ'.symm (some u)) = some u := ψ'.apply_symm_apply (some u)
      exact Option.some.inj ((Option.some_get (hsome (g u))).trans h1)
    refine ⟨⟨⟨f, g, hfg, hgf⟩, ?_⟩⟩
    intro x y
    have hx : ψ' x.1 = some (f x) := (Option.some_get (hsome x)).symm
    have hy : ψ' y.1 = some (f y) := (Option.some_get (hsome y)).symm
    have hrel := ψ'.map_rel_iff (a := x.1) (b := y.1)
    rw [hx, hy] at hrel
    exact hrel
  · rintro ⟨φ⟩
    let f : W → Option U := fun w =>
      if hw : w = v then none else some (φ ⟨w, hw⟩)
    let g : Option U → W := fun o =>
      match o with
      | none => v
      | some u => (φ.symm u).1
    have hfg : ∀ w, g (f w) = w := by
      intro w
      dsimp only [f, g]
      split_ifs with hw
      · exact hw.symm
      · exact congrArg Subtype.val (φ.symm_apply_apply ⟨w, hw⟩)
    have hgf : ∀ o, f (g o) = o := by
      intro o
      cases o with
      | none => simp [f, g]
      | some u =>
        dsimp only [f, g]
        have hne : (φ.symm u).1 ≠ v := (φ.symm u).2
        rw [dif_neg hne]
        exact congrArg some (φ.apply_symm_apply u)
    refine ⟨⟨⟨f, g, hfg, hgf⟩, ?_⟩⟩
    intro x y
    change (addIso X).Adj (f x) (f y) ↔ S.Adj x y
    dsimp only [f]
    by_cases hx : x = v
    · subst hx
      rw [dif_pos rfl]
      exact iff_of_false (addIso_no_adj_none X _) (hv y)
    · rw [dif_neg hx]
      by_cases hy : y = v
      · subst hy
        rw [dif_pos rfl]
        exact iff_of_false (by simp [addIso]) (fun h => hv x h.symm)
      · rw [dif_neg hy]
        exact φ.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)

private def spanSubCnt {U V : Type}
    (X : SimpleGraph U) (G : SimpleGraph V) [Fintype G.edgeSet] : ℕ :=
  edgeSubCnt G (fun S => Nonempty (S ≃g X))

private lemma spanSubCnt_eq_of_iso {U V₁ V₂ : Type}
    (X : SimpleGraph U) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] (φ : G₁ ≃g G₂) :
    spanSubCnt X G₁ = spanSubCnt X G₂ := by
  unfold spanSubCnt
  refine edgeSubCnt_eq_of_iso φ ?_
  intro S₁ S₂ ⟨ψ⟩
  exact ⟨fun ⟨τ⟩ => ⟨ψ.symm.trans τ⟩, fun ⟨τ⟩ => ⟨ψ.trans τ⟩⟩

private lemma spanSubCnt_eq_of_edgeHypomorphic {U W : Type} [Fintype W]
    (X : SimpleGraph U) [Fintype X.edgeSet]
    {G H : SimpleGraph W} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (hEH : EdgeHypomorphic G H)
    (hq : X.edgeFinset.card < G.edgeFinset.card) :
    spanSubCnt X G = spanSubCnt X H := by
  unfold spanSubCnt
  refine edgeSubCnt_eq_of_edgeHypomorphic hEH _ X.edgeFinset.card ?_ ?_ hq
  · intro S₁ S₂ ⟨ψ⟩
    exact ⟨fun ⟨τ⟩ => ⟨ψ.symm.trans τ⟩, fun ⟨τ⟩ => ⟨ψ.trans τ⟩⟩
  · intro S _ ⟨τ⟩
    exact edgeFinset_card_eq_of_iso τ

private lemma spanSubCnt_le_card {U V : Type}
    (X : SimpleGraph U) [Fintype X.edgeSet]
    (G : SimpleGraph V) [Fintype G.edgeSet] :
    (G.edgeFinset.card < X.edgeFinset.card → spanSubCnt X G = 0) ∧
    (G.edgeFinset.card = X.edgeFinset.card →
      spanSubCnt X G = if Nonempty (G ≃g X) then 1 else 0) := by
  constructor
  · intro hlt
    unfold spanSubCnt edgeSubCnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro T hT ⟨φ⟩
    have hTsub : T ⊆ G.edgeFinset := Finset.mem_powerset.mp hT
    have : Fintype (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).edgeSet :=
      Fintype.ofEquiv X.edgeSet φ.symm.mapEdgeSet
    have hcard : T.card = X.edgeFinset.card := by
      rw [← edgeFinset_fromEdgeSet_of_subset hTsub, edgeFinset_card_eq_of_iso φ]
    have hle := Finset.card_le_card hTsub
    omega
  · intro heq
    unfold spanSubCnt edgeSubCnt
    have hfilt : G.edgeFinset.powerset.filter
        (fun T : Finset (Sym2 V) => Nonempty (SimpleGraph.fromEdgeSet (T : Set (Sym2 V)) ≃g X)) =
        if Nonempty (G ≃g X) then {G.edgeFinset} else ∅ := by
      split_ifs with hGX
      · ext T
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · rintro ⟨hTsub, ⟨φ⟩⟩
          have : Fintype (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).edgeSet :=
            Fintype.ofEquiv X.edgeSet φ.symm.mapEdgeSet
          have hcard : T.card = X.edgeFinset.card := by
            rw [← edgeFinset_fromEdgeSet_of_subset hTsub, edgeFinset_card_eq_of_iso φ]
          exact Finset.eq_of_subset_of_card_le hTsub (by omega)
        · rintro rfl
          rw [fromEdgeSet_edgeFinset_eq]
          exact ⟨Finset.Subset.refl _, hGX⟩
      · rw [Finset.filter_eq_empty_iff]
        intro T hT ⟨φ⟩
        have hTsub : T ⊆ G.edgeFinset := Finset.mem_powerset.mp hT
        have : Fintype (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).edgeSet :=
          Fintype.ofEquiv X.edgeSet φ.symm.mapEdgeSet
        have hcard : T.card = X.edgeFinset.card := by
          rw [← edgeFinset_fromEdgeSet_of_subset hTsub, edgeFinset_card_eq_of_iso φ]
        have hTeq : T = G.edgeFinset := Finset.eq_of_subset_of_card_le hTsub (by omega)
        subst hTeq
        rw [fromEdgeSet_edgeFinset_eq] at φ
        exact hGX ⟨φ⟩
    rw [hfilt]
    split_ifs <;> simp

private lemma greenwell_double_count {U W : Type} [Fintype U] [Fintype W]
    (X : SimpleGraph U) (G : SimpleGraph W) :
    (isoCount X + 1) * spanSubCnt (addIso X) G =
      ∑ v : W, spanSubCnt X (G.induce {v}ᶜ) := by
  let S₀ : Finset (Finset (Sym2 W)) := G.edgeFinset.powerset.filter
    (fun T : Finset (Sym2 W) => Nonempty (SimpleGraph.fromEdgeSet (T : Set (Sym2 W)) ≃g addIso X))
  let r : Finset (Sym2 W) → W → Prop :=
    fun T v => ∀ u : W, ¬ (SimpleGraph.fromEdgeSet (T : Set (Sym2 W))).Adj v u
  have hlhs : (isoCount X + 1) * spanSubCnt (addIso X) G =
      ∑ T ∈ S₀, (Finset.bipartiteAbove r Finset.univ T).card := by
    have hconst : ∀ T ∈ S₀, (Finset.bipartiteAbove r Finset.univ T).card = isoCount X + 1 := by
      intro T hT
      obtain ⟨φ⟩ := (Finset.mem_filter.mp hT).2
      have hEq : isoCount (SimpleGraph.fromEdgeSet (T : Set (Sym2 W))) = isoCount X + 1 := by
        rw [isoCount_eq_of_iso φ, addIso_isoCount]
      rw [← hEq]
      unfold isoCount
      simp only [Finset.bipartiteAbove, r]
      exact Finset.card_bij (fun v _ => v) (fun v hv => by simpa using hv)
        (fun _ _ _ _ h => h) (fun v hv => ⟨v, by simpa using hv, rfl⟩)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    rfl
  rw [hlhs, Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finset.bipartiteBelow, r]
  unfold spanSubCnt edgeSubCnt
  symm
  refine Finset.card_bij (fun (T₀ : Finset (Sym2 ({v}ᶜ : Set W))) _ => T₀.image (Sym2.map Subtype.val)) ?_ ?_ ?_
  · intro T₀ hT₀
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT₀
    obtain ⟨hT0sub, ⟨φ⟩⟩ := hT₀
    set T : Finset (Sym2 W) := T₀.image (Sym2.map Subtype.val)
    have hTsub : T ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨a, b, rfl⟩ : ∃ a b, e₀ = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₀
      exact (G.mem_edgeFinset).mpr ((G.induce {v}ᶜ).mem_edgeFinset.mp (hT0sub he₀))
    have hisov : ∀ u : W, ¬ (SimpleGraph.fromEdgeSet (T : Set (Sym2 W))).Adj v u := by
      intro u hadj
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      obtain ⟨e₀, _, hmap⟩ := Finset.mem_image.mp hadj.1
      obtain ⟨a, b, rfl⟩ : ∃ a b, e₀ = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₀
      rw [Sym2.map_mk, Sym2.eq_iff] at hmap
      rcases hmap with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact a.2 ha
      · exact b.2 hb
    have hind_eq : (SimpleGraph.fromEdgeSet (T : Set (Sym2 W))).induce {v}ᶜ =
        SimpleGraph.fromEdgeSet (T₀ : Set (Sym2 ({v}ᶜ : Set W))) := by
      ext a b
      simp only [SimpleGraph.induce_adj, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, T,
        Finset.mem_image, ne_eq]
      constructor
      · rintro ⟨⟨e₀, he₀, hmap⟩, hne⟩
        have heq : s(a, b) = e₀ := Sym2.map.injective Subtype.val_injective (by rw [Sym2.map_mk, hmap])
        exact ⟨heq ▸ he₀, fun h => hne (congrArg Subtype.val h)⟩
      · rintro ⟨hab, hne⟩
        exact ⟨⟨s(a, b), hab, rfl⟩, fun h => hne (Subtype.ext h)⟩
    have hiso : Nonempty (SimpleGraph.fromEdgeSet (T : Set (Sym2 W)) ≃g addIso X) := by
      rw [iso_addIso_iff_of_isolated hisov, hind_eq]
      exact ⟨φ⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTsub, hiso⟩, hisov⟩
  · intro T₁ _ T₂ _ h
    ext e
    have hiff : Sym2.map Subtype.val e ∈ T₁.image (Sym2.map Subtype.val) ↔
        Sym2.map Subtype.val e ∈ T₂.image (Sym2.map Subtype.val) := by rw [h]
    simpa [Finset.mem_image, (Sym2.map.injective Subtype.val_injective).eq_iff] using hiff
  · intro T hT
    simp only [S₀, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨⟨hTsub, hiso⟩, hisov⟩ := hT
    let T₀ : Finset (Sym2 ({v}ᶜ : Set W)) :=
      (G.induce {v}ᶜ).edgeFinset.filter (fun e₀ => Sym2.map Subtype.val e₀ ∈ T)
    have hT0sub : T₀ ⊆ (G.induce {v}ᶜ).edgeFinset := Finset.filter_subset _ _
    have hT0img : T₀.image (Sym2.map Subtype.val) = T := by
      ext e
      simp only [Finset.mem_image, T₀, Finset.mem_filter]
      constructor
      · rintro ⟨e₀, ⟨_, heT⟩, rfl⟩
        exact heT
      · intro heT
        obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
        have hadjS : (SimpleGraph.fromEdgeSet (T : Set (Sym2 W))).Adj a b := by
          rw [← SimpleGraph.mem_edgeSet, edgeSet_fromEdgeSet_of_subset hTsub]
          exact heT
        have hav : a ≠ v := fun h => hisov b (h ▸ hadjS)
        have hbv : b ≠ v := fun h => hisov a (h ▸ hadjS.symm)
        have hadjG : G.Adj a b := fromEdgeSet_le_of_subset hTsub hadjS
        exact ⟨s(⟨a, hav⟩, ⟨b, hbv⟩), ⟨(G.induce {v}ᶜ).mem_edgeFinset.mpr hadjG, heT⟩, rfl⟩
    have hind_eq : (SimpleGraph.fromEdgeSet (T : Set (Sym2 W))).induce {v}ᶜ =
        SimpleGraph.fromEdgeSet (T₀ : Set (Sym2 ({v}ᶜ : Set W))) := by
      rw [← hT0img]
      ext a b
      simp only [SimpleGraph.induce_adj, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
        Finset.mem_image, ne_eq]
      constructor
      · rintro ⟨⟨e₀, he₀, hmap⟩, hne⟩
        have heq : s(a, b) = e₀ := Sym2.map.injective Subtype.val_injective (by rw [Sym2.map_mk, hmap])
        exact ⟨heq ▸ he₀, fun h => hne (congrArg Subtype.val h)⟩
      · rintro ⟨hab, hne⟩
        exact ⟨⟨s(a, b), hab, rfl⟩, fun h => hne (Subtype.ext h)⟩
    have hiso₀ : Nonempty (SimpleGraph.fromEdgeSet (T₀ : Set (Sym2 ({v}ᶜ : Set W))) ≃g X) := by
      rw [← hind_eq]
      exact (iso_addIso_iff_of_isolated hisov).mp hiso
    exact ⟨T₀, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT0sub, hiso₀⟩, hT0img⟩

private lemma induce_compl_edgeFinset_card_lt {W : Type} [Fintype W] (G : SimpleGraph W)
    (v : W) (hv : ∃ u : W, G.Adj v u) :
    (G.induce {v}ᶜ).edgeFinset.card < G.edgeFinset.card := by
  have hcard : (G.induce {v}ᶜ).edgeFinset.card = (G.edgeFinset \ G.incidenceFinset v).card := by
    refine Finset.card_bij (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_
    · intro e he
      obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
      have hadj : G.Adj a.1 b.1 := (G.induce {v}ᶜ).mem_edgeFinset.mp he
      rw [Sym2.map_mk, Finset.mem_sdiff]
      refine ⟨(G.mem_edgeFinset).mpr hadj, fun hinc => ?_⟩
      have hmem := (G.mem_incidenceFinset v _).mp hinc |>.2
      rw [Sym2.mem_iff] at hmem
      rcases hmem with h | h
      · exact a.2 h.symm
      · exact b.2 h.symm
    · intro e₁ _ e₂ _ h
      exact Sym2.map.injective Subtype.val_injective h
    · intro e he
      rw [Finset.mem_sdiff] at he
      obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
      have hadj : G.Adj a b := (G.mem_edgeFinset).mp he.1
      have hav : a ≠ v := fun h => he.2 ((G.mem_incidenceFinset v _).mpr ⟨hadj, by simp [h]⟩)
      have hbv : b ≠ v := fun h => he.2 ((G.mem_incidenceFinset v _).mpr ⟨hadj, by simp [h]⟩)
      exact ⟨s(⟨a, hav⟩, ⟨b, hbv⟩), (G.induce {v}ᶜ).mem_edgeFinset.mpr hadj, rfl⟩
  rw [hcard, Finset.card_sdiff_of_subset (G.incidenceFinset_subset v), G.card_incidenceFinset_eq_degree]
  have hle := degree_le_edgeFinset_card G v
  have hpos : 0 < G.degree v := (degree_pos_iff_exists_adj G v).mpr hv
  omega

private lemma sum_spanSubCnt_induce_compl {U W : Type} [Fintype U] [Fintype W]
    (X : SimpleGraph U) (G : SimpleGraph W) :
    ∑ v : W, spanSubCnt X (G.induce {v}ᶜ) =
      (Finset.univ.filter (fun v : W => Nonempty (G.induce {v}ᶜ ≃g X))).card +
      ∑ v ∈ Finset.univ.filter (fun v : W => X.edgeFinset.card < (G.induce {v}ᶜ).edgeFinset.card),
        spanSubCnt X (G.induce {v}ᶜ) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v : W => X.edgeFinset.card < (G.induce {v}ᶜ).edgeFinset.card), add_comm]
  refine congrArg (· + _) ?_
  have hle_sum : ∑ v ∈ Finset.univ.filter (fun v : W =>
      ¬ (X.edgeFinset.card < (G.induce {v}ᶜ).edgeFinset.card)),
      spanSubCnt X (G.induce {v}ᶜ) =
      ∑ v ∈ Finset.univ.filter (fun v : W =>
        ¬ (X.edgeFinset.card < (G.induce {v}ᶜ).edgeFinset.card)),
        if Nonempty (G.induce {v}ᶜ ≃g X) then 1 else 0 := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hle : (G.induce {v}ᶜ).edgeFinset.card ≤ X.edgeFinset.card := by
      have := (Finset.mem_filter.mp hv).2
      omega
    by_cases hlt : (G.induce {v}ᶜ).edgeFinset.card < X.edgeFinset.card
    · rw [(spanSubCnt_le_card X (G.induce {v}ᶜ)).1 hlt]
      rw [if_neg]
      rintro ⟨φ⟩
      have := edgeFinset_card_eq_of_iso φ
      omega
    · exact (spanSubCnt_le_card X (G.induce {v}ᶜ)).2 (by omega)
  rw [hle_sum, Finset.sum_boole, Nat.cast_id]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  constructor
  · exact fun h => h.2
  · rintro ⟨φ⟩
    exact ⟨le_of_eq (edgeFinset_card_eq_of_iso φ), ⟨φ⟩⟩

private lemma greenwell_hypomorphic {W : Type} [Fintype W]
    {G H : SimpleGraph W}
    (hNoIsoG : ∀ w : W, ∃ u : W, G.Adj w u) (hNoIsoH : ∀ w : W, ∃ u : W, H.Adj w u)
    (hEH : EdgeHypomorphic G H) :
    Hypomorphic G H := by
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := edgeFinset_card_eq_of_edgeHypomorphic hEH
  set m := G.edgeFinset.card
  have hltG : ∀ v : W, (G.induce {v}ᶜ).edgeFinset.card < m := fun v =>
    induce_compl_edgeFinset_card_lt G v (hNoIsoG v)
  have hltH : ∀ v : W, (H.induce {v}ᶜ).edgeFinset.card < m := fun v => by
    rw [hm_eq]
    exact induce_compl_edgeFinset_card_lt H v (hNoIsoH v)
  have hind : ∀ t : ℕ, ∀ {U : Type} [Fintype U] (X : SimpleGraph U),
      m - t ≤ X.edgeFinset.card →
      (Finset.univ.filter (fun v : W => Nonempty (G.induce {v}ᶜ ≃g X))).card =
      (Finset.univ.filter (fun w : W => Nonempty (H.induce {w}ᶜ ≃g X))).card := by
    intro t
    induction t with
    | zero =>
      intro U _ X hXge
      have h0G : (Finset.univ.filter (fun v : W => Nonempty (G.induce {v}ᶜ ≃g X))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro v _ ⟨φ⟩
        have := edgeFinset_card_eq_of_iso φ
        have := hltG v
        omega
      have h0H : (Finset.univ.filter (fun w : W => Nonempty (H.induce {w}ᶜ ≃g X))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w _ ⟨φ⟩
        have := edgeFinset_card_eq_of_iso φ
        have := hltH w
        omega
      rw [h0G, h0H]
    | succ t ih =>
      intro U _ X hXge
      by_cases hge : m - t ≤ X.edgeFinset.card
      · exact ih X hge
      · have hXlt : X.edgeFinset.card < m := by omega
        have hkelly : spanSubCnt (addIso X) G = spanSubCnt (addIso X) H := by
          refine spanSubCnt_eq_of_edgeHypomorphic (addIso X) hEH ?_
          rw [addIso_edgeFinset_card]
          exact hXlt
        have hdc : ∑ v : W, spanSubCnt X (G.induce {v}ᶜ) =
            ∑ w : W, spanSubCnt X (H.induce {w}ᶜ) := by
          rw [← greenwell_double_count X G, ← greenwell_double_count X H, hkelly]
        let SG := Finset.univ.filter (fun v : W => X.edgeFinset.card < (G.induce {v}ᶜ).edgeFinset.card)
        let SH := Finset.univ.filter (fun w : W => X.edgeFinset.card < (H.induce {w}ᶜ).edgeFinset.card)
        have hsplitG := sum_spanSubCnt_induce_compl X G
        have hsplitH := sum_spanSubCnt_induce_compl X H
        have hgt_eq : ∑ v ∈ SG, spanSubCnt X (G.induce {v}ᶜ) =
            ∑ w ∈ SH, spanSubCnt X (H.induce {w}ᶜ) := by
          obtain ⟨e, he⟩ := exists_iso_equiv_of_finset_count_eq
            (fun v : W => G.induce {v}ᶜ)
            (fun w : W => H.induce {w}ᶜ)
            SG.card SG SH rfl
            (fun v hv => by
              have hvgt : X.edgeFinset.card < (G.induce {v}ᶜ).edgeFinset.card :=
                (Finset.mem_filter.mp hv).2
              have h1 : SG.filter (fun v' => Nonempty (G.induce {v'}ᶜ ≃g G.induce {v}ᶜ)) =
                  Finset.univ.filter (fun v' => Nonempty (G.induce {v'}ᶜ ≃g G.induce {v}ᶜ)) := by
                ext v'
                simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hvgt, ⟨φ⟩⟩⟩
              have h2 : SH.filter (fun w => Nonempty (H.induce {w}ᶜ ≃g G.induce {v}ᶜ)) =
                  Finset.univ.filter (fun w => Nonempty (H.induce {w}ᶜ ≃g G.induce {v}ᶜ)) := by
                ext w
                simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hvgt, ⟨φ⟩⟩⟩
              rw [h1, h2]
              exact ih (G.induce {v}ᶜ) (by
                simp_rw [← ncard_edgeSet_eq_card_edgeFinset] at hvgt hXge hge ⊢
                omega))
            (fun w hw => by
              have hwgt : X.edgeFinset.card < (H.induce {w}ᶜ).edgeFinset.card :=
                (Finset.mem_filter.mp hw).2
              have h1 : SG.filter (fun v => Nonempty (G.induce {v}ᶜ ≃g H.induce {w}ᶜ)) =
                  Finset.univ.filter (fun v => Nonempty (G.induce {v}ᶜ ≃g H.induce {w}ᶜ)) := by
                ext v
                simp only [SG, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hwgt, ⟨φ⟩⟩⟩
              have h2 : SH.filter (fun w' => Nonempty (H.induce {w'}ᶜ ≃g H.induce {w}ᶜ)) =
                  Finset.univ.filter (fun w' => Nonempty (H.induce {w'}ᶜ ≃g H.induce {w}ᶜ)) := by
                ext w'
                simp only [SH, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨fun h => h.2, fun ⟨φ⟩ => ⟨by rw [edgeFinset_card_eq_of_iso φ]; exact hwgt, ⟨φ⟩⟩⟩
              rw [h1, h2]
              exact ih (H.induce {w}ᶜ) (by
                simp_rw [← ncard_edgeSet_eq_card_edgeFinset] at hwgt hXge hge ⊢
                omega))
          refine Finset.sum_bij (fun v hv => (e ⟨v, hv⟩).1) ?_ ?_ ?_ ?_
          · intro v hv
            exact (e ⟨v, hv⟩).2
          · intro v₁ hv₁ v₂ hv₂ heq
            exact congrArg Subtype.val (e.injective (Subtype.ext heq))
          · intro w hw
            exact ⟨(e.symm ⟨w, hw⟩).1, (e.symm ⟨w, hw⟩).2, congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)⟩
          · intro v hv
            obtain ⟨φ⟩ := he ⟨v, hv⟩
            exact spanSubCnt_eq_of_iso X φ
        rw [hsplitG, hsplitH] at hdc
        change _ + ∑ v ∈ SG, spanSubCnt X (G.induce {v}ᶜ) =
          _ + ∑ w ∈ SH, spanSubCnt X (H.induce {w}ᶜ) at hdc
        omega
  exact exists_iso_equiv_of_count_eq
    (fun v : W => G.induce {v}ᶜ)
    (fun w : W => H.induce {w}ᶜ)
    (fun v => hind m (G.induce {v}ᶜ) (by omega))
    (fun w => hind m (H.induce {w}ᶜ) (by omega))

end GreenwellTheorem

private lemma main_proof :
    OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1.H1 := by
  intro V _ G H hE hEH
  have hEG : 4 ≤ G.edgeFinset.card := by rwa [← ncard_edgeSet_eq_card_edgeFinset]
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := edgeFinset_card_eq_of_edgeHypomorphic hEH
  by_cases hGstar : ∃ v : V, G.degree v = G.edgeFinset.card
  · obtain ⟨v, hv⟩ := hGstar
    exact Or.inl (star_edge_reconstructible hEG hEH hv)
  · by_cases hHstar : ∃ w : V, H.degree w = H.edgeFinset.card
    · obtain ⟨w, hw⟩ := hHstar
      obtain ⟨φ⟩ := star_edge_reconstructible (hm_eq ▸ hEG) (edgeHypomorphic_symm hEH) hw
      exact Or.inl ⟨φ.symm⟩
    · have hGlt : ∀ v : V, G.degree v < G.edgeFinset.card := fun v =>
        lt_of_le_of_ne (degree_le_edgeFinset_card G v) (fun heq => hGstar ⟨v, heq⟩)
      have hHlt : ∀ w : V, H.degree w < H.edgeFinset.card := fun w =>
        lt_of_le_of_ne (degree_le_edgeFinset_card H w) (fun heq => hHstar ⟨w, heq⟩)
      have hiso_eq : isoCount G = isoCount H := by
        rw [isoCount_eq_card_degree_zero G, isoCount_eq_card_degree_zero H]
        exact degCount_eq_of_not_star hEH hGlt hHlt 0
      obtain ⟨W, _, G', H', h4W, hE', hNoIsoG, hNoIsoH, hEH', hLift⟩ :=
        strip_isolates hEG hEH hiso_eq
      by_cases hConn : G'.Connected
      · refine Or.inr ⟨W, inferInstance, G', H', h4W, hE', hConn, hNoIsoG, hEH', ?_, hLift⟩
        exact greenwell_hypomorphic hNoIsoG hNoIsoH hEH'
      · have hE'f : 4 ≤ G'.edgeFinset.card := by rwa [← ncard_edgeSet_eq_card_edgeFinset]
        exact Or.inl (hLift (disconnected_iso hE'f hNoIsoG hNoIsoH hEH' hConn))

end

end OMA.H1Proof

theorem OMA.solution : OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1.H1 :=
  OMA.H1Proof.main_proof
