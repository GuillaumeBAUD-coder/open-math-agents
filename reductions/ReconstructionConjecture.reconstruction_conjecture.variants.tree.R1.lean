import FormalConjectures.Wikipedia.ReconstructionConjecture

/-!
Reduction `ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1` of Kelly's theorem
for trees. Proves Kelly's edge-count, degree-sequence, acyclicity, and tree-recognition lemmas
in-file, reducing the conjecture to four modular subgoals: path/degree-le-2 trees, Kelly's
induced-subgraph counting lemma, central (even diameter) non-path trees, and bicentral (odd
diameter) non-path trees.
-/

-- Reduction ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1 of Trees are reconstructible
-- Credit: @green-notes
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1

open SimpleGraph ReconstructionConjecture

-- Pillar 1: Any two finite trees on the same number of vertices >= 3 with all degrees <= 2
-- (paths) are isomorphic.
def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V → Fintype.card V = Fintype.card W →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      G.IsTree → H.IsTree →
      (∀ v : V, (G.neighborSet v).ncard ≤ 2) →
      (∀ w : W, (H.neighborSet w).ncard ≤ 2) →
      Nonempty (G ≃g H)

-- Pillar 2: Kelly's induced-subgraph counting lemma for hypomorphic trees.
def H2 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      G.IsTree → H.IsTree → Hypomorphic G H →
      ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard

-- Pillar 3: Central (even diameter) non-path hypomorphic trees with matching degrees and
-- induced-subgraph counts are isomorphic.
def H3 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Even G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      Nonempty (G ≃g H)

-- Pillar 4: Bicentral (odd diameter) non-path hypomorphic trees with matching degrees and
-- induced-subgraph counts are isomorphic.
def H4 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Odd G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      Nonempty (G ≃g H)

section KellyRecognition

open Classical

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (Z : SimpleGraph U) (u : U) :
    (Z.neighborSet u).ncard = Z.degree u := by
  rw [← Z.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (Z.neighborSet u)]
  simp [Set.toFinset_card]

private lemma sum_card_edgeFinset_induce_compl {U : Type} [Fintype U] (Z : SimpleGraph U) :
    (∑ u : U, (Z.induce {u}ᶜ).edgeFinset.card) + 2 * Z.edgeFinset.card =
      Fintype.card U * Z.edgeFinset.card := by
  have hsingle : ∀ u : U, (Z.induce {u}ᶜ).edgeFinset.card + Z.degree u = Z.edgeFinset.card := by
    intro u
    rw [Z.card_edgeFinset_induce_compl_singleton u, Z.card_edgeFinset_deleteIncidenceSet u]
    have hle : Z.degree u ≤ Z.edgeFinset.card := Z.degree_le_card_edgeFinset u
    omega
  have hsum : (∑ u : U, (Z.induce {u}ᶜ).edgeFinset.card) + (∑ u : U, Z.degree u) =
      ∑ _u : U, Z.edgeFinset.card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => hsingle u
  rw [Z.sum_degrees_eq_twice_card_edges, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  exact hsum

private lemma kelly_tree_recognition {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hTG : G.IsTree) (σ : V ≃ W)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) :
    H.IsTree ∧ ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hW : 3 ≤ Fintype.card W := hcard ▸ hV
  have hsum_eq :
      (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) =
        ∑ w : W, (H.induce {w}ᶜ).edgeFinset.card := by
    rw [← Equiv.sum_comp σ (fun w : W => (H.induce {w}ᶜ).edgeFinset.card)]
    refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨φ⟩ := hσ v
    exact Iso.card_edgeFinset_eq φ
  have hSG := sum_card_edgeFinset_induce_compl G
  have hSH := sum_card_edgeFinset_induce_compl H
  have hm_eq : G.edgeFinset.card = H.edgeFinset.card := by
    have hmul : (Fintype.card V - 2) * G.edgeFinset.card =
        (Fintype.card V - 2) * H.edgeFinset.card := by
      have h1 : (Fintype.card V - 2) * G.edgeFinset.card + 2 * G.edgeFinset.card =
          Fintype.card V * G.edgeFinset.card := by
        calc
          (Fintype.card V - 2) * G.edgeFinset.card + 2 * G.edgeFinset.card
            = (Fintype.card V - 2 + 2) * G.edgeFinset.card := (Nat.add_mul _ _ _).symm
          _ = Fintype.card V * G.edgeFinset.card := by rw [Nat.sub_add_cancel (by omega)]
      have h2 : (Fintype.card V - 2) * H.edgeFinset.card + 2 * H.edgeFinset.card =
          Fintype.card W * H.edgeFinset.card := by
        calc
          (Fintype.card V - 2) * H.edgeFinset.card + 2 * H.edgeFinset.card
            = (Fintype.card V - 2 + 2) * H.edgeFinset.card := (Nat.add_mul _ _ _).symm
          _ = Fintype.card W * H.edgeFinset.card := by rw [Nat.sub_add_cancel (by omega), hcard]
      omega
    exact Nat.mul_left_cancel (by omega) hmul
  have hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard := by
    intro v
    rw [ncard_neighborSet_eq_degree, ncard_neighborSet_eq_degree]
    have h1 : (G.induce {v}ᶜ).edgeFinset.card + G.degree v = G.edgeFinset.card := by
      rw [G.card_edgeFinset_induce_compl_singleton v, G.card_edgeFinset_deleteIncidenceSet v]
      have hle : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
      omega
    have h2 : (H.induce {σ v}ᶜ).edgeFinset.card + H.degree (σ v) = H.edgeFinset.card := by
      rw [H.card_edgeFinset_induce_compl_singleton (σ v), H.card_edgeFinset_deleteIncidenceSet (σ v)]
      have hle : H.degree (σ v) ≤ H.edgeFinset.card := H.degree_le_card_edgeFinset (σ v)
      omega
    obtain ⟨φ⟩ := hσ v
    have hc_eq : (G.induce {v}ᶜ).edgeFinset.card = (H.induce {σ v}ᶜ).edgeFinset.card :=
      Iso.card_edgeFinset_eq φ
    omega
  have hmG : G.edgeFinset.card + 1 = Fintype.card V := hTG.card_edgeFinset
  have hmH : H.edgeFinset.card + 1 = Fintype.card W := by omega
  have hHA : H.IsAcyclic := by
    intro w c hc_cyc
    by_cases hmiss : ∃ z : W, z ∉ c.support
    · obtain ⟨z, hz⟩ := hmiss
      have hw_supp : ∀ x ∈ c.support, x ∈ ({z}ᶜ : Set W) := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl
        exact hz hx
      have hc'_cyc : (c.induce ({z}ᶜ : Set W) hw_supp).IsCycle :=
        Walk.IsCycle.of_map (f := (Embedding.induce ({z}ᶜ : Set W)).toHom)
          (by rw [Walk.map_induce]; exact hc_cyc)
      let v := σ.symm z
      obtain ⟨φ⟩ := hσ v
      have hsz : σ v = z := σ.apply_symm_apply z
      have hA_H : (H.induce {z}ᶜ).IsAcyclic := by
        rw [← hsz, ← φ.isAcyclic_iff]
        exact hTG.isAcyclic.induce {v}ᶜ
      exact hA_H (c.induce ({z}ᶜ : Set W) hw_supp) hc'_cyc
    · push Not at hmiss
      have hmem_tail : ∀ z : W, z ∈ c.support.tail := by
        intro z
        have hz := hmiss z
        have hcons : c.support = w :: c.support.tail := by
          cases c with
          | nil => exact False.elim (hc_cyc.ne_nil rfl)
          | cons _ _ => rfl
        rw [hcons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact c.end_mem_tail_support hc_cyc.not_nil
        · exact hz
      have hcard_le : Fintype.card W ≤ c.support.tail.length := by
        calc
          Fintype.card W = (Finset.univ : Finset W).card := rfl
          _ ≤ c.support.tail.toFinset.card := by
            refine Finset.card_le_card fun z _ => ?_
            exact List.mem_toFinset.mpr (hmem_tail z)
          _ = c.support.tail.length := List.toFinset_card_of_nodup hc_cyc.support_nodup
      have hlen_tail : c.support.tail.length = c.length := by
        have hls := c.length_support
        have hne : c.support ≠ [] := by simp
        have hcons : c.support = w :: c.support.tail := by
          cases c with
          | nil => exact False.elim (hc_cyc.ne_nil rfl)
          | cons _ _ => rfl
        have := congrArg List.length hcons
        simp only [List.length_cons] at this
        omega
      have hedges_le : c.edges.length ≤ H.edgeFinset.card := by
        calc
          c.edges.length = c.edges.toFinset.card :=
            (List.toFinset_card_of_nodup hc_cyc.isTrail.edges_nodup).symm
          _ ≤ H.edgeFinset.card := by
            refine Finset.card_le_card fun e he => ?_
            rw [List.mem_toFinset] at he
            exact (H.mem_edgeFinset).mpr (c.edges_subset_edgeSet he)
      have hedges_len : c.edges.length = c.length := c.length_edges
      omega
  have hHC : H.Connected := by
    let f : (Σ c : H.ConnectedComponent, c.toSimpleGraph.edgeSet) → H.edgeSet :=
      fun ⟨c, e⟩ => ⟨e.val.map Subtype.val, by
        rcases e with ⟨e, he⟩
        obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, rfl⟩ : ∃ a b : c.supp, e = s(a, b) :=
          Sym2.ind (fun a b => ⟨a, b, rfl⟩) e
        dsimp only
        rw [Sym2.map_mk, mem_edgeSet]
        exact (c.toSimpleGraph.mem_edgeSet).mp he⟩
    have hfinj : Function.Injective f := by
      rintro ⟨c₁, ⟨e₁, he₁⟩⟩ ⟨c₂, ⟨e₂, he₂⟩⟩ hfe
      have heq_map : e₁.map Subtype.val = e₂.map Subtype.val := congrArg Subtype.val hfe
      obtain ⟨⟨u₁, hu₁⟩, ⟨v₁, hv₁⟩, rfl⟩ : ∃ a b : c₁.supp, e₁ = s(a, b) :=
        Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₁
      obtain ⟨⟨u₂, hu₂⟩, ⟨v₂, hv₂⟩, rfl⟩ : ∃ a b : c₂.supp, e₂ = s(a, b) :=
        Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₂
      rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at heq_map
      have hc_eq : c₁ = c₂ := by
        rcases heq_map with ⟨h1, _⟩ | ⟨h1, _⟩
        · dsimp only at h1
          exact ConnectedComponent.eq_of_common_vertex hu₁ (h1 ▸ hu₂)
        · dsimp only at h1
          exact ConnectedComponent.eq_of_common_vertex hu₁ (h1 ▸ hv₂)
      subst hc_eq
      congr 1
      apply Subtype.ext
      rw [Sym2.eq_iff]
      rcases heq_map with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have hfsurj : Function.Surjective f := by
      rintro ⟨e, he⟩
      obtain ⟨u, v, rfl⟩ : ∃ u v : W, e = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e
      have hadj : H.Adj u v := (H.mem_edgeSet).mp he
      let c := H.connectedComponentMk u
      have hu : u ∈ c.supp := rfl
      have hv : v ∈ c.supp := (ConnectedComponent.mem_supp_congr_adj c hadj).mp hu
      have he' : s(⟨u, hu⟩, ⟨v, hv⟩) ∈ c.toSimpleGraph.edgeSet := by
        rw [c.toSimpleGraph.mem_edgeSet]
        exact hadj
      refine ⟨⟨c, ⟨s(⟨u, hu⟩, ⟨v, hv⟩), he'⟩⟩, ?_⟩
      apply Subtype.ext
      dsimp only [f]
      rw [Sym2.map_mk]
    let Esum : ℕ := ∑ c : H.ConnectedComponent, Fintype.card c.toSimpleGraph.edgeSet
    have hsum_edges : Esum = H.edgeFinset.card := by
      dsimp only [Esum]
      rw [← Fintype.card_sigma, ← H.card_edgeSet]
      exact Fintype.card_of_bijective ⟨hfinj, hfsurj⟩
    have hv_eq : (∑ c : H.ConnectedComponent, Fintype.card c) = Fintype.card W := by
      rw [← Fintype.card_sigma]
      refine Fintype.card_congr
        ⟨fun ⟨_, ⟨w, _⟩⟩ => w, fun w => ⟨H.connectedComponentMk w, ⟨w, rfl⟩⟩, ?_, ?_⟩
      · rintro ⟨c, ⟨w, hw⟩⟩
        have hcw : H.connectedComponentMk w = c := (ConnectedComponent.mem_supp_iff c w).mp hw
        subst hcw
        rfl
      · intro w
        rfl
    have htree_sum : Esum + Fintype.card H.ConnectedComponent = Fintype.card W := by
      calc
        Esum + Fintype.card H.ConnectedComponent
          = ∑ c : H.ConnectedComponent, (Fintype.card c.toSimpleGraph.edgeSet + 1) := by
            dsimp only [Esum]
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
        _ = ∑ c : H.ConnectedComponent, Fintype.card c := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [c.toSimpleGraph.card_edgeSet]
            exact (hHA.isTree_connectedComponent c).card_edgeFinset
        _ = Fintype.card W := hv_eq
    have hcc_le : Fintype.card H.ConnectedComponent ≤ 1 := by omega
    have hss : Subsingleton H.ConnectedComponent :=
      Fintype.card_le_one_iff_subsingleton.mp hcc_le
    have : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    exact Connected.mk fun u v =>
      ConnectedComponent.exact (Subsingleton.elim (H.connectedComponentMk u) (H.connectedComponentMk v))
  exact ⟨⟨hHC, hHA⟩, hdeg⟩

end KellyRecognition

theorem main : H1 → H2 → H3 → H4 → type_of% @ReconstructionConjecture.reconstruction_conjecture.variants.tree := by
  intro h1 h2 h3 h4 V W _ _ hV G H hc ha h
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨hTH, hdeg⟩ := kelly_tree_recognition hV G H ⟨hc, ha⟩ σ hσ
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  by_cases hpath : ∀ v : V, (G.neighborSet v).ncard ≤ 2
  · have hpathH : ∀ w : W, (H.neighborSet w).ncard ≤ 2 := by
      intro w
      rw [← σ.apply_symm_apply w, ← hdeg (σ.symm w)]
      exact hpath (σ.symm w)
    exact h1 hV hcard G H ⟨hc, ha⟩ hTH hpath hpathH
  · push Not at hpath
    have hsub : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard :=
      h2 hV G H ⟨hc, ha⟩ hTH ⟨σ, hσ⟩
    rcases Nat.even_or_odd G.diam with heven | hodd
    · exact h3 hV G H σ ⟨hc, ha⟩ hTH hσ hdeg hpath heven hsub
    · exact h4 hV G H σ ⟨hc, ha⟩ hTH hσ hdeg hpath hodd hsub

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1
