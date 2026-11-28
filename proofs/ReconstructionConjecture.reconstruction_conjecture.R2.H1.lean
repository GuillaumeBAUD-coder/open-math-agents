import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_R2

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

This proof is adapted from the Palomar-registered formalization
VictorLiwentao/fc-palomar-proofs at FCPalomar/Reconstruction/Solution.lean,
ported to Lean 4.33.1 and the pinned Mathlib of this repository.
-/

/-!
# Disconnected graphs are reconstructible (Kelly 1957)

Proof of `OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2.H1`,
via Kelly's lemma, connectivity recognition, and a peeling induction.
-/

namespace ReconstructionDisconnected

open SimpleGraph ReconstructionConjecture

section Embeddings

variable {U V W : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The number of induced embeddings of `F` into `G` with image in `P`. -/
noncomputable def emb (F : SimpleGraph U) (G : SimpleGraph V) (P : Set V) : ℕ :=
  Nat.card {f : F ↪g G // ∀ u, f u ∈ P}

lemma finite_embedding [Finite U] [Finite V] : Finite (F ↪g G) :=
  Finite.of_injective _ DFunLike.coe_injective

/-- An embedding with image in `P`, as an embedding into `G.induce P`. -/
def restrict (f : F ↪g G) {P : Set V} (hf : ∀ u, f u ∈ P) : F ↪g G.induce P where
  toFun u := ⟨f u, hf u⟩
  inj' _ _ h := f.injective (congrArg Subtype.val h)
  map_rel_iff' := f.map_rel_iff

/-- Push an embedding with image in `P` through `G.induce P ≃g H.induce Q`. -/
def transport {P : Set V} {Q : Set W} (φ : G.induce P ≃g H.induce Q) (f : F ↪g G)
    (hf : ∀ u, f u ∈ P) : F ↪g H :=
  (Embedding.induce Q).comp (φ.toEmbedding.comp (restrict f hf))

lemma transport_apply {P : Set V} {Q : Set W} (φ : G.induce P ≃g H.induce Q) (f : F ↪g G)
    (hf : ∀ u, f u ∈ P) (u : U) : transport φ f hf u = (φ ⟨f u, hf u⟩ : W) := rfl

/-- Isomorphic induced subgraphs have the same embedding counts. -/
lemma emb_eq_of_iso {P : Set V} {Q : Set W} (φ : G.induce P ≃g H.induce Q)
    (F : SimpleGraph U) : emb F G P = emb F H Q := by
  refine Nat.card_congr
    { toFun := fun f => ⟨transport φ f.1 f.2, fun u => (φ ⟨f.1 u, f.2 u⟩).2⟩
      invFun := fun g => ⟨transport φ.symm g.1 g.2, fun u => (φ.symm ⟨g.1 u, g.2 u⟩).2⟩
      left_inv := fun f => ?_
      right_inv := fun g => ?_ }
  · refine Subtype.ext (DFunLike.ext _ _ fun u => ?_)
    simp only [transport_apply, Subtype.coe_eta, RelIso.symm_apply_apply]
  · refine Subtype.ext (DFunLike.ext _ _ fun u => ?_)
    simp only [transport_apply, Subtype.coe_eta, RelIso.apply_symm_apply]

lemma emb_univ (F : SimpleGraph U) (G : SimpleGraph V) :
    emb F G Set.univ = Nat.card (F ↪g G) :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun _ _ => Set.mem_univ _)

/-- **Kelly's lemma** for induced embeddings. -/
lemma sum_emb_compl_singleton [Fintype U] [Fintype V] [DecidableEq V] (F : SimpleGraph U)
    (G : SimpleGraph V) :
    ∑ v, emb F G {v}ᶜ = (Fintype.card V - Fintype.card U) * Nat.card (F ↪g G) := by
  classical
  have : Finite (F ↪g G) := finite_embedding
  let : Fintype (F ↪g G) := Fintype.ofFinite _
  have h1 : ∀ v, emb F G {v}ᶜ =
      ∑ f : F ↪g G, if ∀ u, f u ≠ v then 1 else 0 := by
    intro v
    rw [emb, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hf : ∀ u, f u ≠ v
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  have h2 : ∀ f : F ↪g G, (∑ v, if ∀ u, f u ≠ v then 1 else 0) =
      Fintype.card V - Fintype.card U := by
    intro f
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun v => ∀ u, f u ≠ v) = (Finset.univ.image f)ᶜ := by
      ext v
      simp
    rw [this, Finset.card_compl, Finset.card_image_of_injective _ f.injective, Finset.card_univ]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun f _ => h2 f, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Nat.card_eq_fintype_card, mul_comm]

/-- Hypomorphic graphs have the same number of embeddings of each graph with fewer vertices. -/
lemma card_embedding_eq_of_hypomorphic [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (h : Hypomorphic G H) [Finite U] (F : SimpleGraph U) (hU : Nat.card U < Fintype.card V) :
    Nat.card (F ↪g G) = Nat.card (F ↪g H) := by
  obtain ⟨σ, hσ⟩ := h
  let := Fintype.ofFinite U
  have hsum : ∑ v, emb F G {v}ᶜ = ∑ w, emb F H {w}ᶜ :=
    Fintype.sum_equiv σ _ _ fun v => emb_eq_of_iso (hσ v).some F
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  rw [sum_emb_compl_singleton, sum_emb_compl_singleton, ← hcard] at hsum
  rw [Nat.card_eq_fintype_card] at hU
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hU) hsum

/-- A property closed under adjacency propagates along reachability. -/
lemma of_reachable {p : U → Prop} (hp : ∀ a b, F.Adj a b → p a → p b) {a b : U}
    (h : F.Reachable a b) (ha : p a) : p b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hp _ _ hadj ha)

/-- For connected `F`, the embeddings into a set split over a closed piece `C`. -/
lemma emb_eq_add [Finite U] [Finite V] {P C : Set V} (hF : F.Connected) (hC : C ⊆ P)
    (hGC : ∀ x ∈ C, ∀ y ∈ P, G.Adj x y → y ∈ C) :
    emb F G P = emb F G C + emb F G (P \ C) := by
  classical
  have : Finite (F ↪g G) := finite_embedding
  obtain ⟨u₀⟩ := hF.nonempty
  have hstep : ∀ f : F ↪g G, (∀ u, f u ∈ P) → ∀ a b, F.Adj a b → f a ∈ C → f b ∈ C :=
    fun f hf a b hab ha => hGC _ ha _ (hf b) (f.map_adj_iff.mpr hab)
  have key : ∀ f : F ↪g G, (∀ u, f u ∈ P) ↔ (∀ u, f u ∈ C) ∨ (∀ u, f u ∈ P \ C) := by
    intro f
    constructor
    · intro hf
      by_cases h0 : f u₀ ∈ C
      · exact Or.inl fun u => of_reachable (hstep f hf) (hF.preconnected u₀ u) h0
      · exact Or.inr fun u =>
          ⟨hf u, fun hu => h0 (of_reachable (hstep f hf) (hF.preconnected u u₀) hu)⟩
    · rintro (h | h) u
      · exact hC (h u)
      · exact (h u).1
  have hdisj : Disjoint (fun f : F ↪g G => ∀ u, f u ∈ C) (fun f => ∀ u, f u ∈ P \ C) := by
    intro r hr1 hr2 f hf
    exact ((hr2 f hf) u₀).2 ((hr1 f hf) u₀)
  unfold emb
  rw [Nat.card_congr (Equiv.subtypeEquivRight key), Nat.card_congr (subtypeOrEquiv _ _ hdisj),
    Nat.card_sum]

lemma exists_of_emb_pos {P : Set W} (h : 0 < emb F H P) :
    ∃ f : F ↪g H, ∀ u, f u ∈ P := by
  by_contra hcon
  push Not at hcon
  have : IsEmpty {f : F ↪g H // ∀ u, f u ∈ P} := ⟨fun f => by
    obtain ⟨u, hu⟩ := hcon f.1
    exact hu (f.2 u)⟩
  simp [emb, Nat.card_of_isEmpty] at h

end Embeddings

section Connectivity

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma reachable_of_connected_card {a x y : V} (h : (G.induce {a}ᶜ).Connected) (hx : x ≠ a)
    (hy : y ≠ a) : G.Reachable x y :=
  (h.preconnected ⟨x, hx⟩ ⟨y, hy⟩).map (Embedding.induce _).toHom

/-- With at least three vertices, two distinct connected cards force `G` to be connected. -/
lemma connected_of_connected_cards [Fintype V] (hV : 3 ≤ Fintype.card V) {a b : V} (hab : a ≠ b)
    (ha : (G.induce {a}ᶜ).Connected) (hb : (G.induce {b}ᶜ).Connected) : G.Connected := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, z ≠ a ∧ z ≠ b := by
    by_contra hcon
    push Not at hcon
    have : (Finset.univ : Finset V) ⊆ {a, b} := fun z _ => by
      by_cases hza : z = a
      · simp [hza]
      · simp [hcon z hza]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Finset.card_pair hab] at this
    omega
  refine (connected_iff G).mpr ⟨fun x y => ?_, ⟨a⟩⟩
  by_cases hxa : x = a
  · by_cases hya : y = a
    · rw [hxa, hya]
    · by_cases hyb : y = b
      · subst hxa hyb
        exact (reachable_of_connected_card hb hab hz.2).trans
          (reachable_of_connected_card ha hz.1 (Ne.symm hab))
      · exact reachable_of_connected_card hb (hxa ▸ hab) hyb
  · by_cases hya : y = a
    · by_cases hxb : x = b
      · subst hya hxb
        exact (reachable_of_connected_card ha (Ne.symm hab) hz.1).trans
          (reachable_of_connected_card hb hz.2 hab)
      · exact reachable_of_connected_card hb hxb (hya ▸ hab)
    · exact reachable_of_connected_card ha hxa hya

/-- A graph hypomorphic to a disconnected graph on at least three vertices is disconnected. -/
lemma not_connected_of_hypomorphic [Fintype V] [Fintype W] (hV : 3 ≤ Fintype.card V)
    (hd : ¬G.Connected) (h : Hypomorphic G H) : ¬H.Connected := by
  intro hH
  obtain ⟨σ, hσ⟩ := h
  have hW : 3 ≤ Fintype.card W := Fintype.card_congr σ ▸ hV
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  classical
  obtain ⟨u, w, huw, hu, hw⟩ := hT.exists_ne_and_degree_eq_one
  have hcu : (H.induce {u}ᶜ).Connected :=
    (hT.1.induce_compl_singleton_of_degree_eq_one hu).mono fun _ _ h => hTH h
  have hcw : (H.induce {w}ᶜ).Connected :=
    (hT.1.induce_compl_singleton_of_degree_eq_one hw).mono fun _ _ h => hTH h
  have iu := hσ (σ.symm u)
  have iw := hσ (σ.symm w)
  rw [σ.apply_symm_apply] at iu iw
  exact hd (connected_of_connected_cards hV (σ.symm.injective.ne huw)
    (iu.some.connected_iff.mpr hcu) (iw.some.connected_iff.mpr hcw))

/-- A connected induced subgraph of a disconnected graph misses a vertex. -/
lemma ncard_lt_of_not_connected [Fintype V] (hd : ¬G.Connected) {S : Set V}
    (hS : (G.induce S).Connected) : S.ncard < Fintype.card V := by
  by_contra hlt
  have hS' : S = Set.univ := Set.eq_of_subset_of_ncard_le (Set.subset_univ S)
    (by rw [Set.ncard_univ, Nat.card_eq_fintype_card]; omega)
  subst hS'
  exact hd ((induceUnivIso G).connected_iff.mp hS)

/-- Adding a neighbour to a connected set keeps it connected. -/
lemma connected_insert {C : Set V} (hC : (G.induce C).Connected) {x y : V} (hx : x ∈ C)
    (hxy : G.Adj x y) : (G.induce (insert y C)).Connected := by
  let ι := G.induceHomOfLE (Set.subset_insert y C)
  have hreach : ∀ c : (insert y C : Set V), (G.induce (insert y C)).Reachable ⟨x, Or.inr hx⟩ c := by
    rintro ⟨c, hc⟩
    by_cases hcC : c ∈ C
    · exact (hC.preconnected ⟨x, hx⟩ ⟨c, hcC⟩).map ι.toHom
    · have hcy : c = y := by
        rcases hc with hc | hc
        · exact hc
        · exact absurd hc hcC
      have hxc : G.Adj x c := hcy ▸ hxy
      exact Adj.reachable hxc
  exact (connected_iff _).mpr ⟨fun a b => (hreach a).symm.trans (hreach b), ⟨⟨y, Set.mem_insert _ _⟩⟩⟩

lemma connected_induce_singleton (v : V) : (G.induce {v}).Connected :=
  (connected_iff _).mpr ⟨fun a b => by
    have : a = b := Subtype.ext ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)
    subst this
    exact Reachable.refl _, ⟨⟨v, rfl⟩⟩⟩

/-- A largest connected subset is closed under adjacency inside `P`. -/
lemma closed_of_max {P C : Set V} [Finite V] (hCP : C ⊆ P) (hC : (G.induce C).Connected)
    (hmax : ∀ S ⊆ P, (G.induce S).Connected → S.ncard ≤ C.ncard) :
    ∀ x ∈ C, ∀ y ∈ P, G.Adj x y → y ∈ C := by
  intro x hx y hy hxy
  by_contra hyC
  have := hmax (insert y C) (Set.insert_subset hy hCP) (connected_insert hC hx hxy)
  rw [Set.ncard_insert_of_notMem hyC] at this
  omega

end Connectivity

section Glue

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Glue isomorphisms on a closed piece and on its complement. -/
lemma nonempty_iso_glue {P C : Set V} {Q T : Set W} (hC : C ⊆ P) (hT : T ⊆ Q)
    (hGC : ∀ x ∈ C, ∀ y ∈ P, G.Adj x y → y ∈ C) (hHT : ∀ x ∈ T, ∀ y ∈ Q, H.Adj x y → y ∈ T)
    (φ : G.induce C ≃g H.induce T) (ψ : G.induce (P \ C) ≃g H.induce (Q \ T)) :
    Nonempty (G.induce P ≃g H.induce Q) := by
  classical
  let f : P → Q := fun x =>
    if h : (x : V) ∈ C then ⟨(φ ⟨x, h⟩).1, hT (φ ⟨x, h⟩).2⟩
    else ⟨(ψ ⟨x, x.2, h⟩).1, (ψ ⟨x, x.2, h⟩).2.1⟩
  let g : Q → P := fun y =>
    if h : (y : W) ∈ T then ⟨(φ.symm ⟨y, h⟩).1, hC (φ.symm ⟨y, h⟩).2⟩
    else ⟨(ψ.symm ⟨y, y.2, h⟩).1, (ψ.symm ⟨y, y.2, h⟩).2.1⟩
  have f_in {x : P} (h : (x : V) ∈ C) : (f x : W) = φ ⟨x, h⟩ := by simp [f, h]
  have f_out {x : P} (h : (x : V) ∉ C) : (f x : W) = ψ ⟨x, x.2, h⟩ := by simp [f, h]
  have g_in {y : Q} (h : (y : W) ∈ T) : (g y : V) = φ.symm ⟨y, h⟩ := by simp [g, h]
  have g_out {y : Q} (h : (y : W) ∉ T) : (g y : V) = ψ.symm ⟨y, y.2, h⟩ := by simp [g, h]
  have fT {x : P} : ((f x : W) ∈ T ↔ (x : V) ∈ C) := by
    by_cases h : (x : V) ∈ C
    · rw [f_in h]
      exact iff_of_true (φ ⟨x, h⟩).2 h
    · rw [f_out h]
      exact iff_of_false (ψ ⟨x, x.2, h⟩).2.2 h
  have gC {y : Q} : ((g y : V) ∈ C ↔ (y : W) ∈ T) := by
    by_cases h : (y : W) ∈ T
    · rw [g_in h]
      exact iff_of_true (φ.symm ⟨y, h⟩).2 h
    · rw [g_out h]
      exact iff_of_false (ψ.symm ⟨y, y.2, h⟩).2.2 h
  refine ⟨⟨⟨f, g, fun x => ?_, fun y => ?_⟩, fun {a b} => ?_⟩⟩
  · apply Subtype.ext
    by_cases h : (x : V) ∈ C
    · have e : (⟨(f x : W), fT.mpr h⟩ : T) = φ ⟨x, h⟩ := Subtype.ext (f_in h)
      rw [g_in (fT.mpr h), e, RelIso.symm_apply_apply]
    · have e : (⟨(f x : W), (f x).2, mt fT.mp h⟩ : ↥(Q \ T)) = ψ ⟨x, x.2, h⟩ :=
        Subtype.ext (f_out h)
      rw [g_out (mt fT.mp h), e, RelIso.symm_apply_apply]
  · apply Subtype.ext
    by_cases h : (y : W) ∈ T
    · have e : (⟨(g y : V), gC.mpr h⟩ : C) = φ.symm ⟨y, h⟩ := Subtype.ext (g_in h)
      rw [f_in (gC.mpr h), e, RelIso.apply_symm_apply]
    · have e : (⟨(g y : V), (g y).2, mt gC.mp h⟩ : ↥(P \ C)) = ψ.symm ⟨y, y.2, h⟩ :=
        Subtype.ext (g_out h)
      rw [f_out (mt gC.mp h), e, RelIso.apply_symm_apply]
  · change H.Adj (f a : W) (f b : W) ↔ G.Adj (a : V) (b : V)
    by_cases ha : (a : V) ∈ C <;> by_cases hb : (b : V) ∈ C
    · rw [f_in ha, f_in hb]
      exact φ.map_adj_iff
    · rw [f_in ha, f_out hb]
      exact iff_of_false (fun h => (ψ ⟨b, b.2, hb⟩).2.2 (hHT _ (φ ⟨a, ha⟩).2 _
        (ψ ⟨b, b.2, hb⟩).2.1 h)) (fun h => hb (hGC _ ha _ b.2 h))
    · rw [f_out ha, f_in hb]
      exact iff_of_false (fun h => (ψ ⟨a, a.2, ha⟩).2.2 (hHT _ (φ ⟨b, hb⟩).2 _
        (ψ ⟨a, a.2, ha⟩).2.1 h.symm)) (fun h => ha (hGC _ hb _ a.2 h.symm))
    · rw [f_out ha, f_out hb]
      exact ψ.map_adj_iff

end Glue

section Peeling

variable {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

/-- `G.induce P` and `H.induce Q` have the same embedding counts of connected graphs with
fewer than `|V|` vertices. -/
def Hyp (G : SimpleGraph V) (H : SimpleGraph W) (P : Set V) (Q : Set W) : Prop :=
  ∀ (U : Type) [Finite U] (F : SimpleGraph U), F.Connected → Nat.card U < Fintype.card V →
    emb F G P = emb F H Q

lemma emb_induce_pos {S P : Set V} (hSP : S ⊆ P) : 0 < emb (G.induce S) G P := by
  have : Finite (G.induce S ↪g G) := finite_embedding
  have : Nonempty {f : G.induce S ↪g G // ∀ u, f u ∈ P} :=
    ⟨⟨Embedding.induce S, fun u => hSP u.2⟩⟩
  exact Nat.card_pos

omit [Fintype W] in
/-- An embedding of `G.induce C` with image in `Q` gives a set `T ⊆ Q` with
`G.induce C ≃g H.induce T`. -/
lemma exists_iso_of_hyp {P : Set V} {Q : Set W} (hyp : Hyp G H P Q) {C : Set V} (hCP : C ⊆ P)
    (hC : (G.induce C).Connected) (hCn : C.ncard < Fintype.card V) :
    ∃ T ⊆ Q, Nonempty (G.induce C ≃g H.induce T) := by
  have h := hyp C (G.induce C) hC hCn
  have h2 : 0 < emb (G.induce C) H Q := h ▸ emb_induce_pos hCP
  obtain ⟨f, hf⟩ := exists_of_emb_pos h2
  exact ⟨Set.range f, Set.range_subset_iff.mpr hf, ⟨f.isoInduceRange⟩⟩

lemma hyp_symm {P : Set V} {Q : Set W} (hcard : Fintype.card V = Fintype.card W)
    (hyp : Hyp G H P Q) : Hyp H G Q P :=
  fun U _ F hF hU => (hyp U F hF (hcard ▸ hU)).symm

lemma iso_of_hyp_empty {P : Set V} {Q : Set W} (hV : 3 ≤ Fintype.card V) (hP : P = ∅)
    (hyp : Hyp G H P Q) : Nonempty (G.induce P ≃g H.induce Q) := by
  have hQ : Q = ∅ := by
    by_contra hQ
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hQ
    have hF : (⊥ : SimpleGraph Unit).Connected :=
      (connected_iff _).mpr ⟨fun _ _ => Reachable.refl _, ⟨()⟩⟩
    have h := hyp Unit ⊥ hF (by rw [Nat.card_unique]; omega)
    have e1 : emb (⊥ : SimpleGraph Unit) G P = 0 := by
      have : IsEmpty {f : (⊥ : SimpleGraph Unit) ↪g G // ∀ u, f u ∈ P} :=
        ⟨fun f => by simpa [hP] using f.2 ()⟩
      exact Nat.card_of_isEmpty
    let ι : (⊥ : SimpleGraph Unit) ↪g H :=
      ⟨⟨fun _ => w, fun _ _ _ => rfl⟩, fun {_ _} => iff_of_false (H.irrefl (v := w)) id⟩
    have e2 : 0 < emb (⊥ : SimpleGraph Unit) H Q := by
      have : Finite ((⊥ : SimpleGraph Unit) ↪g H) := finite_embedding
      have : Nonempty {f : (⊥ : SimpleGraph Unit) ↪g H // ∀ u, f u ∈ Q} := ⟨⟨ι, fun _ => hw⟩⟩
      exact Nat.card_pos
    omega
  subst hP hQ
  have : IsEmpty (∅ : Set V) := Set.isEmpty_coe_sort.mpr rfl
  have : IsEmpty (∅ : Set W) := Set.isEmpty_coe_sort.mpr rfl
  exact ⟨⟨Equiv.equivOfIsEmpty _ _, fun {a} => isEmptyElim a⟩⟩

/-- **Peeling.** Equal embedding counts of connected graphs give an isomorphism. -/
lemma iso_of_hyp (hV : 3 ≤ Fintype.card V) (hcard : Fintype.card V = Fintype.card W)
    (hGn : ∀ S : Set V, (G.induce S).Connected → S.ncard < Fintype.card V)
    (hHn : ∀ T : Set W, (H.induce T).Connected → T.ncard < Fintype.card V) :
    ∀ m (P : Set V) (Q : Set W), P.ncard ≤ m → Hyp G H P Q →
      Nonempty (G.induce P ≃g H.induce Q) := by
  intro m
  induction m with
  | zero =>
    intro P Q hP hyp
    exact iso_of_hyp_empty hV ((Set.ncard_eq_zero (Set.toFinite P)).mp (Nat.le_zero.mp hP)) hyp
  | succ m ih =>
    intro P Q hP hyp
    rcases P.eq_empty_or_nonempty with hPe | ⟨v, hv⟩
    · exact iso_of_hyp_empty hV hPe hyp
    -- a largest connected subset `C` of `P`
    obtain ⟨C, ⟨hCP, hC⟩, hmax⟩ := Set.exists_max_image
      {S : Set V | S ⊆ P ∧ (G.induce S).Connected} Set.ncard (Set.toFinite _)
      ⟨{v}, Set.singleton_subset_iff.mpr hv, connected_induce_singleton v⟩
    have hmax' : ∀ S ⊆ P, (G.induce S).Connected → S.ncard ≤ C.ncard :=
      fun S hS hSc => hmax S ⟨hS, hSc⟩
    obtain ⟨T, hTQ, ⟨φ⟩⟩ := exists_iso_of_hyp hyp hCP hC (hGn C hC)
    have hTc : (H.induce T).Connected := φ.connected_iff.mp hC
    have hCT : C.ncard = T.ncard := Nat.card_congr φ.toEquiv
    -- `T` is a largest connected subset of `Q`
    have hmaxT : ∀ S ⊆ Q, (H.induce S).Connected → S.ncard ≤ T.ncard := by
      intro S hSQ hSc
      obtain ⟨S', hS'P, ⟨χ⟩⟩ :=
        exists_iso_of_hyp (hyp_symm hcard hyp) hSQ hSc (hcard ▸ hHn S hSc)
      have : S.ncard = S'.ncard := Nat.card_congr χ.toEquiv
      rw [this, ← hCT]
      exact hmax' S' hS'P (χ.connected_iff.mp hSc)
    have hGC := closed_of_max hCP hC hmax'
    have hHT := closed_of_max hTQ hTc hmaxT
    -- the remainders satisfy the hypothesis
    have hyp' : Hyp G H (P \ C) (Q \ T) := by
      intro U _ F hF hU
      have e1 := emb_eq_add (G := G) hF hCP hGC
      have e2 := emb_eq_add (G := H) hF hTQ hHT
      have e3 := emb_eq_of_iso φ F
      have e4 := hyp U F hF hU
      omega
    have hlt : (P \ C).ncard < P.ncard := by
      obtain ⟨⟨c, hc⟩⟩ := hC.nonempty
      exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset Set.sdiff_subset).mpr
        ⟨c, hCP hc, fun h => h.2 hc⟩)
    obtain ⟨ψ⟩ := ih (P \ C) (Q \ T) (by omega) hyp'
    exact nonempty_iso_glue hCP hTQ hGC hHT φ ψ

end Peeling

/-- **Disconnected graphs are reconstructible.** The exact statement of
`ReconstructionConjecture.reconstruction_conjecture.variants.disconnected`. -/
theorem reconstruction_conjecture_variants_disconnected {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hd : ¬G.Connected) (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  classical
  have hcard : Fintype.card V = Fintype.card W := h.card_eq
  have hHd := not_connected_of_hypomorphic hV hd h
  have hyp : Hyp G H Set.univ Set.univ := fun U _ F _ hU => by
    rw [emb_univ, emb_univ]
    exact card_embedding_eq_of_hypomorphic h F hU
  obtain ⟨φ⟩ := iso_of_hyp hV hcard (fun S hS => ncard_lt_of_not_connected hd hS)
    (fun T hT => hcard ▸ ncard_lt_of_not_connected hHd hT) _ Set.univ Set.univ le_rfl hyp
  exact ⟨(induceUnivIso G).symm.trans (φ.trans (induceUnivIso H))⟩

end ReconstructionDisconnected

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2.H1 := by
  intro V _ W _ hV G H hd h
  exact ReconstructionDisconnected.reconstruction_conjecture_variants_disconnected hV G H hd h
