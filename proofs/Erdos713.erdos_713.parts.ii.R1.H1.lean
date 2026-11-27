import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1
import Mathlib

/-!
# Peeling vertices of degree less than two in bipartite Turan problems (Erdos Problem 713, ii, H1)

Given a bipartite graph `G` on `Fin q` with at least `2` edges and a vertex `v` of degree `< 2`:
- If `G.edgeFinset.card = 2`, then `G` is acyclic, so its extremal number is `O(n)`.
- Otherwise, removing `v` yields a bipartite graph `J` on `Fin (q - 1)` with at least `2` edges
  whose extremal number satisfies `0 ≤ extremalNumber n G - extremalNumber n J ≤ q * n` for all
  `n ≥ q`, so `(extremalNumber n J : ℝ) - (extremalNumber n G : ℝ) = O(n)`.
-/

namespace Erdos713IIH1

open Finset SimpleGraph Filter Asymptotics
open scoped Classical

lemma degree_irrel {W : Type*} (G : SimpleGraph W) (w : W)
    (a b : Fintype (G.neighborSet w)) :
    @SimpleGraph.degree W G w a = @SimpleGraph.degree W G w b := by
  cases Subsingleton.elim a b
  rfl

lemma dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) [DecidableRel X.Adj] (q : ℕ)
    (large : q * Fintype.card V < X.edgeFinset.card) :
    ∃ (U : Finset V) (_ : (U : Set V)),
      ∀ x : (U : Set V), q ≤ (X.induce (U : Set V)).degree x := by
  let edges (U : Finset V) := X.edgeFinset ∩ U.sym2
  have start : ∃ k, ∃ U : Finset V, U.card = k ∧ q * U.card < (edges U).card := by
    refine ⟨_, univ, rfl, ?_⟩
    simpa [edges] using large
  obtain ⟨U, hU, dense⟩ := Nat.find_spec start
  have nonempty : U.Nonempty := by
    by_contra! h
    simp [h, edges] at dense
  obtain ⟨u, hu⟩ := nonempty
  refine ⟨U, ⟨u, hu⟩, ?_⟩
  intro x
  let inside := X.neighborFinset x.val ∩ U
  have deg : (X.induce (U : Set V)).degree x = inside.card := by
    have mapEq := SimpleGraph.map_neighborFinset_induce (G := X) (s := (U : Set V)) x
    have count := congrArg Finset.card mapEq
    rw [card_map, card_neighborFinset_eq_degree, Finset.toFinset_coe] at count
    exact (degree_irrel _ _ _ _).trans count
  have cover : edges U ⊆ edges (U.erase x.val) ∪ inside.image (fun y => s(x.val, y)) := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨hab, hends⟩ := mem_inter.mp he
      obtain ⟨ha, hb⟩ := mk_mem_sym2_iff.mp hends
      have adj : X.Adj a b := X.mem_edgeFinset.mp hab
      by_cases ax : a = x.val
      · subst a
        exact mem_union_right _ (mem_image.mpr ⟨b, mem_inter.mpr
          ⟨(X.mem_neighborFinset x.val b).mpr adj, hb⟩, rfl⟩)
      by_cases bx : b = x.val
      · subst b
        exact mem_union_right _ (mem_image.mpr ⟨a, mem_inter.mpr
          ⟨(X.mem_neighborFinset x.val a).mpr adj.symm, ha⟩, Sym2.eq_swap⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨hab, mk_mem_sym2_iff.mpr
        ⟨mem_erase.mpr ⟨ax, ha⟩, mem_erase.mpr ⟨bx, hb⟩⟩⟩)
  have lost := (card_le_card cover).trans (card_union_le ..)
  have cost : (inside.image (fun y => s(x.val, y))).card ≤ inside.card := card_image_le
  have smaller : (U.erase x.val).card < Nat.find start := hU ▸ card_erase_lt_of_mem x.property
  have thin : (edges (U.erase x.val)).card ≤ q * (U.erase x.val).card := by
    by_contra! h
    exact Nat.find_min start smaller ⟨_, rfl, h⟩
  have change := congrArg (q * ·) (card_erase_add_one x.property)
  simp only [Nat.mul_add, Nat.mul_one] at change
  omega

lemma forest_leaf {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (forest : G.IsAcyclic) : ∃ v, G.degree v ≤ 1 := by
  rcases subsingleton_or_nontrivial W with hs | hn
  · let _ := hs
    obtain ⟨v⟩ := ‹Nonempty W›
    exact ⟨v, by simp⟩
  let _ := hn
  obtain ⟨T, sub, _, tree⟩ := (connected_top (V := W)).exists_isTree_le_of_le_of_isAcyclic
    (show G ≤ ⊤ from le_top) forest
  obtain ⟨v, hv⟩ := tree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, (G.degree_le_of_le sub).trans hv.le⟩

lemma forest_embedding {W V : Type*} [Fintype W] [Fintype V]
    (G : SimpleGraph W) (X : SimpleGraph V) [DecidableRel X.Adj] (z : V)
    (forest : G.IsAcyclic) (degree : ∀ x, Fintype.card W ≤ X.degree x) : G ⊑ X := by
  have partialMap (S : Finset W) : ∃ f : W → V, Set.InjOn f (S : Set W) ∧
      ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → X.Adj (f u) (f v) := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases empty : S = ∅
      · subst S
        exact ⟨fun _ => z, by simp, by simp⟩
      obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr empty
      let _ : Nonempty (S : Set W) := ⟨⟨a, ha⟩⟩
      obtain ⟨leaf, low⟩ := forest_leaf (G.induce (S : Set W)) (forest.induce _)
      let u := leaf.val
      have hu : u ∈ S := leaf.property
      let T := S.erase u
      obtain ⟨f, inj, mapAdj⟩ := ih T (erase_ssubset hu)
      have unique (v) (hv : v ∈ T) (w) (hw : w ∈ T) (ev : G.Adj u v) (ew : G.Adj u w) :
          v = w := by
        let v' : (S : Set W) := ⟨v, mem_of_mem_erase hv⟩
        let w' : (S : Set W) := ⟨w, mem_of_mem_erase hw⟩
        have l : ((G.induce (S : Set W)).neighborFinset leaf).card ≤ 1 := low
        have eq := card_le_one.mp l v' ((mem_neighborFinset _ _ _).mpr ev)
          w' ((mem_neighborFinset _ _ _).mpr ew)
        exact congrArg Subtype.val eq
      have anchor : ∃ y : V, ∀ v ∈ T, G.Adj u v → f v = y := by
        by_cases has : ∃ v ∈ T, G.Adj u v
        · obtain ⟨v, hv, ev⟩ := has
          exact ⟨f v, fun w hw ew => congrArg f (unique w hw v hv ew ev)⟩
        · exact ⟨z, fun v hv ev => False.elim (has ⟨v, hv, ev⟩)⟩
      obtain ⟨y, hy⟩ := anchor
      have fresh : ∃ b ∈ X.neighborFinset y, b ∉ T.image f := by
        by_contra! h
        have le := (card_le_card (show X.neighborFinset y ⊆ T.image f from h)).trans card_image_le
        have lt : T.card < S.card := card_lt_card (erase_ssubset hu)
        have lim := card_le_univ S
        have deg := degree y
        rw [card_neighborFinset_eq_degree] at le
        omega
      obtain ⟨b, hb, new⟩ := fresh
      have edge : X.Adj y b := (mem_neighborFinset _ _ _).mp hb
      let g (w : W) := if w = u then b else f w
      have old (w : W) (hw : w ∈ S) (ne : w ≠ u) : w ∈ T := mem_erase.mpr ⟨ne, hw⟩
      have different (w) (hw : w ∈ T) : f w ≠ b := fun eq => new (eq ▸ mem_image_of_mem _ hw)
      refine ⟨g, ?_, ?_⟩
      · intro v hv w hw eq
        by_cases ev : v = u <;> by_cases ew : w = u
        · exact ev.trans ew.symm
        · exact False.elim (different _ (old w hw ew) (by simpa [g, ev, ew] using eq.symm))
        · exact False.elim (different _ (old v hv ev) (by simpa [g, ev, ew] using eq))
        · exact inj (old v hv ev) (old w hw ew) (by simpa [g, ev, ew] using eq)
      · intro v hv w hw e
        by_cases ev : v = u
        · subst v
          have ew : w ≠ u := e.ne.symm
          simp only [g, if_pos rfl, if_neg ew, hy w (old w hw ew) e]
          exact edge.symm
        by_cases ew : w = u
        · subst w
          simp only [g, if_neg ev, if_pos rfl, hy v (old v hv ev) e.symm]
          exact edge
        simpa only [g, if_neg ev, if_neg ew] using mapAdj v (old v hv ev) w (old w hw ew) e
  obtain ⟨f, inj, hom⟩ := partialMap univ
  exact ⟨⟨⟨f, fun {a b} e => hom a (mem_univ _) b (mem_univ _) e⟩,
    fun _ _ eq => inj (mem_univ _) (mem_univ _) eq⟩⟩

lemma forest_extremal_le {q n : ℕ} (G : SimpleGraph (Fin q)) (forest : G.IsAcyclic) :
    extremalNumber n G ≤ q * n := by
  suffices h : extremalNumber (Fintype.card (Fin n)) G ≤ q * n by
    simpa only [Fintype.card_fin] using h
  apply (extremalNumber_le_iff (V := Fin n) G _).mpr
  intro X _ free
  by_contra! large
  obtain ⟨U, u, deg⟩ := dense_core X q (by simpa only [Fintype.card_fin] using large)
  have emb := forest_embedding G (X.induce (U : Set (Fin n))) u forest
    (by simpa only [Fintype.card_fin] using deg)
  exact free (emb.trans (Copy.induce X (U : Set (Fin n))).isContained)

lemma edgeFinset_irrel {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
    (a b : Fintype X.edgeSet) :
    @SimpleGraph.edgeFinset V X a = @SimpleGraph.edgeFinset V X b := by
  ext e
  simp

lemma isAcyclic_of_card_edgeFinset_le_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : G.edgeFinset.card ≤ 2) : G.IsAcyclic := by
  intro w c hc
  have h1 : 3 ≤ c.length := hc.three_le_length
  have h2 : c.length ≤ G.edgeFinset.card := hc.isCircuit.isTrail.length_le_card_edgeFinset
  omega

lemma three_le_of_two_le_edges {q : ℕ} (G : SimpleGraph (Fin q)) (h : 2 ≤ G.edgeFinset.card) :
    3 ≤ q := by
  have hle : G.edgeFinset.card ≤ (⊤ : SimpleGraph (Fin q)).edgeFinset.card :=
    card_le_card (edgeFinset_mono le_top)
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hle
  have h2 : 2 ≤ q.choose 2 := h.trans hle
  rcases q with _ | _ | _ | q'
  · simp at h2
  · simp at h2
  · norm_num at h2
  · omega

noncomputable def extendAt {r : ℕ} {α : Type*} (v : Fin (r + 1)) (w : α) (f : Fin r → α)
    (x : Fin (r + 1)) : α :=
  if hx : x = v then w else f (Classical.choose (Fin.exists_succAbove_eq hx))

@[simp]
lemma extendAt_self {r : ℕ} {α : Type*} (v : Fin (r + 1)) (w : α) (f : Fin r → α) :
    extendAt v w f v = w :=
  dif_pos rfl

@[simp]
lemma extendAt_succAbove {r : ℕ} {α : Type*} (v : Fin (r + 1)) (w : α) (f : Fin r → α)
    (i : Fin r) : extendAt v w f (v.succAbove i) = f i := by
  have hne : v.succAbove i ≠ v := v.succAbove_ne i
  rw [extendAt, dif_neg hne]
  congr 1
  exact v.succAboveEmb.injective (Classical.choose_spec (Fin.exists_succAbove_eq hne))

lemma extendAt_injective {r : ℕ} {α : Type*} (v : Fin (r + 1)) (w : α) (f : Fin r → α)
    (hf : Function.Injective f) (hw : ∀ i, f i ≠ w) :
    Function.Injective (extendAt v w f) := by
  intro x y hxy
  by_cases hx : x = v
  · by_cases hy : y = v
    · exact hx.trans hy.symm
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hy
      rw [hx, extendAt_self, extendAt_succAbove] at hxy
      exact False.elim (hw j hxy.symm)
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hx
    by_cases hy : y = v
    · rw [hy, extendAt_succAbove, extendAt_self] at hxy
      exact False.elim (hw i hxy)
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hy
      rw [extendAt_succAbove, extendAt_succAbove] at hxy
      exact congrArg v.succAbove (hf hxy)

lemma card_edgeFinset_comap_succAbove {r : ℕ} (G : SimpleGraph (Fin (r + 1)))
    (v : Fin (r + 1)) :
    (G.comap v.succAboveEmb).edgeFinset.card + G.degree v = G.edgeFinset.card := by
  let J : SimpleGraph (Fin r) := G.comap v.succAboveEmb
  have hinc_sub : G.incidenceFinset v ⊆ G.edgeFinset := G.incidenceFinset_subset v
  have hsdiff : (G.edgeFinset \ G.incidenceFinset v).card + (G.incidenceFinset v).card =
      G.edgeFinset.card := card_sdiff_add_card_eq_card hinc_sub
  rw [G.card_incidenceFinset_eq_degree v] at hsdiff
  have himg_eq : G.edgeFinset \ G.incidenceFinset v =
      J.edgeFinset.image (Sym2.map v.succAbove) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, mem_incidenceFinset,
        mk'_mem_incidenceSet_iff, mem_image]
      constructor
      · rintro ⟨hab, hnot⟩
        have hav : a ≠ v := fun h => hnot ⟨hab, Or.inl h.symm⟩
        have hbv : b ≠ v := fun h => hnot ⟨hab, Or.inr h.symm⟩
        obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hav
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hbv
        exact ⟨s(i, j), hab, rfl⟩
      · rintro ⟨e', he', hmap⟩
        induction e' using Sym2.ind with
        | _ i j =>
          rw [mem_edgeSet] at he'
          change G.Adj (v.succAbove i) (v.succAbove j) at he'
          have hpair : s(v.succAbove i, v.succAbove j) = s(a, b) := hmap
          rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · refine ⟨he', ?_⟩
            rintro ⟨_, h | h⟩
            · exact v.succAbove_ne i h.symm
            · exact v.succAbove_ne j h.symm
          · refine ⟨he'.symm, ?_⟩
            rintro ⟨_, h | h⟩
            · exact v.succAbove_ne j h.symm
            · exact v.succAbove_ne i h.symm
  have hinj : Function.Injective (Sym2.map v.succAbove) :=
    Sym2.map.injective v.succAboveEmb.injective
  have hcard_eq : (G.edgeFinset \ G.incidenceFinset v).card = J.edgeFinset.card := by
    rw [himg_eq, card_image_of_injective _ hinj]
  change J.edgeFinset.card + G.degree v = G.edgeFinset.card
  omega

lemma peel_low_degree_aux {n q : ℕ} :
    ∀ (m : ℕ) (Y : SimpleGraph (Fin n)),
      (univ.filter (fun x : Fin n => ¬ Y.IsIsolated x)).card ≤ m →
      ∃ Z : SimpleGraph (Fin n), Z ≤ Y ∧
        Y.edgeFinset.card ≤ Z.edgeFinset.card + q * m ∧
        ∀ x : Fin n, ¬ Z.IsIsolated x → q ≤ Z.degree x
  | 0, Y, hm => by
    refine ⟨Y, le_rfl, by simp, ?_⟩
    intro x hx
    have hmem : x ∈ univ.filter (fun z : Fin n => ¬ Y.IsIsolated z) :=
      mem_filter.mpr ⟨mem_univ x, hx⟩
    have hpos : 0 < (univ.filter (fun z : Fin n => ¬ Y.IsIsolated z)).card :=
      card_pos.mpr ⟨x, hmem⟩
    omega
  | m + 1, Y, hm => by
    by_cases hall : ∀ x : Fin n, ¬ Y.IsIsolated x → q ≤ Y.degree x
    · exact ⟨Y, le_rfl, by omega, hall⟩
    · push Not at hall
      obtain ⟨x0, hx0_act, hx0_lt⟩ := hall
      let D := Y.incidenceFinset x0
      let Y' := Y.deleteEdges (D : Set (Sym2 (Fin n)))
      have hY'_le : Y' ≤ Y := Y.deleteEdges_le _
      have hD_sub : D ⊆ Y.edgeFinset := Y.incidenceFinset_subset x0
      have hD_le : D.card ≤ Y.edgeFinset.card := card_le_card hD_sub
      have hD_card : D.card = Y.degree x0 := Y.card_incidenceFinset_eq_degree x0
      have hY'_edges : Y'.edgeFinset.card = Y.edgeFinset.card - D.card := by
        rw [show Y'.edgeFinset = Y.edgeFinset \ D from Y.edgeFinset_deleteEdges D,
          card_sdiff_of_subset hD_sub]
      have hx0_iso : Y'.IsIsolated x0 := by
        intro y hy
        obtain ⟨hadj, hnot⟩ := deleteEdges_adj.mp hy
        apply hnot
        change s(x0, y) ∈ Y.incidenceFinset x0
        rw [mem_incidenceFinset, mem_incidenceSet]
        exact hadj
      have hfilter_sub :
          univ.filter (fun z : Fin n => ¬ Y'.IsIsolated z) ⊆
            (univ.filter (fun z : Fin n => ¬ Y.IsIsolated z)).erase x0 := by
        intro z hz
        rw [mem_filter] at hz
        have hzne : z ≠ x0 := fun hzeq => hz.2 (hzeq ▸ hx0_iso)
        have hz_act : ¬ Y.IsIsolated z := fun hY => hz.2 (fun y hy => hY y (hY'_le hy))
        exact mem_erase.mpr ⟨hzne, mem_filter.mpr ⟨mem_univ z, hz_act⟩⟩
      have hx0_mem : x0 ∈ univ.filter (fun z : Fin n => ¬ Y.IsIsolated z) :=
        mem_filter.mpr ⟨mem_univ x0, hx0_act⟩
      have hcard_lt :
          ((univ.filter (fun z : Fin n => ¬ Y.IsIsolated z)).erase x0).card <
            (univ.filter (fun z : Fin n => ¬ Y.IsIsolated z)).card :=
        card_erase_lt_of_mem hx0_mem
      have hm' : (univ.filter (fun z : Fin n => ¬ Y'.IsIsolated z)).card ≤ m := by
        have := card_le_card hfilter_sub
        omega
      obtain ⟨Z, hZY', hZ_edges, hZ_deg⟩ := peel_low_degree_aux m Y' hm'
      refine ⟨Z, hZY'.trans hY'_le, ?_, hZ_deg⟩
      rw [edgeFinset_irrel Y' _ _] at hY'_edges
      have hmul : q * (m + 1) = q * m + q := by ring
      omega

lemma peel_low_degree {n : ℕ} (X : SimpleGraph (Fin n)) (q : ℕ) :
    ∃ Z : SimpleGraph (Fin n), Z ≤ X ∧
      X.edgeFinset.card ≤ Z.edgeFinset.card + q * n ∧
      ∀ x : Fin n, ¬ Z.IsIsolated x → q ≤ Z.degree x := by
  apply peel_low_degree_aux n X
  exact (card_le_univ _).trans_eq (Fintype.card_fin n)

lemma exists_notMem_image {r n : ℕ} (hrn : r < n) (f : Fin r → Fin n) :
    ∃ w : Fin n, w ∉ (univ : Finset (Fin r)).image f := by
  by_contra! hall
  have hsub : (univ : Finset (Fin n)) ⊆ (univ : Finset (Fin r)).image f :=
    fun w _ => hall w
  have hle := (card_le_card hsub).trans card_image_le
  simp only [card_fin] at hle
  omega

lemma extremal_diff_bound {r n : ℕ} (G : SimpleGraph (Fin (r + 1)))
    (v : Fin (r + 1)) (hv : G.degree v ≤ 1) (hn : r + 1 ≤ n) :
    extremalNumber n G ≤
      extremalNumber n (G.comap v.succAboveEmb) + (r + 1) * n := by
  set J : SimpleGraph (Fin r) := G.comap v.succAboveEmb
  suffices h : extremalNumber (Fintype.card (Fin n)) G ≤
      extremalNumber n J + (r + 1) * n by
    simpa only [Fintype.card_fin] using h
  apply (extremalNumber_le_iff (V := Fin n) G _).mpr
  intro X _ free
  by_contra! large
  rcases (by omega : G.degree v = 0 ∨ G.degree v = 1) with hdeg0 | hdeg1
  · have lJ : extremalNumber (Fintype.card (Fin n)) J < X.edgeFinset.card := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨f⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset (G := X) (H := J) lJ
    obtain ⟨w, hw⟩ := exists_notMem_image (by omega : r < n) f
    have hfw : ∀ i : Fin r, f i ≠ w := fun i eq => hw (eq ▸ mem_image_of_mem _ (mem_univ i))
    let g := extendAt v w f
    have hinj : Function.Injective g := extendAt_injective v w f f.injective hfw
    have hv_no_adj : ∀ y : Fin (r + 1), ¬ G.Adj v y := by
      intro y hy
      have hmem : y ∈ G.neighborFinset v := (G.mem_neighborFinset v y).mpr hy
      have hpos : 0 < (G.neighborFinset v).card := card_pos.mpr ⟨y, hmem⟩
      rw [G.card_neighborFinset_eq_degree v] at hpos
      omega
    apply free
    refine ⟨⟨⟨g, ?_⟩, hinj⟩⟩
    intro x y hadj
    have hxv : x ≠ v := fun h => hv_no_adj y (h ▸ hadj)
    have hyv : y ≠ v := fun h => hv_no_adj x (h ▸ hadj.symm)
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hxv
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hyv
    dsimp only [g]
    rw [extendAt_succAbove, extendAt_succAbove]
    exact f.toHom.map_rel' hadj
  · have hncard : (G.neighborFinset v).card = 1 := by
      rw [G.card_neighborFinset_eq_degree v]
      exact hdeg1
    obtain ⟨u, hu⟩ := card_eq_one.mp hncard
    have huv : G.Adj v u := (G.mem_neighborFinset v u).mp (by rw [hu]; simp)
    have hu_ne : u ≠ v := huv.ne.symm
    obtain ⟨u0, rfl⟩ := Fin.exists_succAbove_eq hu_ne
    have hv_adj_iff : ∀ y : Fin (r + 1), G.Adj v y ↔ y = v.succAbove u0 := by
      intro y
      rw [← G.mem_neighborFinset, hu, mem_singleton]
    by_cases hiso : J.IsIsolated u0
    · have lJ : extremalNumber (Fintype.card (Fin n)) J < X.edgeFinset.card := by
        rw [Fintype.card_fin]
        omega
      obtain ⟨f⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset (G := X) (H := J) lJ
      let S : Finset (Fin r) := univ.erase u0
      let D : Finset (Sym2 (Fin n)) := S.biUnion (fun i => X.incidenceFinset (f i))
      have hS_le : S.card ≤ r := (card_le_univ S).trans_eq (Fintype.card_fin r)
      have hD_card : D.card ≤ r * n := by
        apply card_biUnion_le.trans
        calc
          ∑ i ∈ S, (X.incidenceFinset (f i)).card ≤ ∑ _i ∈ S, n :=
            sum_le_sum (fun i _ => by
              rw [card_incidenceFinset_eq_degree]
              simpa only [Fintype.card_fin] using (X.degree_lt_card_verts (f i)).le)
          _ = S.card * n := by simp
          _ ≤ r * n := Nat.mul_le_mul_right n hS_le
      have hsdiff_pos : 0 < (X.edgeFinset \ D).card := by
        have h1 : X.edgeFinset.card - D.card ≤ (X.edgeFinset \ D).card := le_card_sdiff D _
        have h2 : r * n < (r + 1) * n := by
          have hmul : (r + 1) * n = r * n + n := by ring
          omega
        omega
      obtain ⟨e, he⟩ := card_pos.mp hsdiff_pos
      induction e using Sym2.ind with
      | _ a b =>
        rw [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet] at he
        obtain ⟨hab, hnotD⟩ := he
        have ha_ne : ∀ i ∈ S, f i ≠ a := by
          intro i hi hfi
          apply hnotD
          refine mem_biUnion.mpr ⟨i, hi, ?_⟩
          rw [mem_incidenceFinset, hfi, mem_incidenceSet]
          exact hab
        have hb_ne : ∀ i ∈ S, f i ≠ b := by
          intro i hi hfi
          apply hnotD
          refine mem_biUnion.mpr ⟨i, hi, ?_⟩
          rw [mem_incidenceFinset, hfi, Sym2.eq_swap, mem_incidenceSet]
          exact hab.symm
        let f' : Fin r → Fin n := fun i => if i = u0 then a else f i
        have hf'_inj : Function.Injective f' := by
          intro i j hij
          by_cases hi : i = u0 <;> by_cases hj : j = u0
          · exact hi.trans hj.symm
          · exfalso
            have hjS : j ∈ S := mem_erase.mpr ⟨hj, mem_univ j⟩
            exact ha_ne j hjS (by simpa [f', hi, hj] using hij.symm)
          · exfalso
            have hiS : i ∈ S := mem_erase.mpr ⟨hi, mem_univ i⟩
            exact ha_ne i hiS (by simpa [f', hi, hj] using hij)
          · exact f.injective (by simpa [f', hi, hj] using hij)
        have hf'_not_b : ∀ i : Fin r, f' i ≠ b := by
          intro i
          by_cases hi : i = u0
          · simp only [f', if_pos hi]
            exact hab.ne
          · simp only [f', if_neg hi]
            exact hb_ne i (mem_erase.mpr ⟨hi, mem_univ i⟩)
        let g := extendAt v b f'
        have hg_inj : Function.Injective g := extendAt_injective v b f' hf'_inj hf'_not_b
        apply free
        refine ⟨⟨⟨g, ?_⟩, hg_inj⟩⟩
        intro x y hadj
        by_cases hxv : x = v
        · rw [hxv] at hadj ⊢
          rw [(hv_adj_iff y).mp hadj]
          dsimp only [g]
          rw [extendAt_self, extendAt_succAbove]
          simp only [f', if_pos rfl]
          exact hab.symm
        · by_cases hyv : y = v
          · rw [hyv] at hadj ⊢
            rw [(hv_adj_iff x).mp hadj.symm]
            dsimp only [g]
            rw [extendAt_succAbove, extendAt_self]
            simp only [f', if_pos rfl]
            exact hab
          · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hxv
            obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hyv
            have hJ : J.Adj i j := hadj
            have hi_ne : i ≠ u0 := fun h => hiso j (h ▸ hJ)
            have hj_ne : j ≠ u0 := fun h => hiso i (h ▸ hJ.symm)
            dsimp only [g]
            rw [extendAt_succAbove, extendAt_succAbove]
            simp only [f', if_neg hi_ne, if_neg hj_ne]
            exact f.toHom.map_rel' hJ
    · obtain ⟨Z, hZX, hZ_edges, hZ_deg⟩ := peel_low_degree X (r + 1)
      have lJ : extremalNumber (Fintype.card (Fin n)) J < Z.edgeFinset.card := by
        rw [Fintype.card_fin]
        rw [edgeFinset_irrel X _ _] at large
        omega
      obtain ⟨f⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset (G := Z) (H := J) lJ
      obtain ⟨j0, hj0⟩ := exists_adj_iff_not_isIsolated.mpr hiso
      have hZ_adj : Z.Adj (f u0) (f j0) := f.toHom.map_rel' hj0
      have hZ_act : ¬ Z.IsIsolated (f u0) := fun h => h (f j0) hZ_adj
      have hX_deg : r + 1 ≤ X.degree (f u0) := by
        have h1 := hZ_deg (f u0) hZ_act
        have h2 := Z.degree_le_of_le hZX (v := f u0)
        rw [degree_irrel X (f u0) _ _]
        exact h1.trans h2
      have hfresh : ∃ w ∈ X.neighborFinset (f u0), w ∉ (univ : Finset (Fin r)).image f := by
        by_contra! hsub
        have hle := (card_le_card (show X.neighborFinset (f u0) ⊆ univ.image f from hsub)).trans
          card_image_le
        rw [X.card_neighborFinset_eq_degree (f u0), card_fin] at hle
        omega
      obtain ⟨w, hw_mem, hw_not⟩ := hfresh
      have hw_adj : X.Adj (f u0) w := (X.mem_neighborFinset _ _).mp hw_mem
      have hfw : ∀ i : Fin r, f i ≠ w := fun i eq => hw_not (eq ▸ mem_image_of_mem _ (mem_univ i))
      let g := extendAt v w f
      have hg_inj : Function.Injective g := extendAt_injective v w f f.injective hfw
      apply free
      refine ⟨⟨⟨g, ?_⟩, hg_inj⟩⟩
      intro x y hadj
      by_cases hxv : x = v
      · rw [hxv] at hadj ⊢
        rw [(hv_adj_iff y).mp hadj]
        dsimp only [g]
        rw [extendAt_self, extendAt_succAbove]
        exact hw_adj.symm
      · by_cases hyv : y = v
        · rw [hyv] at hadj ⊢
          rw [(hv_adj_iff x).mp hadj.symm]
          dsimp only [g]
          rw [extendAt_succAbove, extendAt_self]
          exact hw_adj
        · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hxv
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hyv
          dsimp only [g]
          rw [extendAt_succAbove, extendAt_succAbove]
          exact hZX (f.toHom.map_rel' hadj)

lemma nat_linear_isBigO (f : ℕ → ℕ) (C : ℕ) (h : ∀ n, f n ≤ C * n) :
    (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine IsBigO.of_bound (C : ℝ) ?_
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_natCast]
  exact_mod_cast h n

lemma nat_diff_isBigO (a b : ℕ → ℕ) (C N : ℕ)
    (hle : ∀ n ≥ N, a n ≤ b n) (hdiff : ∀ n ≥ N, b n ≤ a n + C * n) :
    (fun n : ℕ => (a n : ℝ) - (b n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine IsBigO.of_bound (C : ℝ) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have ha : (a n : ℝ) ≤ (b n : ℝ) := by exact_mod_cast hle n hn
  have hb : (b n : ℝ) ≤ (a n : ℝ) + (C : ℝ) * (n : ℝ) := by exact_mod_cast hdiff n hn
  rw [Real.norm_eq_abs, Real.norm_natCast, abs_of_nonpos (by linarith)]
  linarith

end Erdos713IIH1

open Filter Asymptotics SimpleGraph
open scoped Classical

theorem prove_Erdos713_ii_H1 :
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      (∃ v, G.degree v < 2) →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) ∨
        ∃ (r : ℕ) (J : SimpleGraph (Fin r)), r < q ∧ J.IsBipartite ∧ 2 ≤ J.edgeFinset.card ∧
          (fun n : ℕ => (extremalNumber n J : ℝ) - (extremalNumber n G : ℝ))
            =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  intro q G hbip hedges ⟨v0, hv0⟩
  by_cases h2 : G.edgeFinset.card ≤ 2
  · left
    have hacyc : G.IsAcyclic := Erdos713IIH1.isAcyclic_of_card_edgeFinset_le_two G h2
    exact Erdos713IIH1.nat_linear_isBigO (fun n => extremalNumber n G) q
      (fun n => Erdos713IIH1.forest_extremal_le G hacyc)
  · right
    have h3 : 3 ≤ G.edgeFinset.card := by omega
    have hq3 : 3 ≤ q := Erdos713IIH1.three_le_of_two_le_edges G hedges
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    let J : SimpleGraph (Fin r) := G.comap v0.succAboveEmb
    let emb : Copy J G := ⟨⟨v0.succAbove, fun h => h⟩, v0.succAboveEmb.injective⟩
    have hJG : J ⊑ G := ⟨emb⟩
    have hJ_bip : J.IsBipartite := Colorable.of_hom emb.toHom hbip
    have hJ_edges_eq : J.edgeFinset.card + G.degree v0 = G.edgeFinset.card :=
      Erdos713IIH1.card_edgeFinset_comap_succAbove G v0
    have hJ_edges : 2 ≤ J.edgeFinset.card := by omega
    refine ⟨r, J, Nat.lt_succ_self r, hJ_bip, hJ_edges, ?_⟩
    exact Erdos713IIH1.nat_diff_isBigO
      (fun n => extremalNumber n J)
      (fun n => extremalNumber n G)
      (r + 1) (r + 1)
      (fun n _ => hJG.extremalNumber_le)
      (fun n hn => Erdos713IIH1.extremal_diff_bound G v0 (by omega) hn)

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1.H1 :=
  prove_Erdos713_ii_H1
