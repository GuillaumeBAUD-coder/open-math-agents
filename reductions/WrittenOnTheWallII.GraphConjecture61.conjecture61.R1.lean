import FormalConjectures.WrittenOnTheWallII.GraphConjecture61

-- Reduction WrittenOnTheWallII.GraphConjecture61.conjecture61.R1 of Written on the Wall II - Conjecture 61
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Split off the cases settled by the residue bound

The target is `residue + ceil (diam / 3) ≤ f` for connected graphs, where `f` is the order of a
largest induced forest. This file does not prove it. It proves the bound

  `indepNum + (diam + 3) / 4 ≤ f`

for every connected graph (natural number division), and leaves two hypotheses.

Proof of the bound. Let `I` be a maximum independent set and take a shortest walk of length
`diam`. For each `k` with `4 k + 1 ≤ diam` the vertices number `4 k` and `4 k + 1` of the walk
are adjacent, so one of them is outside `I`. The `(diam + 3) / 4` chosen vertices are pairwise
at distance at least three. A set `J` of such vertices together with `I` induces a forest:
every edge joins `I` to `J`, and its end in `I` has no second neighbour in `J`, so it is a leaf.

* `H1` is the theorem of Favaron, Maheo and Sacle (1991): `residue ≤ indepNum`. It is a known
  result, stated here exactly as step `H1` of the merged reduction
  `Arxiv.2507.17780.tx_graffiti_conjecture_1.R1`.
* `H2` is what is left of the conjecture: connected graphs with
  `indepNum + (diam + 3) / 4 < residue + ceil (diam / 3)`. With `H1` this forces
  `diam ≥ 4` and `diam ∉ {5, 6, 9}`, and for `diam ≤ 15` it forces `residue = indepNum`.
  This part is open. An exhaustive search over all connected graphs on at most ten
  vertices finds no counterexample to the conjecture.

The bound cannot be improved in terms of `indepNum` and `diam` alone when `diam` is even
(chains of four-cycles sharing cut vertices), so the remaining case needs the residue itself.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture61_conjecture61_R1

open SimpleGraph

/-- Favaron, Maheo, Sacle (1991): the Havel-Hakimi residue is at most the independence number. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.residue ≤ G.indepNum

/-- The open remainder: graphs whose independence number is too close to the residue for the
bound `indepNum + (diam + 3) / 4 ≤ f` to settle the conjecture. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.Connected → 4 ≤ G.diam →
    (G.indepNum : ℝ) + ((G.diam + 3) / 4 : ℕ) < (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ →
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ)

section forest

variable {W : Type*}

/-- A graph in which every edge has an endpoint of degree one is acyclic. -/
lemma isAcyclic_of_leaf_edges (H : SimpleGraph W)
    (h : ∀ x y, H.Adj x y → (∀ z, H.Adj x z → z = y) ∨ (∀ z, H.Adj y z → z = x)) :
    H.IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  rw [isBridge_iff]
  have key : ∀ a b : W, H.Adj a b → (∀ z, H.Adj a z → z = b) →
      ¬ (H.deleteEdges {s(a, b)}).Reachable a b := by
    intro a b hab ha
    rintro ⟨p⟩
    cases p with
    | nil => exact hab.ne rfl
    | cons hadj q =>
      rename_i c
      rw [deleteEdges_adj] at hadj
      have h2 : c = b := ha c hadj.1
      subst h2
      exact hadj.2 rfl
  rcases h x y hxy with hx | hy
  · exact key x y hxy hx
  · intro hr
    have := key y x hxy.symm hy
    rw [Sym2.eq_swap] at this
    exact this hr.symm

lemma card_le_forest [Fintype W] (G : SimpleGraph W) (s : Finset W) (hs : (G.induce (s : Set W)).IsAcyclic) :
    s.card ≤ G.largestInducedForestSize := by
  unfold largestInducedForestSize
  apply le_csSup
  · refine ⟨Fintype.card W, ?_⟩
    rintro n ⟨t, -, rfl⟩
    exact Finset.card_le_univ t
  · exact ⟨s, hs, rfl⟩

/-- Along a shortest walk, the distance from the start to the `i`-th vertex is `i`. -/
lemma dist_getVert_of_shortest {G : SimpleGraph W} (hc : G.Connected) {u v : W}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (i : ℕ) (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have h1 : G.dist u (p.getVert i) ≤ i := by
    have := dist_le (p.take i)
    rw [Walk.take_length] at this
    omega
  have h2 : G.dist (p.getVert i) v ≤ p.length - i := by
    have := dist_le (p.drop i)
    rw [Walk.drop_length] at this
    exact this
  have h3 := hc.dist_triangle (u := u) (v := p.getVert i) (w := v)
  omega

/-- Two vertices of a shortest walk are at least as far apart as their indices. -/
lemma le_dist_getVert {G : SimpleGraph W} (hc : G.Connected) {u v : W}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    j - i ≤ G.dist (p.getVert i) (p.getVert j) := by
  have h1 := dist_getVert_of_shortest hc p hp i (hij.trans hj)
  have h2 := dist_getVert_of_shortest hc p hp j hj
  have h3 := hc.dist_triangle (u := u) (v := p.getVert i) (w := p.getVert j)
  omega

/-- Outside an independent set there are `(diam + 3) / 4` vertices pairwise at distance at least
three: on a shortest walk of length `diam`, take one of the vertices `4k`, `4k + 1`. -/
lemma exists_packing [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W)
    (hc : G.Connected) (I : Finset W) (hI : G.IsIndepSet (I : Set W)) :
    ∃ J : Finset W, Disjoint I J ∧ (∀ a ∈ J, ∀ b ∈ J, a ≠ b → 3 ≤ G.dist a b) ∧
      (G.diam + 3) / 4 ≤ J.card := by
  classical
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  have hlen : p.length = G.diam := hp.trans huv
  let c : ℕ → ℕ := fun k => if p.getVert (4 * k) ∈ I then 4 * k + 1 else 4 * k
  have hc_lo : ∀ k, 4 * k ≤ c k := by
    intro k; simp only [c]; split_ifs <;> omega
  have hc_hi : ∀ k, c k ≤ 4 * k + 1 := by
    intro k; simp only [c]; split_ifs <;> omega
  have hnot : ∀ k, 4 * k + 1 ≤ p.length → p.getVert (c k) ∉ I := by
    intro k hk
    simp only [c]
    split_ifs with h
    · intro h'
      have hadj : G.Adj (p.getVert (4 * k)) (p.getVert (4 * k + 1)) :=
        p.adj_getVert_succ (by omega)
      exact hI (Finset.mem_coe.mpr h) (Finset.mem_coe.mpr h') hadj.ne hadj
    · exact h
  let T := (G.diam + 3) / 4
  have hT : ∀ k, k < T → 4 * k + 1 ≤ p.length := by
    intro k hk
    simp only [T] at hk
    omega
  have hfar : ∀ k k', k < k' → k' < T →
      3 ≤ G.dist (p.getVert (c k)) (p.getVert (c k')) := by
    intro k k' hkk hk'
    have h1 := hc_hi k
    have h2 := hc_lo k'
    have h3 := hc_hi k'
    have h4 := hT k' hk'
    have := le_dist_getVert hc p hp (c k) (c k') (by omega) (by omega)
    omega
  have hinj : Set.InjOn (fun k => p.getVert (c k)) (Finset.range T : Set ℕ) := by
    intro k hk k' hk' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hfar k k' hlt hk'
      simp only at heq
      rw [heq, SimpleGraph.dist_self] at this
      omega
    · have := hfar k' k hlt hk
      simp only at heq
      rw [heq, SimpleGraph.dist_self] at this
      omega
  refine ⟨(Finset.range T).image (fun k => p.getVert (c k)), ?_, ?_, ?_⟩
  · rw [Finset.disjoint_right]
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    exact hnot k (hT k (Finset.mem_range.mp hk))
  · intro a ha b hb hab
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hb
    have hk := Finset.mem_range.mp hk
    have hk' := Finset.mem_range.mp hk'
    have hne : k ≠ k' := fun h => hab (by rw [h])
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hfar k k' hlt hk'
    · rw [SimpleGraph.dist_comm]
      exact hfar k' k hlt hk
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- An independent set together with vertices pairwise at distance at least three induces a
forest: every edge joins the two parts and its end in the independent set is a leaf. -/
lemma isAcyclic_induce_union [DecidableEq W] (G : SimpleGraph W) (hc : G.Connected)
    (I J : Finset W) (hI : G.IsIndepSet (I : Set W))
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → 3 ≤ G.dist a b) :
    (G.induce ((I ∪ J : Finset W) : Set W)).IsAcyclic := by
  apply isAcyclic_of_leaf_edges
  have notJJ : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b := by
    intro a ha b hb hab
    have := hJ a ha b hb hab.ne
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab] at this
    omega
  have leaf : ∀ x y : ((I ∪ J : Finset W) : Set W),
      (G.induce ((I ∪ J : Finset W) : Set W)).Adj x y → (x : W) ∈ I →
      ∀ z, (G.induce ((I ∪ J : Finset W) : Set W)).Adj x z → z = y := by
    intro x y hxy hx z hxz
    have hxy' : G.Adj x y := hxy
    have hxz' : G.Adj x z := hxz
    have memJ : ∀ w : ((I ∪ J : Finset W) : Set W), G.Adj x w → (w : W) ∈ J := by
      intro w hw
      have hw' := w.2
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hw'
      rcases hw' with hw' | hw'
      · exact absurd hw (hI (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hw') hw.ne)
      · exact hw'
    have hyJ := memJ y hxy'
    have hzJ := memJ z hxz'
    by_contra hne
    have hne' : (z : W) ≠ y := fun h => hne (Subtype.ext h)
    have h3 := hJ z hzJ y hyJ hne'
    have h1 : G.dist (z : W) x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxz'.symm
    have h2 : G.dist (x : W) y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy'
    have h4 := hc.dist_triangle (u := (z : W)) (v := x) (w := y)
    omega
  intro x y hxy
  have hxy' : G.Adj x y := hxy
  by_cases hx : (x : W) ∈ I
  · exact Or.inl (leaf x y hxy hx)
  · right
    have hxJ : (x : W) ∈ J := by
      have hx' := x.2
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx'
      exact hx'.resolve_left hx
    have hy : (y : W) ∈ I := by
      have hy' := y.2
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hy'
      rcases hy' with hy' | hy'
      · exact hy'
      · exact absurd hxy' (notJJ x hxJ y hy')
    exact leaf y x hxy.symm hy

/-- In a connected graph, `indepNum + (diam + 3) / 4` is at most the order of a largest induced
forest. -/
lemma indepNum_add_le_forest [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W)
    (hc : G.Connected) : G.indepNum + (G.diam + 3) / 4 ≤ G.largestInducedForestSize := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hind : G.IsIndepSet (I : Set W) := hI.1
  have hcard : I.card = G.indepNum := hI.2
  obtain ⟨J, hdisj, hfar, hJ⟩ := exists_packing G hc I hind
  have hacyc := isAcyclic_induce_union G hc I J hind hfar
  have := card_le_forest G (I ∪ J) hacyc
  rw [Finset.card_union_of_disjoint hdisj, hcard] at this
  omega

end forest

section transfer

variable {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}

lemma edist_hom_le (f : G →g K) (u v : V) : K.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    calc K.edist (f u) (f v) ≤ ((p.map f).length : ℕ∞) := SimpleGraph.edist_le _
      _ = (p.length : ℕ∞) := by simp
  · rw [edist_eq_top_of_not_reachable h]
    exact le_top

lemma edist_iso (e : G ≃g K) (u v : V) : K.edist (e u) (e v) = G.edist u v := by
  apply le_antisymm (edist_hom_le e.toHom u v)
  have := edist_hom_le e.symm.toHom (e u) (e v)
  simpa using this

lemma diam_iso (e : G ≃g K) : K.diam = G.diam := by
  unfold SimpleGraph.diam
  congr 1
  rw [ediam_eq_iSup_iSup_edist, ediam_eq_iSup_iSup_edist, ← e.surjective.iSup_comp]
  congr 1
  funext u
  rw [← e.surjective.iSup_comp]
  simp only [edist_iso]

lemma residue_iso [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    [DecidableRel G.Adj] [DecidableRel K.Adj] (e : G ≃g K) :
    residue K = residue G := by
  unfold residue
  congr 2
  have h1 : (Finset.univ : Finset W) = (Finset.univ : Finset V).map e.toEquiv.toEmbedding := by
    simp
  rw [h1, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro v _
  exact e.degree_eq v

lemma forest_iso_le [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (e : G ≃g K) :
    largestInducedForestSize K ≤ largestInducedForestSize G := by
  unfold largestInducedForestSize
  apply csSup_le'
  rintro n ⟨t, ht, rfl⟩
  let s : Finset V := t.map e.symm.toEquiv.toEmbedding
  have hbij : Set.BijOn e (s : Set V) (t : Set W) := by
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using hy
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe]
      exact ⟨y, hy, rfl⟩
  have hs : (G.induce (s : Set V)).IsAcyclic := (Iso.induce e hbij).isAcyclic_iff.mpr ht
  have hcard : s.card = t.card := by simp [s]
  have := card_le_forest G s hs
  unfold largestInducedForestSize at this
  omega

end transfer

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture61.conjecture61 := by
  intro h1 h2 α _ _ _ G _ hc
  classical
  let e := Fintype.equivFin α
  let K : SimpleGraph (Fin (Fintype.card α)) := G.map e.toEmbedding
  let i : G ≃g K := SimpleGraph.Iso.map e G
  have : Nontrivial (Fin (Fintype.card α)) :=
    Fin.nontrivial_iff_two_le.mpr Fintype.one_lt_card
  have hc' : K.Connected := i.connected_iff.mp hc
  have hres : residue K = residue G := residue_iso i
  have hdiam : K.diam = G.diam := diam_iso i
  have hfor : largestInducedForestSize K ≤ largestInducedForestSize G := forest_iso_le i
  have key : (residue K : ℝ) + ⌈(K.diam : ℝ) / 3⌉ ≤ (K.largestInducedForestSize : ℝ) := by
    by_cases hgap : (K.indepNum : ℝ) + ((K.diam + 3) / 4 : ℕ) <
        (residue K : ℝ) + ⌈(K.diam : ℝ) / 3⌉
    · have hR : residue K ≤ K.indepNum := h1 _ K
      have hceil : ⌈(K.diam : ℝ) / 3⌉ ≤ (((K.diam + 2) / 3 : ℕ) : ℤ) := by
        apply Int.ceil_le.mpr
        have h3 : K.diam ≤ ((K.diam + 2) / 3) * 3 := by omega
        have h3' : (K.diam : ℝ) ≤ (((K.diam + 2) / 3 : ℕ) : ℝ) * 3 := by exact_mod_cast h3
        rw [div_le_iff₀ (by norm_num)]
        exact_mod_cast h3'
      have hgap' : (K.indepNum : ℤ) + (((K.diam + 3) / 4 : ℕ) : ℤ) <
          (residue K : ℤ) + ⌈(K.diam : ℝ) / 3⌉ := by
        have h : (((K.indepNum : ℤ) + (((K.diam + 3) / 4 : ℕ) : ℤ) : ℤ) : ℝ) <
            (((residue K : ℤ) + ⌈(K.diam : ℝ) / 3⌉ : ℤ) : ℝ) := by
          push_cast
          exact hgap
        exact Int.cast_lt.mp h
      have hd' : 4 ≤ K.diam := by
        by_contra hlt
        omega
      exact h2 _ K hc' hd' hgap
    · have hf : ((K.indepNum + (K.diam + 3) / 4 : ℕ) : ℝ) ≤
          (K.largestInducedForestSize : ℝ) := by
        exact_mod_cast indepNum_add_le_forest K hc'
      push_cast at hf
      linarith
  rw [← hres, ← hdiam]
  exact key.trans (by exact_mod_cast hfor)

end OMA.R_WrittenOnTheWallII_GraphConjecture61_conjecture61_R1
