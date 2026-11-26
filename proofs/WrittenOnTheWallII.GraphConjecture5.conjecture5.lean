import FormalConjectures.WrittenOnTheWallII.GraphConjecture5

/-! A shortest-path parent at every vertex gives a connected subgraph in
which the last distance layer consists of leaves. Credit: @Deldor14. -/
open SimpleGraph

namespace OMA.Spheres
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V}

private lemma descend (hc : G.Connected) (a x : V) (hx : x ≠ a) :
    ∃ y, G.Adj x y ∧ G.dist a y + 1 = G.dist a x := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a x
  have hpos : 0 < p.length := by
    rw [hp]; exact Nat.pos_of_ne_zero fun h => hx ((hc.dist_eq_zero_iff.mp h).symm)
  let i := p.length - 1
  have hi : i + 1 = p.length := by dsimp [i]; omega
  have he := p.adj_getVert_succ (show i < p.length by omega)
  rw [hi, p.getVert_length] at he
  refine ⟨_,he.symm,?_⟩
  have hv := length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  rw [Walk.take_length, Nat.min_eq_left (by omega)] at hv
  simpa [← hv,hi,hp]

open scoped Classical in
private lemma tree_layer (hc : G.Connected) (a : V) (r : ℕ)
    (hr : 0 < r) (hmax : ∀ x, G.dist a x ≤ r) :
    ∃ T : SimpleGraph V, ∃ ht : T ≤ G, T.IsTree ∧
      ∀ x, G.dist a x = r → (G.toSubgraph T ht).degree x = 1 := by
  classical
  have choice (x : V) : ∃ y, x ≠ a → G.Adj x y ∧ G.dist a y + 1 = G.dist a x := by
    by_cases h : x = a
    · exact ⟨a, fun hn => (hn h).elim⟩
    · obtain ⟨y,hy⟩ := descend hc a x h
      exact ⟨y, fun _ => hy⟩
  choose parent hpar using choice
  let H : SimpleGraph V := SimpleGraph.fromRel (fun x y => x ≠ a ∧ y = parent x)
  have hHG : H ≤ G := by
    rintro x y ⟨_, h | h⟩
    · obtain ⟨hx,rfl⟩ := h; exact (hpar x hx).1
    · obtain ⟨hy,rfl⟩ := h; exact (hpar y hy).1.symm
  let rec reach (x : V) : H.Reachable x a := by
    by_cases hx : x = a
    · subst x; exact .refl _
    · have had := (hpar x hx).1
      have he : H.Adj x (parent x) := ⟨had.ne,Or.inl ⟨hx,rfl⟩⟩
      exact he.reachable.trans (reach (parent x))
  termination_by G.dist a x
  decreasing_by have := (hpar x hx).2; omega
  have hH : H.Connected := ⟨fun u v => (reach u).trans (reach v).symm⟩
  obtain ⟨T, hTH, htree⟩ := hH.exists_isTree_le
  refine ⟨T, hTH.trans hHG, htree, ?_⟩
  intro x hx
  rw [SimpleGraph.degree_toSubgraph]
  have hpos := htree.connected.preconnected.degree_pos_of_nontrivial x
  have hsub : T.neighborFinset x ⊆ {parent x} := by
    intro y hy
    have he := hTH ((T.mem_neighborFinset x y).mp hy)
    change x ≠ y ∧ ((x ≠ a ∧ y = parent x) ∨ (y ≠ a ∧ x = parent y)) at he
    rcases he.2 with h | ⟨hy',h⟩
    · simpa using h.2
    · have hlevel := (hpar y hy').2
      rw [← h, hx] at hlevel
      have := hmax y
      omega
  have hle := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree, Finset.card_singleton] at hle
  omega

open scoped Classical in
private lemma leaves_bound [DecidableRel G.Adj] (T : SimpleGraph V) (ht : T ≤ G)
    (hT : T.IsTree) (s : Finset V) (hs : ∀ v ∈ s, (G.toSubgraph T ht).degree v = 1) :
    (s.card : ℝ) ≤ Ls G := by
  classical
  let S := G.toSubgraph T ht
  let leaves (Z : G.Subgraph) := Z.verts.toFinset.filter (fun v => Z.degree v = 1)
  have iso : S.coe ≃g T :=
    { toEquiv := Equiv.Set.univ V
      map_rel_iff' := by intros; rfl }
  have hS : S.IsSpanning ∧ S.coe.IsTree := ⟨SimpleGraph.toSubgraph.isSpanning T ht, iso.isTree_iff.mpr hT⟩
  have hj : s ⊆ leaves S := by
    intro v hv; exact Finset.mem_filter.mpr ⟨by simp [S], hs v hv⟩
  have hb : (s.card : ℝ) ≤ (leaves S).card := by exact_mod_cast Finset.card_le_card hj
  unfold Ls
  apply hb.trans
  apply le_csSup
  · refine ⟨(Fintype.card V : ℝ), ?_⟩
    rintro _ ⟨Z, _,rfl⟩
    dsimp only
    exact Nat.cast_le.mpr (Finset.card_le_univ _)
  · exact ⟨S,hS,rfl⟩

end OMA.Spheres

open OMA.Spheres in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture5.conjecture5 := by
  intro V _ _ _ G hc
  classical
  dsimp only
  apply csSup_le
  · obtain ⟨u,hu⟩ := G.exists_eccent_eq_radius
    exact ⟨_,u,hu,rfl⟩
  · rintro _ ⟨v,hv,rfl⟩
    change G.eccent v = G.radius at hv
    have htop := G.radius_ne_top_iff.mpr hc
    have hr : 0 < G.radius.toNat := by
      apply Nat.pos_of_ne_zero
      simp only [ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨hv ▸ G.eccent_ne_zero v, htop⟩
    have hmax (w : V) : G.dist v w ≤ G.radius.toNat :=
      ENat.toNat_le_toNat (hv ▸ G.edist_le_eccent (u := v) (v := w)) htop
    obtain ⟨T, ht, htree, hleaves⟩ := tree_layer hc v _ hr hmax
    apply leaves_bound T ht htree
    intro x hx
    exact hleaves x (Finset.mem_filter.mp hx).2
