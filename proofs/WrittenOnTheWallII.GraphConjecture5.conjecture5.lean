import FormalConjectures.WrittenOnTheWallII.GraphConjecture5

-- Problem: Written on the Wall II - Conjecture 5
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture5.lean:45 (declaration WrittenOnTheWallII.GraphConjecture5.conjecture5)
-- Credit: @jonas-klesen (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea. Fix a centre `v` and let `r` be the radius, so every vertex is within distance `r`
-- of `v`. Give every vertex `w ≠ v` a parent: a neighbour one step closer to `v`. The parent
-- edges form a connected spanning subgraph `K` of `G`. A vertex at distance exactly `r` is the
-- parent of no vertex, so its only neighbour in `K` is its own parent. Hence it is a leaf of
-- every spanning tree of `K`, and such a tree has at least as many leaves as the sphere has
-- vertices.

open SimpleGraph

namespace OMAConjecture5

/-- Every vertex other than `v` has a neighbour one step closer to `v`. -/
lemma exists_parent {V : Type*} (G : SimpleGraph V) (hconn : G.Connected) (v w : V)
    (hne : w ≠ v) : ∃ w', G.Adj w w' ∧ G.dist v w' + 1 = G.dist v w := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist w v
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ w' _ h q =>
    refine ⟨w', h, ?_⟩
    have h1 : G.dist w' v ≤ q.length := dist_le q
    have h2 : G.dist w v ≤ G.dist w w' + G.dist w' v := hconn.dist_triangle
    have h3 : G.dist w w' = 1 := dist_eq_one_iff_adj.2 h
    have h4 : G.dist v w' = G.dist w' v := dist_comm
    have h5 : G.dist v w = G.dist w v := dist_comm
    rw [Walk.length_cons] at hp
    omega

/-- If every vertex is within distance `r` of `v`, some spanning tree has every vertex at
distance exactly `r` from `v` adjacent to at most one vertex, namely `p w`. -/
lemma exists_tree_sphere {V : Type*} (G : SimpleGraph V) (hconn : G.Connected) (v : V) (r : ℕ)
    (hle : ∀ w, G.dist v w ≤ r) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
      ∃ p : V → V, ∀ w, G.dist v w = r → ∀ y, T.Adj w y → y = p w := by
  classical
  have hpar : ∀ w, ∃ w', w ≠ v → (G.Adj w w' ∧ G.dist v w' + 1 = G.dist v w) := by
    intro w
    by_cases h : w = v
    · exact ⟨w, fun h' => absurd h h'⟩
    · obtain ⟨w', h'⟩ := exists_parent G hconn v w h
      exact ⟨w', fun _ => h'⟩
  choose p hp using hpar
  let K : SimpleGraph V := SimpleGraph.fromRel (fun x y => x ≠ v ∧ y = p x)
  have hKG : K ≤ G := by
    intro a b hab
    rw [SimpleGraph.fromRel_adj] at hab
    obtain ⟨-, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := hab
    · exact (hp a h1).1
    · exact (hp b h1).1.symm
  have hreach : ∀ n w, G.dist v w = n → K.Reachable w v := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rw [hconn.dist_eq_zero_iff] at hw
      subst hw
      exact Reachable.refl _
    | succ n ih =>
      intro w hw
      have hwv : w ≠ v := by
        rintro rfl
        simp at hw
      obtain ⟨h1, h2⟩ := hp w hwv
      have hK : K.Adj w (p w) := by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨h1.ne, Or.inl ⟨hwv, rfl⟩⟩
      exact hK.reachable.trans (ih (p w) (by omega))
  have hKconn : K.Connected :=
    K.connected_iff_exists_forall_reachable.2 ⟨v, fun w => (hreach _ w rfl).symm⟩
  obtain ⟨T, hTK, hT⟩ := hKconn.exists_isTree_le
  refine ⟨T, hTK.trans hKG, hT, p, ?_⟩
  intro w hw y hy
  have hK := hTK hy
  rw [SimpleGraph.fromRel_adj] at hK
  obtain ⟨-, ⟨-, h1⟩ | ⟨h1, h2⟩⟩ := hK
  · exact h1
  · have h3 := (hp y h1).2
    have h4 := hle y
    rw [← h2] at h3
    omega

/-- The number of leaves of a spanning tree of `G` is at most `Ls G`. -/
lemma leaves_le_Ls {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (T : SimpleGraph α) [DecidableRel T.Adj] (hTG : T ≤ G)
    (hT : T.IsTree) :
    ((Finset.univ.filter fun x => T.degree x = 1).card : ℝ) ≤ Ls G := by
  classical
  unfold Ls
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro _ ⟨S, -, rfl⟩
    exact Nat.cast_le.2 (Finset.card_le_univ _)
  · refine ⟨SimpleGraph.toSubgraph T hTG, ⟨SimpleGraph.toSubgraph.isSpanning T hTG, ?_⟩, ?_⟩
    · let e : (SimpleGraph.toSubgraph T hTG).coe ≃g T :=
        { toEquiv := Equiv.Set.univ α
          map_rel_iff' := Iff.rfl }
      exact e.isTree_iff.2 hT
    · show ((Finset.filter (fun v => (SimpleGraph.toSubgraph T hTG).degree v = 1)
        (SimpleGraph.toSubgraph T hTG).verts.toFinset).card : ℝ) = _
      congr 1
      apply Finset.card_bij (fun x _ => x)
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ x, ?_⟩
        rw [← hx.2]
        exact (SimpleGraph.degree_toSubgraph G T hTG).symm
      · intro x _ y _ h
        exact h
      · intro x hx
        rw [Finset.mem_filter] at hx
        refine ⟨x, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨Set.mem_toFinset.2 (Set.mem_univ x), ?_⟩
        rw [← hx.2]
        exact SimpleGraph.degree_toSubgraph G T hTG

end OMAConjecture5

open OMAConjecture5 in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture5.conjecture5 := by
  intro V _ _ _ G hconn
  classical
  have hrtop : G.radius ≠ ⊤ := radius_ne_top_iff.2 hconn
  apply csSup_le
  · obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
    exact ⟨_, u, hu, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : G.eccent v = G.radius := hv
    have hle : ∀ w, G.dist v w ≤ G.radius.toNat := fun w =>
      ENat.toNat_le_toNat (hv' ▸ G.edist_le_eccent) hrtop
    obtain ⟨T, hTG, hT, p, hp⟩ := exists_tree_sphere G hconn v _ hle
    refine le_trans ?_ (leaves_le_Ls G T hTG hT)
    refine Nat.cast_le.2 (Finset.card_le_card ?_)
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : 0 < T.degree w := hT.connected.preconnected.degree_pos_of_nontrivial w
    have h2 : T.neighborFinset w ⊆ {p w} := by
      intro y hy
      rw [mem_neighborFinset] at hy
      rw [Finset.mem_singleton]
      exact hp w hw.2 y hy
    have h3 := Finset.card_le_card h2
    rw [T.card_neighborFinset_eq_degree w, Finset.card_singleton] at h3
    omega
