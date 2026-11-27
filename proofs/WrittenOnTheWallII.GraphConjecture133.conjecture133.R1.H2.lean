import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

/-! A shortest walk between endpoints at the diameter is induced. A chord would
replace the intervening segment by one edge and contradict minimal length. -/

open SimpleGraph

private lemma shortest_induced {α : Type} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) :
    G.isInducedPath p.support := by
  refine ⟨(p.isPath_of_length_eq_dist hp).support_nodup, ?_⟩
  intro i j
  have bound (i : Fin p.support.length) : i.val ≤ p.length := by
    exact Nat.lt_succ_iff.mp (lt_of_lt_of_eq i.isLt p.length_support)
  have near (a b : ℕ) (ha : a ≤ p.length) (hb : b ≤ p.length)
      (adj : G.Adj (p.getVert a) (p.getVert b)) : b ≤ a+1 := by
    have cut := G.dist_le ((p.take a).append ((p.drop b).cons adj))
    rw [←hp] at cut
    simp [Walk.take_length, inf_eq_left.mpr ha] at cut
    omega
  rw [← p.getVert_comp_val_eq_get_support]
  change G.Adj (p.getVert i.val) (p.getVert j.val) ↔ _
  constructor
  · intro adj
    have h₁ := near i j (bound i) (bound j) adj
    have h₂ := near j i (bound j) (bound i) adj.symm
    have ne : i.val ≠ j.val := fun eq => adj.ne (congrArg p.getVert eq)
    omega
  · rintro (h|h)
    · rw [←h]
      exact p.adj_getVert_succ (by have := bound j; omega)
    · rw [←h]
      exact (p.adj_getVert_succ (by have := bound i; omega)).symm

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  intro α _ _ _ G connected _
  obtain ⟨u,v,e⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp⟩ := connected.exists_walk_length_eq_dist u v
  have longest := G.length_le_path_of_isInducedPath p.support (shortest_induced p hp)
  rw [p.length_support, hp, e] at longest
  have rad : G.radius.toNat ≤ G.diam :=
    ENat.toNat_le_toNat G.radius_le_ediam (G.connected_iff_ediam_ne_top.mp connected)
  exact_mod_cast (show G.radius.toNat + 1 ≤ G.path by omega)
