import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

/-! A diameter path is induced. Its vertices occupy successive distance
layers from its first vertex, and an edge can cross at most one layer. -/

open SimpleGraph

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  intro α _ _ _ G hc _
  obtain ⟨u, v, hd⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp, hlen⟩ := hc.exists_path_of_dist u v
  have index_le (i : Fin p.support.length) : i.val ≤ p.length := by
    have := i.isLt
    have := p.length_support
    omega
  have vertex (i : Fin p.support.length) : p.support.get i = p.getVert i.val :=
    p.support_getElem_eq_getVert i.isLt
  have layer (i : Fin p.support.length) : G.dist u (p.getVert i.val) = i.val := by
    simpa [Walk.take_length, Nat.min_eq_left (index_le i)] using
      (length_eq_dist_of_subwalk hlen (p.isSubwalk_take i.val)).symm
  have induced : G.isInducedPath p.support := by
    refine ⟨hp.support_nodup, fun i j => ?_⟩
    rw [vertex, vertex]
    constructor
    · intro adj
      have hij : i.val ≠ j.val := fun he => adj.ne (congrArg p.getVert he)
      have ha := adj.diff_dist_adj (u := u)
      rw [layer, layer] at ha
      omega
    · rintro (h | h)
      · rw [← h]
        exact p.adj_getVert_succ (by have := index_le j; omega)
      · rw [← h]
        exact (p.adj_getVert_succ (by have := index_le i; omega)).symm
  have h := G.length_le_path_of_isInducedPath _ induced
  rw [p.length_support, hlen, hd] at h
  have hr : G.radius.toNat ≤ G.diam :=
    ENat.toNat_le_toNat G.radius_le_ediam (G.connected_iff_ediam_ne_top.mp hc)
  exact_mod_cast (by omega : G.radius.toNat + 1 ≤ G.path)
