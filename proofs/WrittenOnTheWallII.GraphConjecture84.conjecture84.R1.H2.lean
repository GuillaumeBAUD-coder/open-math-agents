import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

/-! A shortest path realizing the diameter induces a tree with one more vertex
than the diameter. For minimum degree at least two this gives the claimed bound. -/

open SimpleGraph

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2 := by
  intro α _ _ _ G _ hc hpos htwo
  obtain ⟨u, v, hd⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp, hlen⟩ := hc.exists_path_of_dist u v
  have ht := card_le_largestInducedTreeSize (p.induce_support_isTree_of_length_eq_dist hlen)
  rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hlen, hd] at ht
  have hr : G.radius.toNat ≤ G.diam :=
    ENat.toNat_le_toNat G.radius_le_ediam (G.connected_iff_ediam_ne_top.mp hc)
  apply (div_le_iff₀ (by exact_mod_cast hpos)).mpr
  have h : (G.radius.toNat : ℝ) ≤ largestInducedTreeSize G := by
    exact_mod_cast (by omega : G.radius.toNat ≤ largestInducedTreeSize G)
  have h' : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast htwo
  calc
    _ ≤ 2 * (largestInducedTreeSize G : ℝ) := by linarith
    _ ≤ _ := by rw [mul_comm]; gcongr
