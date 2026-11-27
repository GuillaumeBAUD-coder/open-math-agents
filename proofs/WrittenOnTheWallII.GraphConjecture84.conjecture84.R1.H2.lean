import OMAReductions.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1

/-!
# Step H2 of the reduction WrittenOnTheWallII.GraphConjecture84.conjecture84.R1

If the minimum degree is at least two, then `2 rad / δ ≤ rad`. A shortest path between
two vertices at distance `diam` induces a tree on `diam + 1` vertices, and `rad ≤ diam`.
After the merge, replace `h2` by `theorem OMA.solution : type_of% @OMA.R_..._R1.H2`.
-/

open SimpleGraph

namespace OMA.Step84H2

theorem h2 : ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj], G.Connected → 0 < G.minDegree → 2 ≤ G.minDegree →
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  intro α _ _ _ G _ hc _ h2
  -- the radius is at most the diameter
  obtain ⟨u0⟩ := (inferInstance : Nonempty α)
  have hne : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hc
  have hrd : G.radius.toNat ≤ G.diam :=
    ENat.toNat_le_toNat ((radius_le_eccent (u := u0)).trans eccent_le_ediam) hne
  -- a shortest path of length `diam` induces a tree
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  have hT := Walk.induce_support_isTree_of_length_eq_dist p hp
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup (p.isPath_of_length_eq_dist hp).support_nodup,
      p.length_support]
  have htree : G.diam + 1 ≤ largestInducedTreeSize G := by
    have := card_le_largestInducedTreeSize hT
    omega
  -- combine
  have hδ : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast h2
  have hr : (G.radius.toNat : ℝ) + 1 ≤ largestInducedTreeSize G := by
    exact_mod_cast (Nat.add_le_add_right hrd 1).trans htree
  have hpos : (0 : ℝ) < G.minDegree := by linarith
  rw [div_le_iff₀ hpos]
  have h0 : (0 : ℝ) ≤ G.radius.toNat := Nat.cast_nonneg _
  nlinarith

end OMA.Step84H2

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture84_conjecture84_R1.H2 := OMA.Step84H2.h2
