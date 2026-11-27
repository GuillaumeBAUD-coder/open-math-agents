import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

namespace OMA.wowB133H2

open SimpleGraph

lemma no_adj_gap {V : Type*} {G : SimpleGraph V} (hG : G.Connected) {u w : V}
    (p : G.Walk u w) (hp : p.length = G.dist u w) {a b : ℕ} (hab : a + 2 ≤ b)
    (hb : b ≤ p.length) : ¬ G.Adj (p.getVert a) (p.getVert b) := by
  intro hadj
  have h1 : G.dist u (p.getVert a) ≤ a := by
    have := dist_le (p.take a)
    rw [Walk.take_length] at this
    omega
  have h2 : G.dist (p.getVert b) w ≤ p.length - b := by
    have := dist_le (p.drop b)
    rwa [Walk.drop_length] at this
  have h3 : G.dist (p.getVert a) (p.getVert b) = 1 := dist_eq_one_iff_adj.mpr hadj
  have t1 := hG.dist_triangle (u := u) (v := p.getVert a) (w := w)
  have t2 := hG.dist_triangle (u := p.getVert a) (v := p.getVert b) (w := w)
  omega

lemma support_isInducedPath {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.Connected) {u w : V} (p : G.Walk u w) (hp : p.length = G.dist u w) :
    G.isInducedPath p.support := by
  refine ⟨(p.isPath_of_length_eq_dist hp).support_nodup, ?_⟩
  intro i j
  have hi : i.val ≤ p.length := by have := i.isLt; have := p.length_support; omega
  have hj : j.val ≤ p.length := by have := j.isLt; have := p.length_support; omega
  rw [List.get_eq_getElem, List.get_eq_getElem, p.support_getElem_eq_getVert,
    p.support_getElem_eq_getVert]
  constructor
  · intro hadj
    by_contra hne
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact no_adj_gap hG p hp (a := i.val) (b := j.val) (by omega) hj hadj
    · rw [h] at hadj
      exact G.irrefl hadj
    · exact no_adj_gap hG p hp (a := j.val) (b := i.val) (by omega) hi hadj.symm
  · rintro (h | h)
    · rw [← h]
      exact p.adj_getVert_succ (by omega)
    · rw [← h]
      exact (p.adj_getVert_succ (by omega)).symm

theorem rad_add_one_le_path {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) : G.radius.toNat + 1 ≤ SimpleGraph.path G := by
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite u
  have hne : G.edist u w ≠ ⊤ := edist_ne_top_iff_reachable.mpr (hG u w)
  have hrad : G.radius.toNat ≤ G.dist u w := by
    unfold SimpleGraph.dist
    rw [hw]
    exact ENat.toNat_le_toNat radius_le_eccent (hw ▸ hne)
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u w
  have := length_le_path_of_isInducedPath G p.support (support_isInducedPath hG p hp)
  rw [Walk.length_support] at this
  omega

theorem H2_proof :
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.path G : ℝ) := by
  intro α _ _ _ G hG _
  exact_mod_cast rad_add_one_le_path G hG

end OMA.wowB133H2


theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  unfold OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2
  exact OMA.wowB133H2.H2_proof
