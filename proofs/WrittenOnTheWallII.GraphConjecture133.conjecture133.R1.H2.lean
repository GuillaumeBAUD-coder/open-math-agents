import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

namespace OMA.ShortestInducedPath
open SimpleGraph

lemma levels {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    {u v : V} (p : G.Walk u v) (hlen : p.length = G.dist u v)
    (i : ℕ) (hi : i ≤ p.length) : G.dist u (p.getVert i) = i := by
  have htake := G.dist_le (p.take i)
  rw [p.take_length, Nat.min_eq_left hi] at htake
  have hdrop := G.dist_le (p.drop i)
  rw [p.drop_length] at hdrop
  have htri := hconn.dist_triangle (u := u) (v := p.getVert i) (w := v)
  rw [← hlen] at htri
  omega

lemma induced {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hconn : G.Connected) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length = G.dist u v) : G.isInducedPath p.support := by
  refine ⟨hp.support_nodup, ?_⟩
  intro i j
  have hi : i.val ≤ p.length := Nat.le_of_lt_succ (i.isLt.trans_eq p.length_support)
  have hj : j.val ≤ p.length := Nat.le_of_lt_succ (j.isLt.trans_eq p.length_support)
  change G.Adj p.support[i.val] p.support[j.val] ↔ _
  rw [← p.getVert_eq_support_getElem hi, ← p.getVert_eq_support_getElem hj]
  constructor
  · intro hadj
    have hd := hadj.diff_dist_adj (u := u)
    rw [levels hconn p hlen i.val hi, levels hconn p hlen j.val hj] at hd
    have hne : i.val ≠ j.val := by
      intro he
      rw [he] at hadj
      exact hadj.ne rfl
    omega
  · rintro (h | h)
    · rw [← h]
      exact p.adj_getVert_succ (by omega)
    · rw [← h]
      exact (p.adj_getVert_succ (by omega)).symm

end OMA.ShortestInducedPath

-- Step WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture133.conjecture133.R1
-- Credit: @DeepDuke
-- H2 := ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →     (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧       G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →     (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.path G : ℝ)

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  intro V _ _ _ G hconn hC4
  classical
  obtain ⟨u,v,hrad⟩ := G.exists_edist_eq_radius_of_finite
  obtain ⟨p,hp,hlen⟩ := hconn.exists_path_of_dist u v
  have hi := G.length_le_path_of_isInducedPath p.support
    (OMA.ShortestInducedPath.induced hconn p hp hlen)
  rw [p.length_support, hlen] at hi
  have hr : G.radius.toNat = G.dist u v := by
    rw [← hrad]
    rfl
  rw [hr]
  exact_mod_cast hi

