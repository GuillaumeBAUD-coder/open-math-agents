import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

-- Step WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture133.conjecture133.R1
-- Credit: @carterleffen
-- H2 := ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →     (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧       G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →     (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.path G : ℝ)

/-!
Pick a vertex `u` and a vertex `v` at distance `ecc u` from it. A shortest walk from `u` to `v`
has its `i`-th vertex at distance exactly `i` from `u`, so two of its vertices are adjacent only
when their indices differ by one. It is therefore an induced path on `dist u v + 1` vertices,
and `radius ≤ ecc u = dist u v`. The four-cycle hypothesis is not needed.
Reduction WrittenOnTheWallII.GraphConjecture133.conjecture133.R1 by @jagong-cmu.
-/

open SimpleGraph

namespace OMA.WOW133H2

/-- Every vertex of a shortest walk lies at distance equal to its index from the start. -/
lemma dist_getVert_of_shortest {α : Type} (G : SimpleGraph α) (hG : G.Connected) {u v : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (i : ℕ) (hi : i ≤ G.dist u v) :
    G.dist u (p.getVert i) = i := by
  apply le_antisymm
  · have h := G.dist_le (p.take i)
    rw [Walk.take_length] at h
    omega
  · have h1 := G.dist_le (p.drop i)
    rw [Walk.drop_length] at h1
    have h2 := (hG.preconnected u (p.getVert i)).dist_triangle_left v
    omega

theorem radius_add_one_le_path {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (hG : G.Connected) [Nonempty α] :
    G.radius.toNat + 1 ≤ SimpleGraph.path G := by
  classical
  obtain ⟨u⟩ : Nonempty α := inferInstance
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  obtain ⟨p, -, hp⟩ := hG.exists_path_of_dist u v
  have hrad : G.radius.toNat ≤ G.dist u v := by
    apply ENat.toNat_le_of_le_natCast
    rw [(hG.preconnected u v).coe_dist_eq_edist, hv]
    exact G.radius_le_eccent
  let l : List α := List.ofFn (fun k : Fin (G.dist u v + 1) => p.getVert k)
  have hlen : l.length = G.dist u v + 1 := List.length_ofFn
  have hget (k : Fin l.length) : l.get k = p.getVert k.val := by
    simp only [l, List.get_eq_getElem, List.getElem_ofFn]
  have hl : G.isInducedPath l := by
    refine ⟨?_, ?_⟩
    · rw [List.nodup_ofFn]
      intro a b hab
      have ha := dist_getVert_of_shortest G hG p hp a (Nat.lt_succ_iff.mp a.isLt)
      have hb := dist_getVert_of_shortest G hG p hp b (Nat.lt_succ_iff.mp b.isLt)
      simp only at hab
      rw [hab] at ha
      exact Fin.ext (ha.symm.trans hb)
    · intro i j
      rw [hget, hget]
      have hi : i.val ≤ G.dist u v := by have := i.isLt; omega
      have hj : j.val ≤ G.dist u v := by have := j.isLt; omega
      constructor
      · intro hadj
        have hne : i.val ≠ j.val := fun e => hadj.ne (by rw [e])
        have h := hadj.diff_dist_adj (u := u)
        rw [dist_getVert_of_shortest G hG p hp _ hi,
          dist_getVert_of_shortest G hG p hp _ hj] at h
        omega
      · rintro (h | h)
        · rw [← h]
          exact p.adj_getVert_succ (by omega)
        · rw [← h]
          exact (p.adj_getVert_succ (by omega)).symm
  have hpath := length_le_path_of_isInducedPath G l hl
  omega

end OMA.WOW133H2

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  intro α _ _ _ G hG _
  have : Nonempty α := inferInstance
  exact_mod_cast OMA.WOW133H2.radius_add_one_le_path G hG
