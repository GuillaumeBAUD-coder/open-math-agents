import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# `τ(T) ≤ 2 γ_t(T)` for trees

Proof (the one sketched in the reduction): root the tree at `r` and take a total dominating set `D`
of minimum size. Let `P` be the set of vertices outside `D` that have a child outside `D`.
Then `D ∪ P` is a vertex cover, and each `v ∈ P` with such a child `w` maps to a child of `w`
lying in `D` (which exists because `w` is totally dominated and its parent is not in `D`);
that map is injective, so `|P| ≤ |D|`.

The only tree-specific input is that a vertex has at most one neighbour one level closer to the
root, which follows from uniqueness of paths in a tree.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Appending a single edge to a walk leaves the vertices of the walk unchanged. -/
private lemma getVert_append_cons_le {G : SimpleGraph α} {r w z : α} (q : G.Walk r w)
    (h : G.Adj w z) {i : ℕ} (hi : i ≤ q.length) :
    (q.append (Walk.cons h Walk.nil)).getVert i = q.getVert i := by
  rw [Walk.getVert_append]
  split_ifs with hlt
  · rfl
  · have hlen : i = q.length := by omega
    subst hlen
    rw [Nat.sub_self]
    simp [Walk.getVert_zero, Walk.getVert_length]

/-- In a tree, a vertex has at most one neighbour one level closer to any fixed root.

Two such neighbours would give two distinct simple paths of the same length from the root to a
common vertex, contradicting uniqueness of paths in a tree. -/
private lemma adj_unique_of_dist_eq_succ {T : SimpleGraph α} (hT : T.IsTree) (r : α) {z v w : α}
    (hzv : T.Adj z v) (hzw : T.Adj z w)
    (hv : T.dist r v + 1 = T.dist r z) (hw : T.dist r w + 1 = T.dist r z) : v = w := by
  obtain ⟨p, -, hplen⟩ := hT.connected.exists_path_of_dist r v
  obtain ⟨q, -, hqlen⟩ := hT.connected.exists_path_of_dist r w
  have hlenp : (p.append (Walk.cons hzv.symm Walk.nil)).length = T.dist r z := by
    rw [Walk.length_append, Walk.length_cons, Walk.length_nil]; omega
  have hlenq : (q.append (Walk.cons hzw.symm Walk.nil)).length = T.dist r z := by
    rw [Walk.length_append, Walk.length_cons, Walk.length_nil]; omega
  have hpz : (p.append (Walk.cons hzv.symm Walk.nil)).IsPath :=
    Walk.isPath_of_length_eq_dist _ hlenp
  have hqz : (q.append (Walk.cons hzw.symm Walk.nil)).IsPath :=
    Walk.isPath_of_length_eq_dist _ hlenq
  have heq : p.append (Walk.cons hzv.symm Walk.nil) = q.append (Walk.cons hzw.symm Walk.nil) :=
    (hT.existsUnique_path r z).unique hpz hqz
  have hpq : p.length = q.length := by omega
  have e1 : (p.append (Walk.cons hzv.symm Walk.nil)).getVert p.length = v := by
    rw [getVert_append_cons_le p hzv.symm le_rfl, Walk.getVert_length]
  have e2 : (q.append (Walk.cons hzw.symm Walk.nil)).getVert p.length = w := by
    rw [getVert_append_cons_le q hzw.symm (by omega), show p.length = q.length from hpq,
      Walk.getVert_length]
  rw [← e1, heq, e2]

/-- Every vertex of a tree with at least two vertices has a neighbour. -/
private lemma exists_adj_of_two_le_card {T : SimpleGraph α} (hT : T.IsTree)
    (hcard : 2 ≤ Fintype.card α) : ∀ v : α, ∃ w : α, T.Adj v w := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro v
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := hT.connected v w
  have hlen : 0 < p.length := by
    rcases Nat.eq_zero_or_pos p.length with h | h
    · exact absurd (by rw [← p.getVert_length, h, Walk.getVert_zero]) hw
    · exact h
  exact ⟨p.getVert 1, by simpa using p.adj_getVert_succ (i := 0) hlen⟩

/-- `τ(T) ≤ 2 γ_t(T)` for every tree of order at least two. -/
theorem tree_vertexCoverNum_toNat_le_two_mul_totalDominationNumber (T : SimpleGraph α)
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber := by
  classical
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let r : α := Classical.arbitrary α
  have hnoiso := exists_adj_of_two_le_card hT hcard
  -- a total dominating set of minimum size
  have hne : {n : ℕ | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card α, Finset.univ, ?_, by simp⟩
    intro v
    obtain ⟨w, hw⟩ := hnoiso v
    exact ⟨w, Finset.mem_univ w, hw⟩
  have hmem : T.totalDominationNumber ∈
      {n : ℕ | ∃ D : Finset α, T.IsTotalNDominatingSet n D} := by
    rw [totalDominationNumber]
    exact Nat.sInf_mem hne
  obtain ⟨D, hDdom, hDcard⟩ := hmem
  -- vertices outside `D` having a child outside `D`
  let P : Finset α := Finset.univ.filter fun v =>
    v ∉ D ∧ ∃ w : α, T.Adj v w ∧ w ∉ D ∧ T.dist r w = T.dist r v + 1
  let C : Finset α := D ∪ P
  have hmemP : ∀ v : α, v ∈ P ↔
      (v ∉ D ∧ ∃ w : α, T.Adj v w ∧ w ∉ D ∧ T.dist r w = T.dist r v + 1) := by
    intro v; simp [P]
  have hCcover : IsVertexCover T (C : Set α) := by
    intro x y hxy
    by_contra hcon
    have hxD : x ∉ D := fun h => hcon (Or.inl (by simp [C, h]))
    have hyD : y ∉ D := fun h => hcon (Or.inr (by simp [C, h]))
    have hxP : x ∉ P := fun h => hcon (Or.inl (by simp [C, h]))
    have hyP : y ∉ P := fun h => hcon (Or.inr (by simp [C, h]))
    rcases IsTree.dist_eq_dist_add_one_of_adj hT r hxy with h | h
    · exact hyP ((hmemP y).mpr ⟨hyD, x, hxy.symm, hxD, h⟩)
    · exact hxP ((hmemP x).mpr ⟨hxD, y, hxy, hyD, h⟩)
  -- the child of a witness which lies in `D`
  have hex : ∀ v ∈ P, ∃ z : α, z ∈ D ∧
      ∃ w : α, T.Adj v w ∧ w ∉ D ∧ T.dist r w = T.dist r v + 1 ∧ T.Adj w z ∧
        T.dist r z = T.dist r w + 1 := by
    intro v hv
    obtain ⟨hvD, w, hvw, hwD, hwdist⟩ := (hmemP v).mp hv
    obtain ⟨z, hzD, hwz⟩ := hDdom w
    rcases IsTree.dist_eq_dist_add_one_of_adj hT r hwz with h1 | h1
    · exfalso
      have hz : v = z := adj_unique_of_dist_eq_succ hT r hvw.symm hwz (by omega) (by omega)
      exact hvD (hz ▸ hzD)
    · exact ⟨z, hzD, w, hvw, hwD, hwdist, hwz, h1⟩
  let g : α → α := fun v => if hv : v ∈ P then Classical.choose (hex v hv) else v
  have hg_spec : ∀ v, v ∈ P → g v ∈ D ∧
      ∃ w : α, T.Adj v w ∧ w ∉ D ∧ T.dist r w = T.dist r v + 1 ∧ T.Adj w (g v) ∧
        T.dist r (g v) = T.dist r w + 1 := by
    intro v hv
    have hg : g v = Classical.choose (hex v hv) := by simp only [g, dif_pos hv]
    rw [hg]
    exact Classical.choose_spec (hex v hv)
  have hgD : ∀ v ∈ P, g v ∈ D := fun v hv => (hg_spec v hv).1
  have hginj : ∀ v ∈ P, ∀ v' ∈ P, g v = g v' → v = v' := by
    intro v hv v' hv' heq
    obtain ⟨-, w1, hvw1, -, hwdist1, hw1z, hdist1⟩ := hg_spec v hv
    obtain ⟨-, w2, hvw2, -, hwdist2, hw2z, hdist2⟩ := hg_spec v' hv'
    rw [← heq] at hdist2 hw2z
    have hw12 : w1 = w2 :=
      adj_unique_of_dist_eq_succ hT r hw1z.symm hw2z.symm hdist1.symm hdist2.symm
    subst hw12
    exact adj_unique_of_dist_eq_succ hT r hvw1.symm hvw2.symm hwdist1.symm hwdist2.symm
  have hPC : P.card ≤ D.card := by
    have hsub : P.image g ⊆ D := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact hgD v hv
    have hinj : (P.image g).card = P.card := Finset.card_image_of_injOn hginj
    rw [← hinj]
    exact Finset.card_le_card hsub
  have hCcard : C.card ≤ 2 * T.totalDominationNumber := by
    have h1 : C.card ≤ D.card + P.card := Finset.card_union_le D P
    omega
  have hvcn : T.vertexCoverNum ≤ (C.card : ℕ∞) := by
    have := hCcover.vertexCoverNum_le
    simpa using this
  calc T.vertexCoverNum.toNat ≤ (C.card : ℕ∞).toNat := ENat.toNat_le_toNat hvcn (by simp)
    _ = C.card := by simp
    _ ≤ 2 * T.totalDominationNumber := hCcard

end OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

theorem OMA.solution :
    OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 := by
  intro α _ _ T hT hcard
  exact OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.tree_vertexCoverNum_toNat_le_two_mul_totalDominationNumber
    T hT hcard
