import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1
/-! A branching tree has a proper induced subgraph containing a diametral path.
Equality of induced-subgraph counts transfers this path to the other tree. -/
namespace TreeDiam
open SimpleGraph
lemma path_dist {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist u v
  have he := (hG.isAcyclic.subsingleton_path u v).elim (⟨p,hp⟩ : G.Path u v) ⟨q,q.isPath_of_length_eq_dist hq⟩
  exact (congrArg (fun w : G.Path u v => w.1.length) he).trans hq

lemma span_impossible {V : Type} [Fintype V] {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {w : V} (hw : 3 ≤ (G.neighborSet w).ncard) : ∃ x, x ∉ p.support := by
  classical
  by_contra! hall
  let L := p.takeUntil w (hall w)
  let R := p.dropUntil w (hall w)
  have sub : G.neighborSet w ⊆ {L.penultimate, R.snd} := by
    intro x hx
    have mem := hall x
    rw [← p.take_spec (hall w), Walk.mem_support_append_iff] at mem
    rcases mem with h | h
    · exact Or.inl (hG.isAcyclic.eq_penultimate_of_adj_end (hp.takeUntil (hall w)) hx h)
    · exact Or.inr (hG.isAcyclic.eq_snd_of_adj_start (hp.dropUntil (hall w)) hx h)
  have bound := Set.ncard_le_ncard sub
  have small : ({L.penultimate, R.snd} : Set V).ncard ≤ 2 := by
    by_cases h : L.penultimate = R.snd <;> simp [h]
  omega

lemma transfer {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsTree) (hH : H.IsTree) (branch : ∃ w : V, 3 ≤ (G.neighborSet w).ncard)
    (copy : ∀ (S : Finset V), S.card < Fintype.card V → ∃ T : Finset W,
      Nonempty (H.induce (T : Set W) ≃g G.induce (S : Set V))) : G.diam ≤ H.diam := by
  classical
  have := hG.connected.nonempty
  have := hH.connected.nonempty
  obtain ⟨u,v,hdiam⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hlen⟩ := hG.connected.exists_walk_length_eq_dist u v
  have hp := p.isPath_of_length_eq_dist hlen
  let S := p.support.toFinset
  obtain ⟨w,hw⟩ := branch
  obtain ⟨x,hx⟩ := span_impossible hG hp hw
  have hs : S.card < Fintype.card V := Finset.card_lt_univ_of_notMem (x := x) (s := S) (by simpa [S] using hx)
  obtain ⟨T,⟨iso⟩⟩ := copy S hs
  have hsupp : ∀ a ∈ p.support, a ∈ (S : Set V) := by simp [S]
  let q := p.induce (S : Set V) hsupp
  have hmap : q.map (Embedding.induce (S : Set V)).toHom = p := Walk.map_induce p hsupp
  have hq : q.IsPath := (Walk.isPath_map_iff_of_injective (Embedding.induce (G := G) (S : Set V)).injective).mp (hmap ▸ hp)
  let i := (Embedding.induce (G := H) (T : Set W)).comp iso.symm.toEmbedding
  have him : (q.map i.toHom).IsPath := hq.map (f := i.toHom) i.injective
  have hdist := path_dist hH him
  have heq : q.length = p.length := (Walk.length_map (Embedding.induce (G := G) (S : Set V)).toHom q).symm.trans (congrArg Walk.length hmap)
  rw [Walk.length_map, heq, hlen, hdiam] at hdist
  exact hdist ▸ H.dist_le_diam (H.connected_iff_ediam_ne_top.mp hH.connected)

lemma diameter_two {V : Type} [Fintype V] {G : SimpleGraph V} (hG : G.IsTree)
    {w : V} (hw : 3 ≤ (G.neighborSet w).ncard) : 2 ≤ G.diam := by
  have := hG.connected.nonempty
  obtain ⟨a,ha,b,hb,hab⟩ := (Set.one_lt_ncard (s := G.neighborSet w)).mp (by omega)
  have ha' : G.Adj w a := ha
  have hb' : G.Adj w b := hb
  let p := Walk.cons ha'.symm hb'.toWalk
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    simp [p, Adj.toWalk, hab, ha'.ne.symm, hb'.ne]
  have hd : 2 = G.dist a b := by simpa [p, Adj.toWalk] using path_dist hG hp
  exact hd ▸ G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hG.connected)

theorem recover {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W)
    (hG : G.IsTree) (hH : H.IsTree)
    (deg : ∀ v, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    (br : ∃ w : V, 3 ≤ (G.neighborSet w).ncard)
    (ho : Odd G.diam)
    (counts : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U), Fintype.card U < Fintype.card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
      {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) :
    3 ≤ G.diam ∧ G.diam = H.diam := by
  classical
  obtain ⟨w,hw⟩ := br
  have hcard := Fintype.card_congr σ
  refine ⟨by obtain ⟨k,hk⟩ := ho; have := diameter_two hG hw; omega, le_antisymm ?_ ?_⟩
  · apply transfer hG hH ⟨w,hw⟩
    intro S hs
    let Q := G.induce (S : Set V)
    have he := counts (↥S) Q (by simpa using hs)
    have hn : 0 < {s : Finset V | Nonempty (G.induce (s : Set V) ≃g Q)}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨S, ⟨Iso.refl⟩⟩
    exact (Set.ncard_pos (Set.toFinite _)).mp (he ▸ hn)
  · apply transfer hH hG ⟨σ w, (deg w) ▸ hw⟩
    intro T ht
    let Q := H.induce (T : Set W)
    have he := counts (↥T) Q (by simpa [hcard] using ht)
    have hn : 0 < {t : Finset W | Nonempty (H.induce (t : Set W) ≃g Q)}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨T, ⟨Iso.refl⟩⟩
    exact (Set.ncard_pos (Set.toFinite _)).mp (he.symm ▸ hn)
end TreeDiam

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H1 := by
  intro V W _ _ _ G H σ hG hH deg br ho counts
  exact TreeDiam.recover G H σ hG hH deg br ho counts
