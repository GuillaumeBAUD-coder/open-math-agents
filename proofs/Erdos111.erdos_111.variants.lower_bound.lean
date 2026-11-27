import FormalConjectures.ErdosProblems.«111»
import Mathlib.Combinatorics.Compactness

/-!
# The linear edge-deletion bound for Erdős Problem 111

A countable coloring would exist if finite vertex sets met every bounded-size
non-bipartite induced subgraph. Disjoint finite obstructions then give the bound.
-/

open Cardinal Erdos111 Filter SimpleGraph

namespace OMA

private theorem chromatic_le_mk {V C : Type} {G : SimpleGraph V}
    (coloring : G.Coloring C) : G.chromaticCardinal ≤ Cardinal.mk C := by
  exact csInf_le (OrderBot.bddBelow _) ⟨C, rfl, ⟨coloring⟩⟩

private theorem bipartite_of_finite_subgraphs {V : Type} {G : SimpleGraph V}
    (localColors : ∀ S : Finset V, (G.induce (S : Set V)).IsBipartite) :
    G.IsBipartite := by
  classical
  obtain ⟨color, hcolor⟩ :=
    Finset.rado_selection_subtype (β := fun _ : V => Fin 2) (fun S => (localColors S).some)
  refine ⟨Coloring.mk color ?_⟩
  intro v w adjacency equalColor
  let S : Finset V := {v, w}
  let vS : S := ⟨v, by simp [S]⟩
  let wS : S := ⟨w, by simp [S]⟩
  obtain ⟨T, inclusion, agrees⟩ := hcolor S
  have edge : (G.induce (T : Set V)).Adj (Set.inclusion inclusion vS)
      (Set.inclusion inclusion wS) := adjacency
  apply (localColors T).some.valid edge
  exact (agrees vS).symm.trans (equalColor.trans (agrees wS))

-- If every size bound had a finite hitting set, their union would leave a bipartite graph.
private theorem bounded_obstructions {V : Type} (G : SimpleGraph V)
    (hG : ℵ₀ < G.chromaticCardinal) :
    ∃ m : ℕ, ∀ D : Finset V, ∃ S : Finset V, S.card ≤ m ∧ Disjoint S D ∧
      ¬ (G.induce (S : Set V)).IsBipartite := by
  classical
  by_contra! missing
  choose blocker hblocker using missing
  let U : Set V := ⋃ m, (blocker m : Set V)
  have countU : Countable U :=
    (Set.countable_iUnion fun m => (blocker m).finite_toSet.countable).to_subtype
  have complementBipartite : (G.induce Uᶜ).IsBipartite := by
    apply bipartite_of_finite_subgraphs
    intro S
    let T : Finset V := S.image Subtype.val
    have disj : Disjoint T (blocker T.card) := by
      refine Finset.disjoint_left.mpr ?_
      intro v hv hvBlock
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact w.property (Set.mem_iUnion_of_mem T.card hvBlock)
    have bip := hblocker T.card T le_rfl disj
    refine Colorable.of_hom ?_ bip
    refine ⟨fun w => ⟨w.val.val, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨w.val, w.property, rfl⟩
    · exact fun adjacency => adjacency
  let color (v : V) : U ⊕ Fin 2 :=
    if hv : v ∈ U then Sum.inl ⟨v, hv⟩ else Sum.inr (complementBipartite.some ⟨v, hv⟩)
  have coloring : G.Coloring (U ⊕ Fin 2) := by
    refine Coloring.mk color ?_
    intro v w adjacency
    by_cases hv : v ∈ U <;> by_cases hw : w ∈ U
    · intro eq
      have eqSub : (⟨v, hv⟩ : U) = ⟨w, hw⟩ := by simpa [color, hv, hw] using eq
      exact adjacency.ne (congrArg Subtype.val eqSub)
    · simp [color, hv, hw]
    · simp [color, hv, hw]
    · simpa [color, hv, hw] using
        (complementBipartite.some.valid (v := ⟨v, hv⟩) (w := ⟨w, hw⟩) adjacency)
  exact (not_le_of_gt hG) ((chromatic_le_mk coloring).trans Cardinal.mk_le_aleph0)

-- Greedily adjoin an obstruction disjoint from the old vertex set.
private theorem pack_obstructions {V : Type} (G : SimpleGraph V) {m : ℕ}
    (small : ∀ D : Finset V, ∃ S : Finset V, S.card ≤ m ∧ Disjoint S D ∧
      ¬ (G.induce (S : Set V)).IsBipartite) (k : ℕ) :
    ∃ T : Finset V, T.card ≤ k * m ∧ ∀ D : Finset V, D.card < k →
      ∃ S : Finset V, S ⊆ T ∧ Disjoint S D ∧ ¬ (G.induce (S : Set V)).IsBipartite := by
  classical
  induction k with
  | zero =>
    exact ⟨∅, by simp, fun D hD => (Nat.not_lt_zero D.card hD).elim⟩
  | succ k ih =>
    obtain ⟨T, hT, pack⟩ := ih
    obtain ⟨S, hS, hST, hBad⟩ := small T
    refine ⟨T ∪ S, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hST.symm, Nat.succ_mul]
      exact Nat.add_le_add hT hS
    · intro D hD
      by_cases hSD : Disjoint S D
      · exact ⟨S, Finset.subset_union_right, hSD, hBad⟩
      have smaller : (D \ S).card < D.card := by
        obtain ⟨v, hvS, hvD⟩ := Finset.not_disjoint_iff.mp hSD
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩)
        intro eq
        have hmem : v ∈ D \ S := eq.symm ▸ hvD
        exact (Finset.mem_sdiff.mp hmem).2 hvS
      obtain ⟨A, hAT, hAD, hA⟩ := pack (D \ S) (by omega)
      refine ⟨A, hAT.trans Finset.subset_union_left, Finset.disjoint_left.mpr ?_, hA⟩
      intro v hvA hvD
      exact Finset.disjoint_left.mp hAD hvA
        (Finset.mem_sdiff.mpr ⟨hvD, fun hvS => Finset.disjoint_left.mp hST hvS (hAT hvA)⟩)

private theorem bipartiteDistance_choices_nonempty {V : Type*} (G : SimpleGraph V) :
    {k : ℕ | ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (G.edgeSet \ H.edgeSet).ncard = k}.Nonempty := by
  refine ⟨G.edgeSet.ncard, ⊥, bot_le, ?_, by simp⟩
  exact ⟨Coloring.mk (fun _ => 0) (fun adjacency => False.elim (bot_adj _ _ |>.mp adjacency))⟩

-- The endpoints of the deleted edges must meet every obstruction in the chosen vertex set.
private theorem obstruction_bound {V : Type} (G : SimpleGraph V)
    {T : Finset V} {W : Set V} (finiteW : W.Finite) (hTW : (T : Set V) ⊆ W) (k : ℕ)
    (pack : ∀ D : Finset V, D.card < k →
      ∃ S : Finset V, S ⊆ T ∧ Disjoint S D ∧ ¬ (G.induce (S : Set V)).IsBipartite) :
    k ≤ 2 * bipartiteDistance (G.induce W) := by
  classical
  have finiteVertices : Finite W := finiteW.to_subtype
  let K := G.induce W
  obtain ⟨H, _, hBip, hDist⟩ := csInf_mem (bipartiteDistance_choices_nonempty K)
  let missing : Set (Sym2 W) := K.edgeSet \ H.edgeSet
  let finiteMissing := missing.toFinite
  let edges : Finset (Sym2 W) := finiteMissing.toFinset
  let ends (e : Sym2 W) : Finset V := e.toFinset.image Subtype.val
  let D := edges.biUnion ends
  have boundD : D.card ≤ 2 * bipartiteDistance K := by
    have boundEnds (e : Sym2 W) : (ends e).card ≤ 2 := by
      exact Finset.card_image_le.trans (by rw [Sym2.card_toFinset]; split <;> omega)
    have count : edges.card = bipartiteDistance K :=
      (Set.ncard_eq_toFinset_card missing finiteMissing).symm.trans hDist
    simpa [D, count, Nat.mul_comm] using
      (Finset.card_biUnion_le_card_mul edges ends 2 (fun e _ => boundEnds e))
  by_contra! big
  obtain ⟨S, hST, hSD, hBad⟩ := pack D (lt_of_le_of_lt boundD big)
  apply hBad
  refine Colorable.of_hom ?_ hBip
  let embed (v : (S : Set V)) : W := ⟨v.val, hTW (hST v.property)⟩
  refine ⟨embed, ?_⟩
  intro v w adjacency
  by_contra absent
  have hm : s(embed v, embed w) ∈ missing := ⟨adjacency, absent⟩
  have he : s(embed v, embed w) ∈ edges := finiteMissing.mem_toFinset.mpr hm
  have hvEnds : v.val ∈ ends (s(embed v, embed w)) := Finset.mem_image.mpr
    ⟨embed v, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _), rfl⟩
  exact Finset.disjoint_left.mp hSD v.property (Finset.mem_biUnion.mpr ⟨_, he, hvEnds⟩)

private theorem bipartiteDistance_le_choose {V : Type*} (G : SimpleGraph V)
    {W : Set V} (finiteW : W.Finite) :
    bipartiteDistance (G.induce W) ≤ W.ncard.choose 2 := by
  classical
  let vertexFintype := finiteW.fintype
  let K := G.induce W
  have candidate :
      K.edgeSet.ncard ∈ {k : ℕ | ∃ H : SimpleGraph W, H ≤ K ∧ H.IsBipartite ∧
        (K.edgeSet \ H.edgeSet).ncard = k} := by
    refine ⟨⊥, bot_le, ?_, by simp⟩
    exact ⟨Coloring.mk (fun _ => 0) (fun adjacency => False.elim (bot_adj _ _ |>.mp adjacency))⟩
  refine (csInf_le (OrderBot.bddBelow _) candidate).trans ?_
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    (SimpleGraph.card_edgeFinset_le_card_choose_two (G := K))

end OMA

theorem OMA.solution : type_of% @Erdos111.erdos_111.variants.lower_bound := by
  classical
  intro V G chromatic
  have uncountableChromatic : ℵ₀ < G.chromaticCardinal := by
    rw [chromatic]
    exact Cardinal.aleph0_lt_aleph_one
  have infiniteV : Infinite V := by
    apply not_finite_iff_infinite.mp
    intro finiteV
    exact (not_le_of_gt uncountableChromatic)
      ((OMA.chromatic_le_mk G.selfColoring).trans Cardinal.mk_le_aleph0)
  obtain ⟨m, small⟩ := OMA.bounded_obstructions G uncountableChromatic
  let M := m + 1
  have positiveM : 0 < M := by dsimp [M]; omega
  refine ⟨1 / (4 * (M : ℝ)), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * M)] with n hn
  have positiveN : 0 < n := by omega
  let k := n / M
  have kpos : 0 < k := Nat.div_pos (by omega) positiveM
  have width : M * k ≤ n := by simpa [k, Nat.mul_comm] using (Nat.div_mul_le_self n M)
  obtain ⟨T, sizeT, pack⟩ := OMA.pack_obstructions G small k
  have sizeT' : (T : Set V).ncard ≤ n := by
    rw [Set.ncard_coe_finset]
    exact sizeT.trans ((Nat.mul_le_mul_left k (Nat.le_succ m)).trans (by
      simpa [Nat.mul_comm] using width))
  obtain ⟨W, hTW, _, nW⟩ :=
    (Set.infinite_univ : (Set.univ : Set V).Infinite).exists_superset_ncard_eq
      (Set.subset_univ _) T.finite_toSet sizeT'
  have finiteW : W.Finite := Set.finite_of_ncard_pos (by rw [nW]; exact positiveN)
  have lower : k ≤ 2 * bipartiteDistance (G.induce W) :=
    OMA.obstruction_bound G finiteW hTW k pack
  have upper : bipartiteDistance (G.induce W) ≤ hG G n := by
    unfold hG
    refine le_csSup ?_ ?_
    · refine ⟨n.choose 2, ?_⟩
      rintro d ⟨S, hS, rfl⟩
      have finiteS : S.Finite := Set.finite_of_ncard_pos (by rw [hS]; exact positiveN)
      simpa [hS] using OMA.bipartiteDistance_le_choose G finiteS
    · exact ⟨W, nW, rfl⟩
  have cover : n ≤ 2 * (M * k) := by
    have remainder := Nat.mod_lt n positiveM
    have split := Nat.mod_add_div n M
    have first : M ≤ M * k := Nat.le_mul_of_pos_right _ kpos
    dsimp [k] at first ⊢
    omega
  have estimate : n ≤ (4 * M) * hG G n := calc
    n ≤ 2 * (M * k) := cover
    _ = (2 * M) * k := by ring
    _ ≤ (2 * M) * (2 * hG G n) :=
      Nat.mul_le_mul_left _ (lower.trans (Nat.mul_le_mul_left _ upper))
    _ = (4 * M) * hG G n := by ring
  calc
    _ = (n : ℝ) / (4 * (M : ℝ)) := by ring
    _ ≤ (hG G n : ℝ) := (div_le_iff₀ (by positivity)).mpr (by
      have : (n : ℝ) ≤ (4 * (M : ℝ)) * (hG G n : ℝ) := by exact_mod_cast estimate
      simpa [mul_comm] using this)
