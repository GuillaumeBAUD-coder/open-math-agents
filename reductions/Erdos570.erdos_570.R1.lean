import FormalConjectures.ErdosProblems.«570»
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Reducing the cycle Ramsey bound to connected graphs and matchings

Fix the cycle length k. The connected case allows a fixed minimum host order to cover
small targets. The matching step asks only for a matching of k edges. Host edges are blue.

The component argument is related to Claim 11 of Cambie, Freschi, Morawski, Petrova
and Pokrovskiy (arXiv:2601.10238). Here the auxiliary bound is the maximum of the
desired bound and a function of slope three halves. Removing a connected component
with at least two edges frees enough vertices for induction on either branch.
-/

open SimpleGraph Filter
open scoped Classical

namespace OMA.R_Erdos570_erdos_570_R1

/-- The sharp host size, above a constant depending on the cycle length, for connected targets. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ B : ℕ, ∀ (W V : Type) [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V),
    H.Connected →
    B ≤ Fintype.card V → 2 * H.edgeSet.ncard + (k - 1) / 2 ≤ Fintype.card V →
    ¬ (cycleGraph k ⊑ Gᶜ) → H ⊑ G

/-- Only the diagonal matching case of Proposition 9: the matching has exactly k edges. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ (W V : Type) [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V),
    (∀ v, (H.neighborSet v).ncard = 1) → H.edgeSet.ncard = k →
    2 * k + (k - 1) / 2 ≤ Fintype.card V → ¬ (cycleGraph k ⊑ Gᶜ) → H ⊑ G

/-- Restricting to a union of components preserves every degree there. -/
lemma degree_on_part {W : Type} [Fintype W] (H : SimpleGraph W)
    (s : Set W) (closed : ∀ {v w}, H.Adj v w → v ∈ s → w ∈ s) (v : s) :
    ((H.induce s).neighborSet v).ncard = (H.neighborSet v.val).ncard := by
  let e : (H.induce s).neighborSet v ≃ H.neighborSet v.val :=
    { toFun := fun w => ⟨w.val.val, w.property⟩
      invFun := fun w => ⟨⟨w.val, closed w.property v.property⟩, w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [← Nat.card_coe_set_eq] using Nat.card_congr e

lemma edge_count_from_degrees {W : Type} [Fintype W] (H : SimpleGraph W) :
    ∑ v, (H.neighborSet v).ncard = 2 * H.edgeSet.ncard := by
  simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree,
    edgeFinset_card] using H.sum_degrees_eq_twice_card_edges

/-- A cut with no crossing edges partitions the total edge count. -/
lemma edge_count_on_parts {W : Type} [Fintype W] (H : SimpleGraph W) (s : Set W)
    (closed : ∀ {v w}, H.Adj v w → (v ∈ s ↔ w ∈ s)) :
    (H.induce s).edgeSet.ncard + (H.induce sᶜ).edgeSet.ncard = H.edgeSet.ncard := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ s) (fun v => (H.neighborSet v).ncard)
  have left := edge_count_from_degrees (H.induce s)
  have right := edge_count_from_degrees (H.induce sᶜ)
  simp_rw [degree_on_part H s (fun h => (closed h).mp)] at left
  simp_rw [degree_on_part H sᶜ (fun h => mt (closed h).mpr)] at right
  have sum_eq : 2 * (H.induce s).edgeSet.ncard + 2 * (H.induce sᶜ).edgeSet.ncard =
      2 * H.edgeSet.ncard := by
    rw [← left, ← right, ← edge_count_from_degrees]
    exact h
  omega

/-- Combine two blue copies on opposite sides of an edgeless cut in the target. -/
lemma combine_copies {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) (s : Set W)
    (closed : ∀ {v w}, H.Adj v w → (v ∈ s ↔ w ∈ s))
    (f : (H.induce s).Copy G)
    (g : (H.induce sᶜ).Copy (G.induce (Set.range f)ᶜ)) : H ⊑ G := by
  let embed (w : W) : V := if hw : w ∈ s then f ⟨w, hw⟩ else (g ⟨w, hw⟩).val
  refine ⟨⟨⟨embed, ?_⟩, ?_⟩⟩
  · intro u v huv
    by_cases hu : u ∈ s
    · have hv := (closed huv).mp hu
      simpa only [embed, dif_pos hu, dif_pos hv, Copy.toHom_apply] using
        (f.toHom.map_adj (show (H.induce s).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv))
    · have hv := mt (closed huv).mpr hu
      simpa only [embed, dif_neg hu, dif_neg hv, Copy.toHom_apply, induce_adj] using
        (g.toHom.map_adj (show (H.induce sᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv))
  · intro u v he
    change embed u = embed v at he
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
    · simp only [embed, dif_pos hu, dif_pos hv] at he
      exact congrArg Subtype.val (f.injective he)
    · simp only [embed, dif_pos hu, dif_neg hv] at he
      exact False.elim ((g ⟨v, hv⟩).property ⟨⟨u, hu⟩, he⟩)
    · simp only [embed, dif_neg hu, dif_pos hv] at he
      exact False.elim ((g ⟨u, hu⟩).property ⟨⟨v, hv⟩, he.symm⟩)
    · simp only [embed, dif_neg hu, dif_neg hv] at he
      exact congrArg Subtype.val (g.injective (Subtype.ext he))

/-- Matchings of all orders follow by peeling an edge from both target and host.
Below k edges we reserve k extra vertices so that the host always has a blue edge. -/
lemma pack_matching (base : H2) (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (W V : Type) [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (regular : ∀ v, (H.neighborSet v).ncard = 1) (edges : H.edgeSet.ncard = m)
    (size : 2 * m + (if m < k then k else (k - 1) / 2) ≤ Fintype.card V)
    (free : ¬ (cycleGraph k ⊑ Gᶜ)) : H ⊑ G := by
  induction m generalizing W V with
  | zero =>
    have card := edge_count_from_degrees H
    simp [regular, edges] at card
    let := Fintype.card_eq_zero_iff.mp card
    exact IsContained.of_isEmpty
  | succ m ih =>
    by_cases diag : m + 1 = k
    · exact base k hk W V H G regular (edges.trans diag) (by simpa [diag] using size) free
    obtain ⟨x, y, xy⟩ : ∃ x y, H.Adj x y := ne_bot_iff_exists_adj.mp (by
      rintro rfl
      simp at edges)
    let s : Set W := {x, y}
    have cardS : Fintype.card s = 2 := by
      simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using Set.ncard_pair xy.ne
    have neighbors (z : W) : (H.neighborSet z).Subsingleton :=
      Set.ncard_le_one_iff_subsingleton.mp (regular z).le
    have stays {i j : W} (hij : H.Adj i j) (hi : i ∈ s) : j ∈ s := by
      rcases (show i = x ∨ i = y from hi) with rfl | rfl
      · exact Or.inr (neighbors _ hij xy)
      · exact Or.inl (neighbors _ hij xy.symm)
    have closed : ∀ {i j}, H.Adj i j → (i ∈ s ↔ j ∈ s) :=
      fun h => ⟨stays h, stays h.symm⟩
    have regOn (w : s) : ((H.induce s).neighborSet w).ncard = 1 :=
      (degree_on_part H s (fun h => (closed h).mp) w).trans (regular w.val)
    have one := edge_count_from_degrees (H.induce s)
    simp only [regOn, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, cardS] at one
    have split := (edge_count_on_parts H s closed).trans edges
    have remEdges : (H.induce sᶜ).edgeSet.ncard = m := by omega
    have room : k ≤ Fintype.card V := by split at size <;> omega
    obtain ⟨u, v, uv⟩ : ∃ u v, G.Adj u v := ne_bot_iff_exists_adj.mp (by
      rintro rfl
      apply free
      rw [compl_bot]
      exact isContained_top_iff.mpr (Function.Embedding.nonempty_of_card_le (by simpa using room)))
    let pair : Set V := {u, v}
    have clique : G.IsClique pair := isClique_pair.mpr (fun _ => uv)
    have cardPair : Fintype.card pair = 2 := by
      simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using Set.ncard_pair uv.ne
    have small : H.induce s ⊑ G.induce pair := by
      rw [induce_eq_top.mpr clique]
      apply isContained_top_iff.mpr
      exact Function.Embedding.nonempty_of_card_le (cardS.trans cardPair.symm).le
    obtain ⟨f⟩ := small.trans (Embedding.induce pair).isContained
    let rest := (Set.range f)ᶜ
    have cardRest : Fintype.card rest = Fintype.card V - 2 := by
      rw [Fintype.card_compl_set (Set.range f),
        Fintype.card_congr (Equiv.ofInjective f f.injective).symm, cardS]
    have roomRest : 2 * m + (if m < k then k else (k - 1) / 2) ≤ Fintype.card rest := by
      rw [cardRest]
      split at size <;> split <;> omega
    have remFree : ¬ (cycleGraph k ⊑ (G.induce rest)ᶜ) :=
      fun hc => free (hc.trans (Embedding.complEquiv (Embedding.induce rest)).isContained)
    obtain ⟨g⟩ := ih ↥(sᶜ) rest (H.induce sᶜ) (G.induce rest)
      (fun w => (degree_on_part H sᶜ (fun h => mt (closed h).mpr) w).trans (regular w.val))
      remEdges roomRest remFree
    exact combine_copies H G s closed f g

theorem main : H1 → H2 → type_of% @Erdos570.erdos_570 := by
  intro hConn hMatch k hk
  obtain ⟨a, conn⟩ := hConn k hk
  let B := max a (3 * k)
  let t := (k - 1) / 2
  let bound (m : ℕ) := max (2 * m + t) (m + m / 2 + B)
  have pack (m : ℕ) (W V : Type) [Fintype W] [Fintype V]
      (H : SimpleGraph W) (G : SimpleGraph V) (pos : ∀ v, 0 < (H.neighborSet v).ncard)
      (edges : H.edgeSet.ncard = m) (size : bound m ≤ Fintype.card V)
      (free : ¬ (cycleGraph k ⊑ Gᶜ)) : H ⊑ G := by
    induction m using Nat.strong_induction_on generalizing W V with
    | h m ih =>
      have sharp := (le_max_left _ _).trans size
      have extra := (le_max_right _ _).trans size
      by_cases regular : ∀ v, (H.neighborSet v).ncard = 1
      · apply pack_matching hMatch k hk m W V H G regular edges _ free
        dsimp [B] at extra
        split <;> omega
      push Not at regular
      obtain ⟨v, hv⟩ := regular
      let c := H.connectedComponentMk v
      let s := c.supp
      have closed : ∀ {u w}, H.Adj u w → (u ∈ s ↔ w ∈ s) := fun h => c.mem_supp_congr_adj h
      let e := (H.induce s).edgeSet.ncard
      let r := (H.induce sᶜ).edgeSet.ncard
      have split : e + r = m := (edge_count_on_parts H s closed).trans edges
      have vmem : v ∈ s := rfl
      have e2 : 2 ≤ e := by
        have h : ((H.induce s).neighborSet ⟨v, vmem⟩).ncard ≤ e := by
          simpa only [e, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
            card_neighborSet_eq_degree, edgeFinset_card] using
            (H.induce s).degree_le_card_edgeFinset ⟨v, vmem⟩
        rw [degree_on_part H s (fun h => (closed h).mp)] at h
        change (H.neighborSet v).ncard ≤ e at h
        have := pos v
        omega
      have hconnected : (H.induce s).Connected := c.connected_toSimpleGraph
      have order : Fintype.card s ≤ e + 1 := by
        simpa only [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card', Set.toFinset_card, e]
          using hconnected.card_vert_le_card_edgeSet_add_one
      obtain ⟨f⟩ := conn s V (H.induce s) G hconnected
        (by dsimp [B] at extra; omega)
        (show 2 * e + t ≤ Fintype.card V by omega) free
      let rest := (Set.range f)ᶜ
      have restSize : bound r ≤ Fintype.card rest := by
        have hrange : Fintype.card (Set.range f) = Fintype.card s :=
          Fintype.card_congr (Equiv.ofInjective f f.injective).symm
        rw [show Fintype.card rest = Fintype.card V - Fintype.card s by
          rw [Fintype.card_compl_set (Set.range f), hrange]]
        dsimp only [bound]
        omega
      have restFree : ¬ (cycleGraph k ⊑ (G.induce rest)ᶜ) :=
        fun hc => free (hc.trans (Embedding.complEquiv (Embedding.induce rest)).isContained)
      obtain ⟨g⟩ := ih r (by omega) ↥(sᶜ) rest (H.induce sᶜ) (G.induce rest)
        (fun w => lt_of_lt_of_eq (pos w.val) (degree_on_part H sᶜ (fun h => mt (closed h).mpr) w).symm)
        rfl restSize restFree
      exact combine_copies H G s closed f g
  filter_upwards [eventually_ge_atTop (2 * B)] with m hm
  intro W _ H _ pos edges
  have npos (v : W) : 0 < (H.neighborSet v).ncard := by
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using pos v
  apply Nat.sInf_le
  intro C
  by_cases hc : cycleGraph k ⊑ C
  · exact Or.inl hc
  · exact Or.inr (pack m W _ H Cᶜ npos edges
      (by simp only [Fintype.card_fin, bound]; omega) (by simpa using hc))

end OMA.R_Erdos570_erdos_570_R1
