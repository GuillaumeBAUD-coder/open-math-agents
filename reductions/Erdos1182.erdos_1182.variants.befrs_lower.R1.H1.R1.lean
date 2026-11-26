import OMAReductions.R_Erdos1182_erdos_1182_variants_befrs_lower_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

-- Reduction Erdos1182.erdos_1182.variants.befrs_lower.R1.H1.R1 of step Erdos1182.erdos_1182.variants.befrs_lower.R1.H1
-- Credit: @dk8827

/-! Separate the two local graph operations used to find a small Ramsey
obstruction. The counting step uses the degree sum and disjoint incidence sets. -/

namespace OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1_H1_R1

open SimpleGraph
open scoped BigOperators

/-- Deleting a leaf from a connected graph preserves the obstruction if
the host is large enough for the leaf extension argument. -/
def H1 : Prop :=
  ∀ {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),
    4 ≤ l → 2 * l - 1 ≤ m → G.Connected → C.CliqueFree 3 →
    (∃ x, (G.neighborSet x).ncard = 1) →
    ∃ H : SimpleGraph (Fin (l - 1)), H.Connected ∧
      H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard ∧ (H.IsContained Cᶜ → G.IsContained Cᶜ)

/-- Shortening a suspended path with adjacent degree-two vertices preserves the
obstruction. If the two other endpoints coincide, replace the triangle by a leaf. -/
def H2 : Prop :=
  ∀ {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),
    4 ≤ l → 2 * l - 1 ≤ m → G.Connected → C.CliqueFree 3 →
    (∃ x y, G.Adj x y ∧ (G.neighborSet x).ncard = 2 ∧ (G.neighborSet y).ncard = 2) →
    ∃ H : SimpleGraph (Fin (l - 1)), H.Connected ∧
      H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard ∧ (H.IsContained Cᶜ → G.IsContained Cᶜ)

theorem blueTriangle {m : ℕ} (C : SimpleGraph (Fin m)) (hm : 6 ≤ m)
    (hC : C.CliqueFree 3) : (⊤ : SimpleGraph (Fin 3)).IsContained Cᶜ := by
  classical
  apply (not_cliqueFree_iff_top_isContained 3).mp
  intro hblue
  let v : Fin m := ⟨0, by omega⟩
  by_cases hred : 3 ≤ (C.neighborFinset v).card
  · obtain ⟨S, hS, hscard⟩ := Finset.exists_subset_card_eq hred
    let p := S.orderEmbOfFin hscard
    have hadj (i : Fin 3) : C.Adj v (p i) :=
      (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hscard i))
    have hpair (i j : Fin 3) (hij : i ≠ j) : Cᶜ.Adj (p i) (p j) := by
      rw [compl_adj]
      exact ⟨p.injective.ne hij, fun h => hC _ (is3Clique_triple_iff.mpr ⟨hadj i, hadj j, h⟩)⟩
    exact hblue _ (is3Clique_triple_iff.mpr
      ⟨hpair 0 1 (by decide), hpair 0 2 (by decide), hpair 1 2 (by decide)⟩)
  · have hdeg := C.degree_compl (v := v)
    have hdeg' : (Cᶜ.neighborFinset v).card = m - 1 - (C.neighborFinset v).card := by
      simpa only [Fintype.card_fin, card_neighborFinset_eq_degree] using hdeg
    have hlarge : 3 ≤ (Cᶜ.neighborFinset v).card := by omega
    obtain ⟨S, hS, hscard⟩ := Finset.exists_subset_card_eq hlarge
    let p := S.orderEmbOfFin hscard
    have hadj (i : Fin 3) : Cᶜ.Adj v (p i) :=
      (mem_neighborFinset Cᶜ v _).mp (hS (S.orderEmbOfFin_mem hscard i))
    have hpair (i j : Fin 3) (hij : i ≠ j) : C.Adj (p i) (p j) := by
      by_contra h
      have hh := (compl_adj C _ _).mpr ⟨p.injective.ne hij, h⟩
      exact hblue _ (is3Clique_triple_iff.mpr ⟨hadj i, hadj j, hh⟩)
    exact hC _ (is3Clique_triple_iff.mpr
      ⟨hpair 0 1 (by decide), hpair 0 2 (by decide), hpair 1 2 (by decide)⟩)

theorem smallGraphsEmbed {l m : ℕ} (H : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (hl : l ≤ 3) (hm : 6 ≤ m) (hC : C.CliqueFree 3) : H.IsContained Cᶜ := by
  apply IsContained.trans ?_ (blueTriangle C hm hC)
  refine isContained_iff_exists_le_comap.mpr ⟨Fin.castLEEmb hl, ?_⟩
  intro x y hxy
  simpa only [comap_adj, top_adj] using (Fin.castLEEmb hl).injective.ne (H.ne_of_adj hxy)

theorem positiveDegree {l : ℕ} (H : SimpleGraph (Fin l)) (hl : 1 < l) (hH : H.Connected)
    (v : Fin l) : 0 < (H.neighborSet v).ncard := by
  classical
  have : Nontrivial (Fin l) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using hl)
  obtain ⟨w, hw⟩ := exists_ne v
  have hp := (hH.preconnected v w).degree_pos_left hw.symm
  rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset] at hp
  exact hp

theorem coreCounts {l k : ℕ} (H : SimpleGraph (Fin l))
    (hl : 0 < l) (hedge : H.edgeSet.ncard ≤ l + k)
    (hdeg : ∀ v, 2 ≤ (H.neighborSet v).ncard)
    (hind : ∀ x y, (H.neighborSet x).ncard = 2 → (H.neighborSet y).ncard = 2 → ¬ H.Adj x y) :
    ∃ D : Finset (Fin l), l ≤ 5 * k ∧ l - D.card < 4 * k ∧
      (H.induce (↑Dᶜ : Set (Fin l))).edgeSet.ncard ≤ l - D.card + k ∧
      ∀ x ∈ D, (H.neighborSet x).ncard ≤ 2 := by
  classical
  let D := Finset.univ.filter (fun v => (H.neighborSet v).ncard = 2)
  let U := Dᶜ
  have hD (x : Fin l) : x ∈ D ↔ (H.neighborSet x).ncard = 2 := by simp [D]
  have degree_ncard (x : Fin l) : H.degree x = (H.neighborSet x).ncard := by
    rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset]
  have hDsum : ∑ x ∈ D, H.degree x = 2 * D.card := by
    calc
      _ = ∑ _ ∈ D, 2 := Finset.sum_congr rfl (fun x hx => (degree_ncard x).trans ((hD x).mp hx))
      _ = _ := by simp [Nat.mul_comm]
  have hUsum : 3 * U.card ≤ ∑ x ∈ U, H.degree x := by
    calc
      _ = ∑ _ ∈ U, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        have hne : (H.neighborSet x).ncard ≠ 2 :=
          fun hh => Finset.mem_compl.mp hx ((hD x).mpr hh)
        rw [degree_ncard]
        exact lt_of_le_of_ne (hdeg x) hne.symm
  have hUV : U.card = l - D.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hDU : D.card + U.card = l := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  have hcount : H.edgeFinset.card = H.edgeSet.ncard := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have hSum : 2 * D.card + 3 * U.card ≤ 2 * H.edgeFinset.card := by
    calc
      _ ≤ (∑ x ∈ D, H.degree x) + ∑ x ∈ U, H.degree x := by omega
      _ = _ := by rw [Finset.sum_add_sum_compl, H.sum_degrees_eq_twice_card_edges]
  let removed := D.biUnion (fun x => H.incidenceFinset x)
  have hremoved : removed.card = 2 * D.card := by
    calc
      _ = ∑ x ∈ D, (H.incidenceFinset x).card := by
        apply Finset.card_biUnion
        intro x hx y hy hxy
        apply Finset.disjoint_left.mpr
        intro e he hf
        change e ∈ H.incidenceFinset x at he
        change e ∈ H.incidenceFinset y at hf
        rw [incidenceFinset_eq_filter, Finset.mem_filter] at he hf
        exact hind x y ((hD x).mp hx) ((hD y).mp hy)
          ((H.adj_iff_exists_edge).mpr ⟨hxy, e, mem_edgeFinset.mp he.1, he.2, hf.2⟩)
      _ = _ := by simpa only [card_incidenceFinset_eq_degree] using hDsum
  let kept := H.edgeFinset.filter (fun e => e.toFinset ⊆ U)
  have hkept : kept.card = (H.induce (↑U : Set (Fin l))).edgeSet.ncard := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    exact card_filter_edgeFinset_toFinset_subset U
  have hsplit : removed.card + kept.card ≤ H.edgeFinset.card := by
    have hdis : Disjoint removed kept := by
      apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨x, hx, hxe⟩ := Finset.mem_biUnion.mp he
      rw [incidenceFinset_eq_filter, Finset.mem_filter] at hxe
      have hxu : x ∈ U := (Finset.mem_filter.mp hf).2 (Sym2.mem_toFinset.mpr hxe.2)
      exact Finset.mem_compl.mp hxu hx
    rw [← Finset.card_union_of_disjoint hdis]
    apply Finset.card_le_card
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_biUnion.mp he
      exact H.incidenceFinset_subset x hxe
    · exact (Finset.mem_filter.mp he).1
  have hV : 2 * U.card ≤ 4 * k := by omega
  have hDt : D.card ≤ U.card + k := by omega
  have hk : 0 < k := by omega
  refine ⟨D, ?_, ?_, ?_, fun x hx => ((hD x).mp hx).le⟩
  · omega
  · omega
  · change (H.induce (↑U : Set (Fin l))).edgeSet.ncard ≤ l - D.card + k
    omega

theorem main : H1 → H2 → OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1.H1 := by
  intro hleaf hpath n hn G hG hsize C hC havoid
  let k := (2 * n + 1) / 15
  have compress : ∀ l ≤ n, ∀ (H : SimpleGraph (Fin l)), H.Connected →
      H.edgeSet.ncard ≤ l + k → ¬ H.IsContained Cᶜ →
      ∃ (r : ℕ) (J : SimpleGraph (Fin r)) (D : Finset (Fin r)),
        r ≤ 5 * k ∧ r - D.card < 4 * k ∧
        (J.induce (↑Dᶜ : Set (Fin r))).edgeSet.ncard ≤ r - D.card + k ∧
        (∀ x ∈ D, (J.neighborSet x).ncard ≤ 2) ∧ ¬ J.IsContained Cᶜ := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro hln H hconn he hbad
      have hl : 4 ≤ l := by
        by_contra! h
        exact hbad (smallGraphsEmbed H C (by omega) (by omega) hC)
      by_cases hasLeaf : ∃ x, (H.neighborSet x).ncard = 1
      · obtain ⟨J, hJ, hJedge, htransfer⟩ := hleaf H C hl (by omega) hconn hC hasLeaf
        exact ih (l - 1) (by omega) (by omega) J hJ (by omega) (fun h => hbad (htransfer h))
      by_cases hasPath : ∃ x y, H.Adj x y ∧
          (H.neighborSet x).ncard = 2 ∧ (H.neighborSet y).ncard = 2
      · obtain ⟨J, hJ, hJedge, htransfer⟩ := hpath H C hl (by omega) hconn hC hasPath
        exact ih (l - 1) (by omega) (by omega) J hJ (by omega) (fun h => hbad (htransfer h))
      have hdeg (v : Fin l) : 2 ≤ (H.neighborSet v).ncard := by
        have hp := positiveDegree H (by omega) hconn v
        have hne : (H.neighborSet v).ncard ≠ 1 := fun h => hasLeaf ⟨v, h⟩
        omega
      have hind x y (hx : (H.neighborSet x).ncard = 2) (hy : (H.neighborSet y).ncard = 2)
          (hxy : H.Adj x y) : False := hasPath ⟨x, y, hxy, hx, hy⟩
      obtain ⟨D, hlk, hdc, hde, hdd⟩ := coreCounts H (by omega) he hdeg hind
      exact ⟨l, H, D, hlk, hdc, hde, hdd, hbad⟩
  obtain ⟨l, H, D, hl, hD, hE, hdeg, hbad⟩ := compress n le_rfl G hG hsize havoid
  refine ⟨l, k, H, D, ?_, hl, hD, hE, hdeg, hbad⟩
  dsimp [k]
  omega

end OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1_H1_R1
