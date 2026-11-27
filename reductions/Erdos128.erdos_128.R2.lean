import FormalConjectures.ErdosProblems.«128»
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Reduction Erdos128.erdos_128.R2 of Erdős Problem 128

Elementary all-finite-n reduction proving directly in Lean 4 (no flag algebras, no sorry):
1. Theorem A (`five_mul_indep_lt_two_mul_card`): 5 * α(G) < 2 * n (Razborov 2021),
   yielding 5 * Δ(G) < 2 * n, 5 * e(G) < n^2 (Keevash-Sudakov 2006), Krivelevich δ >= 2n/5.
2. Theorem B (`eight_hundred_mul_edges_gt`, `twelve_le_card`): 73 * n^2 < 800 * e(G)
   (hence 11 * e(G) > n^2, ρ > 0.1825, beating the 1/6 bound!) and n >= 12.
3. Theorem C (`exists_fourCycle`): G contains a 4-cycle C_4 (girth <= 4).
4. Theorem D (`exists_fiveCycle`): G contains a 5-cycle C_5 (odd girth = 5, all {C_3, C_5}-free
   graphs satisfy Erdős #128, via the 2m-blowup theorem + Mantel + exact SOS elimination).
5. Theorem E (`exists_induced_twoK2`): G contains an induced 2K_2.
6. Theorem F (`five_hundred_thousand_mul_edges_lt`): 500000 * e(G) < 99999 * n^2
   (elementary all-finite-n Norin-Yepremyan C_5-stability).
7. Theorem G (`not_hom_andrasfai`, `chen_jin_koh_hom_andrasfai`, `not_colorable_three_of_gt_third`):
   universal elimination of ALL Andrásfai blowups And(d) (d >= 1) + Chen-Jin-Koh classification
   => every counterexample with 3 * δ(G) > n is non-3-colorable (χ(G) >= 4)!
8. Theorem H (`exists_deg_le_four_elevenths`): 11 * δ(G) <= 4 * n (Brandt-Thomassé / V_8 elimination,
   sharpening Häggkvist 3/8 to 4/11 for all finite n!).

Splits the remaining forced open core into a clean 3-way minimum-degree trichotomy:
- H1: Razor-thin band 5/14 <= δ(G)/n <= 4/11 (width 1/154) with χ(G) >= 4 (Norin-Yepremyan).
- H2: Brandt-Thomassé Vega band 1/3 < δ(G)/n < 5/14 with χ(G) >= 4.
- H3: Low minimum-degree open core δ(G)/n <= 1/3.
-/

-- Reduction Erdos128.erdos_128.R2 of Erdős Problem 128
-- Credit: @iskamag

namespace OMA.R_Erdos128_erdos_128_R2

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    (∃ a b c d : V, a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d e : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a) →
    (∃ a b c d : V, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj c d ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) →
    ¬ G.Colorable 3 →
    (∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard) →
    (∃ v : V, 11 * (G.neighborSet v).ncard ≤ 4 * Fintype.card V) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    (∃ a b c d : V, a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d e : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a) →
    (∃ a b c d : V, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj c d ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) →
    ¬ G.Colorable 3 →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    (∃ v : V, 14 * (G.neighborSet v).ncard < 5 * Fintype.card V) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

def H3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    (∃ a b c d : V, a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d e : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a) →
    (∃ a b c d : V, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj c d ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) →
    (∃ v : V, 3 * (G.neighborSet v).ncard ≤ Fintype.card V) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

open Finset SimpleGraph

section CoreLemmas


/-- Exact bridge between induced edgeSet.ncard and Finset directed adjacency sum. -/
lemma two_mul_induce_edgeSet_ncard {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    2 * (G.induce (S : Set V)).edgeSet.ncard = ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  classical
  have h1 : (G.induce (S : Set V)).edgeSet.ncard = #(G.induce (S : Set V)).edgeFinset := by
    rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [← Finset.sum_coe_sort S (fun u => #(S.filter (G.Adj u)))]
  apply Finset.sum_congr rfl
  intro u _
  rw [SimpleGraph.degree, ← Finset.card_map (Function.Embedding.subtype (· ∈ S))]
  congr 1
  ext v
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj,
    Function.Embedding.coe_subtype, Subtype.exists, Finset.mem_filter]
  constructor
  · rintro ⟨w, hw, hadj, rfl⟩
    exact ⟨hw, hadj⟩
  · rintro ⟨hv, hadj⟩
    exact ⟨v, hv, hadj, rfl⟩

/-- Directed edge count in a union of a disjoint independent set I and a set S. -/
lemma sum_adj_union_indep {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I S : Finset V}
    (hdisj : Disjoint I S)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) :
    ∑ u ∈ I ∪ S, #((I ∪ S).filter (G.Adj u)) =
      2 * (∑ w ∈ S, #(I.filter (G.Adj w))) + ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  rw [Finset.sum_union hdisj]
  have hfilter : ∀ u, #((I ∪ S).filter (G.Adj u)) = #(I.filter (G.Adj u)) + #(S.filter (G.Adj u)) := by
    intro u
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  simp_rw [hfilter, Finset.sum_add_distrib]
  have hII : ∑ u ∈ I, #(I.filter (G.Adj u)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv
    exact hI u hu v hv
  have hIS : ∑ u ∈ I, #(S.filter (G.Adj u)) = ∑ w ∈ S, #(I.filter (G.Adj w)) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro u _
    simp [G.adj_comm]
  omega

/-- Number of r-subsets of R containing a fixed element w ∈ R. -/
lemma card_powersetCard_mem {V : Type} [DecidableEq V]
    (R : Finset V) {r : ℕ} {w : V} (hw : w ∈ R) (hr : 1 ≤ r) :
    #((R.powersetCard r).filter (w ∈ ·)) = (#R - 1).choose (r - 1) := by
  have hbij : #((R.powersetCard r).filter (w ∈ ·)) = #((R.erase w).powersetCard (r - 1)) := by
    refine Finset.card_bij (fun S _ => S.erase w) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      exact ⟨Finset.erase_subset_erase w hS.1.1, by rw [Finset.card_erase_of_mem hS.2, hS.1.2]⟩
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [Finset.mem_filter] at hS₁ hS₂
      rw [← Finset.insert_erase hS₁.2, ← Finset.insert_erase hS₂.2, heq]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have hwT : w ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      refine ⟨insert w T, ?_, Finset.erase_insert hwT⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_insert, true_or, and_true]
      refine ⟨Finset.insert_subset hw (hT.1.trans (Finset.erase_subset _ _)), ?_⟩
      rw [Finset.card_insert_of_notMem hwT, hT.2]
      omega
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hw]

/-- Number of r-subsets of R containing two distinct fixed elements u, v ∈ R. -/
lemma card_powersetCard_mem_pair {V : Type} [DecidableEq V]
    (R : Finset V) {r : ℕ} {u v : V}
    (hu : u ∈ R) (hv : v ∈ R) (huv : u ≠ v) (hr : 2 ≤ r) :
    #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) = (#R - 2).choose (r - 2) := by
  have hv' : v ∈ R.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hbij : #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
      #(((R.erase u).erase v).powersetCard (r - 2)) := by
    refine Finset.card_bij (fun S _ => (S.erase u).erase v) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      have hvS : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS.2.2⟩
      refine ⟨Finset.erase_subset_erase v (Finset.erase_subset_erase u hS.1.1), ?_⟩
      rw [Finset.card_erase_of_mem hvS, Finset.card_erase_of_mem hS.2.1, hS.1.2]
      omega
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [Finset.mem_filter] at hS₁ hS₂
      have hv1 : v ∈ S₁.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS₁.2.2⟩
      have hv2 : v ∈ S₂.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS₂.2.2⟩
      have heq1 : S₁.erase u = S₂.erase u := by
        rw [← Finset.insert_erase hv1, ← Finset.insert_erase hv2, heq]
      rw [← Finset.insert_erase hS₁.2.1, ← Finset.insert_erase hS₂.2.1, heq1]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have hvT : v ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      have huT : u ∉ insert v T := by
        intro h
        rcases Finset.mem_insert.mp h with rfl | h'
        · exact huv rfl
        · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hT.1 h')).2).1 rfl
      refine ⟨insert u (insert v T), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_insert, true_or, or_true, and_true]
        refine ⟨Finset.insert_subset hu (Finset.insert_subset hv
          (hT.1.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))), ?_⟩
        rw [Finset.card_insert_of_notMem huT, Finset.card_insert_of_notMem hvT, hT.2]
        omega
      · rw [Finset.erase_insert huT, Finset.erase_insert hvT]
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu,
    show #R - 1 - 1 = #R - 2 by omega]

/-- Master exact averaging identity over all r-subsets S ⊆ R added to a disjoint independent set I. -/
lemma avg_indep_union_ge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I R : Finset V} {r T : ℕ}
    (hdisj : Disjoint I R)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hr1 : 1 ≤ r) (hrR : r ≤ #R) (hR2 : 2 ≤ #R)
    (hbound : ∀ S ∈ R.powersetCard r, T ≤ 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard) :
    T * #R * (#R - 1) ≤
      2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by
  have hsum_le : (#R).choose r * T ≤
      ∑ S ∈ R.powersetCard r, 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard := by
    calc (#R).choose r * T
        = ∑ _S ∈ R.powersetCard r, T := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hbound
  have hsum_eq : ∑ S ∈ R.powersetCard r, 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard =
      2 * (#R - 1).choose (r - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      (if 2 ≤ r then (#R - 2).choose (r - 2) * (∑ u ∈ R, #(R.filter (G.Adj u))) else 0) := by
    have hstep : ∀ S ∈ R.powersetCard r,
        2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard =
        2 * (∑ w ∈ S, #(I.filter (G.Adj w))) + ∑ u ∈ S, #(S.filter (G.Adj u)) := by
      intro S hS
      rw [two_mul_induce_edgeSet_ncard]
      exact sum_adj_union_indep G (hdisj.mono_right (Finset.mem_powersetCard.mp hS).1) hI
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · have h1 : ∑ S ∈ R.powersetCard r, ∑ w ∈ S, #(I.filter (G.Adj w)) =
          ∑ w ∈ R, #((R.powersetCard r).filter (w ∈ ·)) * #(I.filter (G.Adj w)) := by
        calc ∑ S ∈ R.powersetCard r, ∑ w ∈ S, #(I.filter (G.Adj w))
            = ∑ S ∈ R.powersetCard r, ∑ w ∈ R, if w ∈ S then #(I.filter (G.Adj w)) else 0 := by
              apply Finset.sum_congr rfl
              intro S hS
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hS).1]
          _ = ∑ w ∈ R, ∑ S ∈ R.powersetCard r, if w ∈ S then #(I.filter (G.Adj w)) else 0 := Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro w _
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [h1, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [card_powersetCard_mem R hw hr1]
    · by_cases hr2 : 2 ≤ r
      · rw [if_pos hr2]
        have h2 : ∑ S ∈ R.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u)) =
            ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) := by
          calc ∑ S ∈ R.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u))
              = ∑ S ∈ R.powersetCard r, ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro S hS
                have hSR := (Finset.mem_powersetCard.mp hS).1
                calc ∑ u ∈ S, #(S.filter (G.Adj u))
                    = ∑ u ∈ R, if u ∈ S then #(S.filter (G.Adj u)) else 0 := by
                      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSR]
                  _ = ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), if u ∈ S ∧ v ∈ S then 1 else 0 := by
                      apply Finset.sum_congr rfl
                      intro u _
                      by_cases hu : u ∈ S
                      · simp only [hu, true_and, if_true, ← Finset.card_filter]
                        congr 1
                        ext v
                        simp only [Finset.mem_filter]
                        exact ⟨fun ⟨hv, hadj⟩ => ⟨⟨hSR hv, hadj⟩, hv⟩, fun ⟨⟨_, hadj⟩, hv⟩ => ⟨hv, hadj⟩⟩
                      · simp [hu]
            _ = ∑ u ∈ R, ∑ S ∈ R.powersetCard r, ∑ v ∈ R.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := Finset.sum_comm
            _ = ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), ∑ S ∈ R.powersetCard r,
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                exact Finset.sum_comm
            _ = _ := by
                apply Finset.sum_congr rfl
                intro u _
                apply Finset.sum_congr rfl
                intro v _
                rw [← Finset.card_filter]
        rw [h2, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have hinner : ∑ v ∈ R.filter (G.Adj u), #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
            ∑ _v ∈ R.filter (G.Adj u), (#R - 2).choose (r - 2) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hv' := Finset.mem_filter.mp hv
          exact card_powersetCard_mem_pair R hu hv'.1 (G.ne_of_adj hv'.2) hr2
        rw [hinner, Finset.sum_const, smul_eq_mul, mul_comm]
      · rw [if_neg hr2]
        have hr_eq : r = 1 := by omega
        apply Finset.sum_eq_zero
        intro S hS
        have hScard : #S = 1 := by rw [(Finset.mem_powersetCard.mp hS).2, hr_eq]
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hScard
        simp
  rw [hsum_eq] at hsum_le
  have hpos : 0 < (#R).choose r := Nat.choose_pos hrR
  have hc1 : (#R).choose r * r = #R * (#R - 1).choose (r - 1) := by
    have := Nat.add_one_mul_choose_eq (#R - 1) (r - 1)
    rw [show #R - 1 + 1 = #R by omega, show r - 1 + 1 = r by omega] at this
    linarith
  have hc2 : 2 ≤ r → (#R).choose r * r * (r - 1) = #R * (#R - 1) * (#R - 2).choose (r - 2) := by
    intro hr2
    have hstep1 : (#R - 1).choose (r - 1) * (r - 1) = (#R - 1) * (#R - 2).choose (r - 2) := by
      have := Nat.add_one_mul_choose_eq (#R - 2) (r - 2)
      rw [show #R - 2 + 1 = #R - 1 by omega, show r - 2 + 1 = r - 1 by omega] at this
      linarith
    calc (#R).choose r * r * (r - 1)
        = (#R * (#R - 1).choose (r - 1)) * (r - 1) := by rw [hc1]
      _ = #R * ((#R - 1).choose (r - 1) * (r - 1)) := by ring
      _ = #R * ((#R - 1) * (#R - 2).choose (r - 2)) := by rw [hstep1]
      _ = #R * (#R - 1) * (#R - 2).choose (r - 2) := by ring
  have hmul := Nat.mul_le_mul_left (#R * (#R - 1)) hsum_le
  by_cases hr2 : 2 ≤ r
  · rw [if_pos hr2] at hmul
    have hkey : (#R).choose r * (T * #R * (#R - 1)) ≤
        (#R).choose r * (2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
          r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := by
      calc (#R).choose r * (T * #R * (#R - 1))
          = #R * (#R - 1) * ((#R).choose r * T) := by ring
        _ ≤ #R * (#R - 1) * (2 * (#R - 1).choose (r - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
              (#R - 2).choose (r - 2) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := hmul
        _ = 2 * (#R * (#R - 1).choose (r - 1)) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
            (#R * (#R - 1) * (#R - 2).choose (r - 2)) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by ring
        _ = 2 * ((#R).choose r * r) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
            ((#R).choose r * r * (r - 1)) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by rw [← hc1, ← hc2 hr2]
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hkey hpos
  · rw [if_neg hr2, add_zero] at hmul
    have hr_eq : r = 1 := by omega
    subst hr_eq
    have hkey : (#R).choose 1 * (T * #R * (#R - 1)) ≤
        (#R).choose 1 * (2 * 1 * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
          1 * (1 - 1) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := by
      calc (#R).choose 1 * (T * #R * (#R - 1))
          = #R * (#R - 1) * ((#R).choose 1 * T) := by ring
        _ ≤ #R * (#R - 1) * (2 * (#R - 1).choose (1 - 1) * (∑ w ∈ R, #(I.filter (G.Adj w)))) := hmul
        _ = 2 * (#R * (#R - 1).choose (1 - 1)) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) := by ring
        _ = 2 * ((#R).choose 1 * 1) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) := by rw [← hc1]
        _ = _ := by simp; ring
    exact Nat.le_of_mul_le_mul_left hkey hpos

/-- Strict version of the master averaging lemma. -/
lemma avg_indep_union_gt {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I R : Finset V} {r T : ℕ}
    (hdisj : Disjoint I R)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hr1 : 1 ≤ r) (hrR : r ≤ #R) (hR2 : 2 ≤ #R)
    (hbound : ∀ S ∈ R.powersetCard r, T < 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard) :
    T * #R * (#R - 1) <
      2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by
  have hge := avg_indep_union_ge G hdisj hI hr1 hrR hR2 (fun S hS => Nat.succ_le_of_lt (hbound S hS))
  have hpos : 0 < #R * (#R - 1) := Nat.mul_pos (by omega) (by omega)
  nlinarith

/-- In a triangle-free graph, no three pairwise adjacent vertices exist. -/
lemma not_adj_of_cliqueFree_three {V : Type} {G : SimpleGraph V}
    (hTF : G.CliqueFree 3) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    False := by
  classical
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hne_bc : b ≠ c := G.ne_of_adj hbc
  have hne_ac : a ≠ c := G.ne_of_adj hac
  apply hTF {a, b, c}
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hab | exact hab.symm | exact hbc | exact hbc.symm | exact hac | exact hac.symm
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne_bc]
    · simp [hne_ab, hne_ac]

/-- In a triangle-free graph, every neighborhood (filtered to any set) is an independent set. -/
lemma filter_adj_indep {V : Type} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (A : Finset V) (v : V) :
    ∀ x ∈ A.filter (G.Adj v), ∀ y ∈ A.filter (G.Adj v), ¬ G.Adj x y := by
  intro x hx y hy hxy
  exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2 hxy (Finset.mem_filter.mp hy).2

/-- Theorem A (Master α < 2n/5 theorem): 12-line elementary all-finite-n proof of Razborov (2021). -/
theorem five_mul_indep_lt_two_mul_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (I₀ : Set V) (hI₀ : G.IsIndepSet I₀) :
    5 * I₀.ncard < 2 * Fintype.card V := by
  classical
  by_contra hge
  push Not at hge
  set n := Fintype.card V
  set k := n / 2
  have hk_cond : ∀ S : Finset V, #S = k → 50 * (G.induce (S : Set V)).edgeSet.ncard > n ^ 2 := by
    intro S hS
    apply hH (S : Set V)
    rw [Set.ncard_coe_finset, hS]
    omega
  -- Pick maximum independent Finset I
  let indepSets : Finset (Finset V) :=
    Finset.univ.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
  have hI₀_mem : I₀.toFinset ∈ indepSets := by
    simp only [indepSets, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    intro x hx y hy hadj
    exact hI₀ hx hy (G.ne_of_adj hadj) hadj
  obtain ⟨I, hI_mem, hI_max⟩ := Finset.exists_max_image indepSets Finset.card ⟨I₀.toFinset, hI₀_mem⟩
  have hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := (Finset.mem_filter.mp hI_mem).2
  have hI_le : ∀ J : Finset V, (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) → #J ≤ #I := by
    intro J hJ
    exact hI_max J (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩)
  set α := #I
  have h5a : 2 * n ≤ 5 * α := by
    have hcard : I₀.ncard = #I₀.toFinset := Set.ncard_eq_toFinset_card' I₀
    have hle : #I₀.toFinset ≤ α := hI_max I₀.toFinset hI₀_mem
    omega
  -- Step 1: α < k (else k-subset of I has 0 edges)
  have hα_lt_k : α < k := by
    by_contra hka
    push Not at hka
    obtain ⟨S, hSI, hScard⟩ := Finset.exists_subset_card_eq hka
    have hpos := hk_cond S hScard
    have hzero : 2 * (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv
      exact hI u (hSI hu) v (hSI hv)
    omega
  set r := k - α
  have hr1 : 1 ≤ r := by omega
  have hα_pos : 0 < α := by omega
  -- Step 2: every k-subset has 2 * e > α * r
  have h_gt_ar : ∀ S : Finset V, #S = k → α * r < 2 * (G.induce (S : Set V)).edgeSet.ncard := by
    intro S hS
    have h50 := hk_cond S hS
    have h50ar : 50 * (α * r) ≤ 2 * n ^ 2 := by
      have h2r : 2 * r + 2 * α ≤ n := by omega
      have h1 : (0 : ℤ) ≤ (5 * (α : ℤ) - 2 * n) * (10 * α - n) :=
        mul_nonneg (by omega) (by omega)
      zify
      nlinarith
    omega
  -- Step 3: Partition V \ I into R₁ (high deg into I) and R₀ (low deg into I)
  let R₁ : Finset V := (Finset.univ \ I).filter (fun v => α < 2 * #(I.filter (G.Adj v)))
  let R₀ : Finset V := (Finset.univ \ I).filter (fun v => 2 * #(I.filter (G.Adj v)) ≤ α)
  have hR₁_indep : ∀ u ∈ R₁, ∀ v ∈ R₁, ¬ G.Adj u v := by
    intro u hu v hv huv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    have hdisj : Disjoint (I.filter (G.Adj u)) (I.filter (G.Adj v)) := by
      rw [Finset.disjoint_left]
      intro x hxu hxv
      exact not_adj_of_cliqueFree_three hTF huv (Finset.mem_filter.mp hxv).2 (Finset.mem_filter.mp hxu).2
    have hunion : #(I.filter (G.Adj u)) + #(I.filter (G.Adj v)) ≤ #I := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    omega
  set m₁ := #R₁
  set m₀ := #R₀
  have hm₁_le : m₁ ≤ α := hI_le R₁ hR₁_indep
  have hdisj_IR₀ : Disjoint I R₀ := by
    rw [Finset.disjoint_left]
    intro x hx hx0
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx0).1).2 hx
  have hdisj_IR₁ : Disjoint I R₁ := by
    rw [Finset.disjoint_left]
    intro x hx hx1
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx1).1).2 hx
  have hdisj_R₁R₀ : Disjoint R₁ R₀ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx0
    have h1 := (Finset.mem_filter.mp hx1).2
    have h0 := (Finset.mem_filter.mp hx0).2
    omega
  have hpart : α + m₁ + m₀ = n := by
    have hR : m₁ + m₀ = #(Finset.univ \ I) := by
      rw [← Finset.card_union_of_disjoint hdisj_R₁R₀]
      congr 1
      ext x
      simp only [R₁, R₀, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases h : α < 2 * #(I.filter (G.Adj x))
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    have hsdiff : #(Finset.univ \ I) + α = n := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
    omega
  set r₁ := k - m₁
  have hr_le_r₁ : r ≤ r₁ := by omega
  have hr_sum : r + r₁ ≤ m₀ := by omega
  have hm₀_ge_2r : 2 * r ≤ m₀ := by omega
  -- Step 4: Max independent subset J ⊆ R₀
  let indepR₀ : Finset (Finset V) :=
    R₀.powerset.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
  have hEmpty_R₀ : (∅ : Finset V) ∈ indepR₀ := by
    simp [indepR₀]
  obtain ⟨J, hJ_mem, hJ_max⟩ := Finset.exists_max_image indepR₀ Finset.card ⟨∅, hEmpty_R₀⟩
  have hJ_sub : J ⊆ R₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hJ_mem).1
  have hJ_indep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := (Finset.mem_filter.mp hJ_mem).2
  set β := #J
  -- Case 1: r ≤ β
  by_cases hβ : r ≤ β
  · obtain ⟨S, hSJ, hScard⟩ := Finset.exists_subset_card_eq hβ
    have hSR₀ : S ⊆ R₀ := hSJ.trans hJ_sub
    have hS_indep : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y := fun x hx y hy => hJ_indep x (hSJ hx) y (hSJ hy)
    have hcard_IS : #(I ∪ S) = k := by
      rw [Finset.card_union_of_disjoint (hdisj_IR₀.mono_right hSR₀), hScard]
      omega
    have hgt := h_gt_ar (I ∪ S) hcard_IS
    rw [two_mul_induce_edgeSet_ncard, sum_adj_union_indep G (hdisj_IR₀.mono_right hSR₀) hI] at hgt
    have hSS : ∑ u ∈ S, #(S.filter (G.Adj u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv
      exact hS_indep u hu v hv
    have hIS : 2 * ∑ w ∈ S, #(I.filter (G.Adj w)) ≤ r * α := by
      calc 2 * ∑ w ∈ S, #(I.filter (G.Adj w))
          = ∑ w ∈ S, 2 * #(I.filter (G.Adj w)) := Finset.mul_sum _ _ _
        _ ≤ ∑ _w ∈ S, α := Finset.sum_le_sum (fun w hw => (Finset.mem_filter.mp (hSR₀ hw)).2)
        _ = r * α := by rw [Finset.sum_const, hScard, smul_eq_mul]
    nlinarith
  -- Case 2: β < r
  · push Not at hβ
    -- Show 1 ≤ β (hence 2 ≤ r and 4 ≤ m₀)
    have hβ_pos : 1 ≤ β := by
      have hm₀_pos : 0 < #R₀ := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hm₀_pos
      have hw_mem : ({w} : Finset V) ∈ indepR₀ := by
        simp only [indepR₀, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff,
          Finset.mem_singleton]
        refine ⟨hw, ?_⟩
        rintro _ rfl _ rfl
        exact G.loopless.irrefl _
      have := hJ_max {w} hw_mem
      simpa using this
    have hr2 : 2 ≤ r := by omega
    have hm₀2 : 2 ≤ m₀ := by omega
    set e₁ := ∑ w ∈ R₀, #(I.filter (G.Adj w))
    set e₂ := ∑ w ∈ R₀, #(R₁.filter (G.Adj w))
    set d₀ := ∑ u ∈ R₀, #(R₀.filter (G.Adj u))
    -- (F1): e₁ + e₂ + d₀ ≤ m₀ * α
    have hF1 : e₁ + e₂ + d₀ ≤ m₀ * α := by
      have hsum : e₁ + e₂ + d₀ =
          ∑ w ∈ R₀, (#(I.filter (G.Adj w)) + #(R₁.filter (G.Adj w)) + #(R₀.filter (G.Adj w))) := by
        simp only [e₁, e₂, d₀, Finset.sum_add_distrib]
      rw [hsum]
      calc ∑ w ∈ R₀, (#(I.filter (G.Adj w)) + #(R₁.filter (G.Adj w)) + #(R₀.filter (G.Adj w)))
          ≤ ∑ _w ∈ R₀, α := by
            apply Finset.sum_le_sum
            intro w _
            have hd1 : Disjoint (I.filter (G.Adj w)) (R₁.filter (G.Adj w)) :=
              hdisj_IR₁.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
            have hd2 : Disjoint (I.filter (G.Adj w) ∪ R₁.filter (G.Adj w)) (R₀.filter (G.Adj w)) :=
              (Finset.disjoint_union_left.mpr ⟨hdisj_IR₀, hdisj_R₁R₀⟩).mono
                (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _))
                (Finset.filter_subset _ _)
            rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
            have hsub : I.filter (G.Adj w) ∪ R₁.filter (G.Adj w) ∪ R₀.filter (G.Adj w) ⊆
                Finset.univ.filter (G.Adj w) := by
              intro x hx
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              rcases hx with (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩ <;> exact h
            exact (Finset.card_le_card hsub).trans (hI_le _ (filter_adj_indep hTF Finset.univ w))
        _ = m₀ * α := by rw [Finset.sum_const, smul_eq_mul]
    -- (F2): e₁ ≤ α * (r - 1)
    have hF2 : e₁ ≤ α * (r - 1) := by
      have hswap : e₁ = ∑ x ∈ I, #(R₀.filter (G.Adj x)) := by
        simp only [e₁, Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro w _
        simp [G.adj_comm]
      rw [hswap]
      calc ∑ x ∈ I, #(R₀.filter (G.Adj x))
          ≤ ∑ _x ∈ I, (r - 1) := by
            apply Finset.sum_le_sum
            intro x _
            have hmem : R₀.filter (G.Adj x) ∈ indepR₀ :=
              Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
                filter_adj_indep hTF R₀ x⟩
            have hle := hJ_max _ hmem
            omega
        _ = α * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
    -- (F3): averaging over r-subsets S ⊆ R₀ added to I
    have hF3_raw : α * r * m₀ * (m₀ - 1) < 2 * r * (m₀ - 1) * e₁ + r * (r - 1) * d₀ := by
      refine avg_indep_union_gt G hdisj_IR₀ hI hr1 (by omega) hm₀2 ?_
      intro S hS
      apply h_gt_ar (I ∪ S)
      rw [Finset.card_union_of_disjoint (hdisj_IR₀.mono_right (Finset.mem_powersetCard.mp hS).1),
        (Finset.mem_powersetCard.mp hS).2]
      omega
    have hF3 : α * m₀ * (m₀ - 1) < 2 * (m₀ - 1) * e₁ + (r - 1) * d₀ := by
      have hrpos : 0 < r := by omega
      nlinarith
    -- (F4): averaging over r₁-subsets S' ⊆ R₀ added to R₁
    have hF4 : α * r * m₀ * (m₀ - 1) < 2 * r₁ * (m₀ - 1) * e₂ + r₁ * (r₁ - 1) * d₀ := by
      refine avg_indep_union_gt G hdisj_R₁R₀ hR₁_indep (by omega) (by omega) hm₀2 ?_
      intro S hS
      apply h_gt_ar (R₁ ∪ S)
      rw [Finset.card_union_of_disjoint (hdisj_R₁R₀.mono_right (Finset.mem_powersetCard.mp hS).1),
        (Finset.mem_powersetCard.mp hS).2]
      omega
    -- Exact integer cancellation ending in d² + (r+d)*s + 2r + 3d > 0
    have hfinal : False := by
      have hA : (0 : ℤ) < (α : ℤ) := Nat.cast_pos.mpr hα_pos
      have hR : (2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr2
      have hRR1 : (r : ℤ) ≤ (r₁ : ℤ) := Nat.cast_le.mpr hr_le_r₁
      have hsumR : (r : ℤ) + (r₁ : ℤ) ≤ (m₀ : ℤ) := by exact_mod_cast hr_sum
      have hD0 : (0 : ℤ) ≤ (d₀ : ℤ) := Nat.cast_nonneg d₀
      have h1z : (e₁ : ℤ) + (e₂ : ℤ) + (d₀ : ℤ) ≤ (m₀ : ℤ) * (α : ℤ) := by exact_mod_cast hF1
      have h2z : (e₁ : ℤ) ≤ (α : ℤ) * ((r : ℤ) - 1) := by
        have : (e₁ : ℤ) ≤ ((α * (r - 1) : ℕ) : ℤ) := Nat.cast_le.mpr hF2
        rw [Nat.cast_mul, Nat.cast_sub (by omega)] at this
        simpa using this
      have h3z : (α : ℤ) * (m₀ : ℤ) * ((m₀ : ℤ) - 1) <
          2 * ((m₀ : ℤ) - 1) * (e₁ : ℤ) + ((r : ℤ) - 1) * (d₀ : ℤ) := by
        have : ((α * m₀ * (m₀ - 1) : ℕ) : ℤ) < ((2 * (m₀ - 1) * e₁ + (r - 1) * d₀ : ℕ) : ℤ) :=
          Nat.cast_lt.mpr hF3
        push_cast [Nat.cast_sub (show 1 ≤ m₀ by omega), Nat.cast_sub (show 1 ≤ r by omega)] at this
        simpa using this
      have h4z : (α : ℤ) * (r : ℤ) * (m₀ : ℤ) * ((m₀ : ℤ) - 1) <
          2 * (r₁ : ℤ) * ((m₀ : ℤ) - 1) * (e₂ : ℤ) + (r₁ : ℤ) * ((r₁ : ℤ) - 1) * (d₀ : ℤ) := by
        have : ((α * r * m₀ * (m₀ - 1) : ℕ) : ℤ) <
            ((2 * r₁ * (m₀ - 1) * e₂ + r₁ * (r₁ - 1) * d₀ : ℕ) : ℤ) :=
          Nat.cast_lt.mpr hF4
        push_cast [Nat.cast_sub (show 1 ≤ m₀ by omega), Nat.cast_sub (show 1 ≤ r₁ by omega)] at this
        simpa using this
      set A : ℤ := (α : ℤ)
      set M : ℤ := (m₀ : ℤ)
      set R : ℤ := (r : ℤ)
      set R1 : ℤ := (r₁ : ℤ)
      set E1 : ℤ := (e₁ : ℤ)
      set E2 : ℤ := (e₂ : ℤ)
      set D0 : ℤ := (d₀ : ℤ)
      have hM1 : 0 < M - 1 := by linarith
      have hMpos : 0 < M := by linarith
      have hR1pos : 0 < R1 := by linarith
      have hR1m : 0 < R - 1 := by linarith
      have hw1 : 0 < R1 * (M + R - 1) := mul_pos hR1pos (by linarith)
      have hc1 := mul_lt_mul_of_pos_left h3z hw1
      have hc2 := mul_lt_mul_of_pos_left h4z hR1m
      have hadd : R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) <
          R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
          (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) := add_lt_add hc1 hc2
      have hnn1 : 0 ≤ 2 * (M - 1) * R1 * (R - 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1.le) hR1pos.le) hR1m.le
      have hnn2 : 0 ≤ 2 * (M - 1) * R1 * M :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1.le) hR1pos.le) hMpos.le
      have hnn3 : 0 ≤ (R - 1) * R1 * D0 :=
        mul_nonneg (mul_nonneg hR1m.le hR1pos.le) hD0
      have hterm1 : 2 * (M - 1) * R1 * (R - 1) * (E1 + E2 + D0) ≤
          2 * (M - 1) * R1 * (R - 1) * (M * A) := mul_le_mul_of_nonneg_left h1z hnn1
      have hterm2 : 2 * (M - 1) * R1 * M * E1 ≤ 2 * (M - 1) * R1 * M * (A * (R - 1)) :=
        mul_le_mul_of_nonneg_left h2z hnn2
      have hterm3 : (R - 1) * R1 * D0 * (R + R1 - M) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hnn3 (by linarith)
      have hrhs : R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
          (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) ≤
          4 * A * M * (M - 1) * R1 * (R - 1) := by
        have hid : R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
            (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) =
            2 * (M - 1) * R1 * (R - 1) * (E1 + E2 + D0) +
            2 * (M - 1) * R1 * M * E1 +
            (R - 1) * R1 * D0 * (R + R1 - M) := by ring
        have hsum4 : 2 * (M - 1) * R1 * (R - 1) * (M * A) +
            2 * (M - 1) * R1 * M * (A * (R - 1)) = 4 * A * M * (M - 1) * R1 * (R - 1) := by ring
        linarith
      have hcore : 0 < R1 * (M - 3 * R + 3) + R * (R - 1) := by
        have hdecomp : R1 * (M - 3 * R + 3) + R * (R - 1) =
            (R1 - R) ^ 2 + R1 * (M - R - R1) + 2 * R + 3 * (R1 - R) := by ring
        have hnonneg1 : 0 ≤ (R1 - R) ^ 2 := sq_nonneg _
        have hnonneg2 : 0 ≤ R1 * (M - R - R1) := mul_nonneg hR1pos.le (by linarith)
        linarith
      have hlhs : 4 * A * M * (M - 1) * R1 * (R - 1) <
          R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) := by
        have hid2 : R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) -
            4 * A * M * (M - 1) * R1 * (R - 1) =
            (A * M * (M - 1)) * (R1 * (M - 3 * R + 3) + R * (R - 1)) := by ring
        have hpos_f : 0 < A * M * (M - 1) := mul_pos (mul_pos hA hMpos) hM1
        have := mul_pos hpos_f hcore
        linarith
      linarith
    exact hfinal

/-- Corollary A1: Every vertex has degree < 2n/5. -/
theorem five_mul_deg_lt_two_mul_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (v : V) :
    5 * (G.neighborSet v).ncard < 2 * Fintype.card V := by
  apply five_mul_indep_lt_two_mul_card G hTF hH (G.neighborSet v)
  intro x hx y hy _ hxy
  exact not_adj_of_cliqueFree_three hTF hx hxy hy

/-- Corollary A2 (Keevash-Sudakov 2006): Total edge count satisfies 5 * e(G) < n^2. -/
theorem five_mul_edges_lt_sq {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    5 * G.edgeSet.ncard < Fintype.card V ^ 2 := by
  classical
  have hne : 0 < Fintype.card V := by
    by_contra h0
    have hcard0 : Fintype.card V = 0 := by omega
    have h := hH ∅ (by simp [hcard0])
    have hempty : 2 * (G.induce (∅ : Set V)).edgeSet.ncard = 0 := by
      have h2 := two_mul_induce_edgeSet_ncard G (∅ : Finset V)
      rw [Finset.coe_empty] at h2
      simpa using h2
    omega
  have hedge : 2 * G.edgeSet.ncard = ∑ v : V, (G.neighborSet v).ncard := by
    have h1 : G.edgeSet.ncard = #G.edgeFinset := by
      rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
    apply Finset.sum_congr rfl
    intro v _
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
  have hsum : ∑ v : V, 5 * (G.neighborSet v).ncard < ∑ _v : V, 2 * Fintype.card V := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by simpa using hne))
    intro v _
    exact five_mul_deg_lt_two_mul_card G hTF hH v
  rw [← Finset.mul_sum, ← hedge, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  nlinarith

/-- Small-n elimination: n >= 6. -/
lemma six_le_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    6 ≤ Fintype.card V := by
  classical
  by_contra hlt
  push Not at hlt
  set n := Fintype.card V
  by_cases hn3 : n ≤ 3
  · have hle : n / 2 ≤ #(Finset.univ : Finset V) := by simp; omega
    obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq hle
    have hpos := hH (S : Set V) (by rw [Set.ncard_coe_finset, hScard]; omega)
    have hzero : 2 * (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      by_cases h0 : #S = 0
      · rw [Finset.card_eq_zero.mp h0]; simp
      · have h1 : #S = 1 := by omega
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
        simp
    omega
  · -- n = 4 or 5: every pair is adjacent, so any 3 distinct vertices form a triangle
    have hn4 : 4 ≤ n := by omega
    have hall : ∀ a b : V, a ≠ b → G.Adj a b := by
      intro a b hab
      have hcard2 : #({a, b} : Finset V) = 2 := Finset.card_pair hab
      have hpos := hH (({a, b} : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard2]; omega)
      by_contra hnadj
      have hzero : 2 * (G.induce (({a, b} : Finset V) : Set V)).edgeSet.ncard = 0 := by
        rw [two_mul_induce_edgeSet_ncard]
        rw [Finset.sum_pair hab]
        have ha : ({a, b} : Finset V).filter (G.Adj a) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact G.loopless.irrefl _
          · rw [Finset.mem_singleton.mp hx']; exact hnadj
        have hb : ({a, b} : Finset V).filter (G.Adj b) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact fun h => hnadj h.symm
          · rw [Finset.mem_singleton.mp hx']; exact G.loopless.irrefl _
        rw [ha, hb]; simp
      omega
    have h3le : 3 ≤ #(Finset.univ : Finset V) := by simp; omega
    obtain ⟨T, -, hTcard⟩ := Finset.exists_subset_card_eq h3le
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hTcard
    exact not_adj_of_cliqueFree_three hTF (hall a b hab) (hall b c hbc) (hall a c hac)

/-- Exact finite-n neighborhood averaging inequality (Theorem B core). -/
lemma neighborhood_avg_ineq {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    let n : ℤ := Fintype.card V
    let k : ℤ := (Fintype.card V / 2 : ℕ)
    let m : ℤ := G.edgeSet.ncard
    let T0 : ℤ := (Fintype.card V ^ 2 / 50 + 1 : ℕ)
    T0 * (n ^ 2 * (n - 1) * (n - 2) - 2 * n * (2 * n - 3) * m + 4 * m ^ 2) +
      (k - 1) * (k - 2) * (4 * m ^ 2) ≤ (k - 1) * (k - 2) * n ^ 2 * m := by
  classical
  set nN := Fintype.card V
  set kN := nN / 2
  set mN := G.edgeSet.ncard
  set T0N := nN ^ 2 / 50 + 1
  have hn6 : 6 ≤ nN := six_le_card G hTF hH
  have hk3 : 3 ≤ kN := by omega
  have hdeg_lt : ∀ v : V, G.degree v < kN := by
    intro v
    have h5 := five_mul_deg_lt_two_mul_card G hTF hH v
    have hdeq : G.degree v = (G.neighborSet v).ncard := by
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
    omega
  have hm_eq : 2 * mN = ∑ v : V, G.degree v := by
    have h1 : mN = #G.edgeFinset := by
      show G.edgeSet.ncard = #G.edgeFinset
      rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  -- Per-vertex inequality
  have hper_v : ∀ v : V,
      T0N * (nN - 1 - G.degree v) * (nN - 2 - G.degree v) +
        (kN - 1) * (kN - 2) * (∑ x ∈ G.neighborFinset v, G.degree x) ≤
      (kN - 1) * (kN - 2) * mN := by
    intro v
    let Nv : Finset V := G.neighborFinset v
    let Mv : Finset V := (Finset.univ.erase v) \ Nv
    have hv_not_Nv : v ∉ Nv := by simp [Nv]
    have hNv_sub : Nv ⊆ Finset.univ.erase v := by
      intro x hx
      have hadj : G.Adj v x := (SimpleGraph.mem_neighborFinset G v x).mp hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hadj).symm, Finset.mem_univ _⟩
    have hMv_card : #Mv = nN - 1 - G.degree v := by
      have h1 : #Mv + #Nv = #(Finset.univ.erase v) := Finset.card_sdiff_add_card_eq_card hNv_sub
      have h2 : #(Finset.univ.erase v) = nN - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
      have h3 : #Nv = G.degree v := rfl
      omega
    have hdv_lt : G.degree v < kN := hdeg_lt v
    have hMv_ge : kN ≤ #Mv := by omega
    have hdisj_vM : Disjoint ({v} : Finset V) Mv := by
      rw [Finset.disjoint_singleton_left]
      intro h
      exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
    have hv_indep : ∀ x ∈ ({v} : Finset V), ∀ y ∈ ({v} : Finset V), ¬ G.Adj x y := by
      rintro x hx y hy
      rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
      exact G.loopless.irrefl v
    have havg := avg_indep_union_ge G hdisj_vM hv_indep (r := kN - 1) (T := 2 * T0N)
      (by omega) (by omega) (by omega) (by
        intro S hS
        have hScard : #({v} ∪ S) = kN := by
          rw [Finset.card_union_of_disjoint (hdisj_vM.mono_right (Finset.mem_powersetCard.mp hS).1),
            Finset.card_singleton, (Finset.mem_powersetCard.mp hS).2]
          omega
        have h50 := hH (({v} ∪ S : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hScard]; omega)
        omega)
    have hzero_v : ∑ w ∈ Mv, #(({v} : Finset V).filter (G.Adj w)) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      intro hadj
      exact (Finset.mem_sdiff.mp hw).2 ((SimpleGraph.mem_neighborFinset G v w).mpr hadj.symm)
    rw [hzero_v, mul_zero, zero_add] at havg
    -- Exact triangle-free identity: ∑ u ∈ Mv, #(Mv.filter (G.Adj u)) + 2 * ∑ x ∈ Nv, deg x = 2 * mN
    have htf_id : ∑ u ∈ Mv, #(Mv.filter (G.Adj u)) + 2 * ∑ x ∈ Nv, G.degree x = 2 * mN := by
      have hpart_univ : Finset.univ = insert v (Nv ∪ Mv) := by
        ext x
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Mv, Finset.mem_sdiff,
          Finset.mem_erase, true_iff]
        by_cases hxv : x = v
        · exact Or.inl hxv
        · by_cases hxN : x ∈ Nv
          · exact Or.inr (Or.inl hxN)
          · exact Or.inr (Or.inr ⟨⟨hxv, trivial⟩, hxN⟩)
      have hdisj_NM : Disjoint Nv Mv := Finset.disjoint_sdiff
      have hv_not_NM : v ∉ Nv ∪ Mv := by
        simp only [Finset.mem_union, not_or]
        exact ⟨hv_not_Nv, fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl⟩
      have hsum_all : 2 * mN = G.degree v + (∑ x ∈ Nv, G.degree x) + (∑ u ∈ Mv, G.degree u) := by
        rw [hm_eq, hpart_univ, Finset.sum_insert hv_not_NM, Finset.sum_union hdisj_NM]
        omega
      have hdeg_M : ∀ u ∈ Mv, G.degree u = #(Nv.filter (G.Adj u)) + #(Mv.filter (G.Adj u)) := by
        intro u hu
        have hnuv : ¬ G.Adj u v := fun hadj =>
          (Finset.mem_sdiff.mp hu).2 ((SimpleGraph.mem_neighborFinset G v u).mpr hadj.symm)
        have heq : G.neighborFinset u = Nv.filter (G.Adj u) ∪ Mv.filter (G.Adj u) := by
          ext w
          simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_filter,
            Mv, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · intro hadj
            by_cases hwN : w ∈ Nv
            · exact Or.inl ⟨hwN, hadj⟩
            · exact Or.inr ⟨⟨fun h => hnuv (h ▸ hadj), hwN⟩, hadj⟩
          · rintro (⟨_, hadj⟩ | ⟨_, hadj⟩) <;> exact hadj
        rw [SimpleGraph.degree, heq, Finset.card_union_of_disjoint
          (hdisj_NM.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      have hswap : ∑ u ∈ Mv, #(Nv.filter (G.Adj u)) = ∑ x ∈ Nv, #(Mv.filter (G.Adj x)) := by
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro u _
        simp [G.adj_comm]
      have hdeg_N : ∀ x ∈ Nv, G.degree x = 1 + #(Mv.filter (G.Adj x)) := by
        intro x hx
        have hvx : G.Adj v x := (SimpleGraph.mem_neighborFinset G v x).mp hx
        have hxv : G.Adj x v := hvx.symm
        have heq : G.neighborFinset x = insert v (Mv.filter (G.Adj x)) := by
          ext w
          simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_filter,
            Mv, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · intro hadj
            by_cases hwv : w = v
            · exact Or.inl hwv
            · refine Or.inr ⟨⟨hwv, ?_⟩, hadj⟩
              intro hwN
              exact not_adj_of_cliqueFree_three hTF hvx hadj ((SimpleGraph.mem_neighborFinset G v w).mp hwN)
          · rintro (rfl | ⟨_, hadj⟩)
            · exact hxv
            · exact hadj
        have hv_not : v ∉ Mv.filter (G.Adj x) := fun h =>
          (Finset.mem_erase.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1).1 rfl
        rw [SimpleGraph.degree, heq, Finset.card_insert_of_notMem hv_not]
        omega
      have hsum_N : ∑ x ∈ Nv, G.degree x = G.degree v + ∑ x ∈ Nv, #(Mv.filter (G.Adj x)) := by
        calc ∑ x ∈ Nv, G.degree x
            = ∑ x ∈ Nv, (1 + #(Mv.filter (G.Adj x))) := Finset.sum_congr rfl hdeg_N
          _ = ∑ _x ∈ Nv, 1 + ∑ x ∈ Nv, #(Mv.filter (G.Adj x)) := Finset.sum_add_distrib
          _ = G.degree v + ∑ x ∈ Nv, #(Mv.filter (G.Adj x)) := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]; rfl
      have hsum_M : ∑ u ∈ Mv, G.degree u =
          (∑ x ∈ Nv, #(Mv.filter (G.Adj x))) + ∑ u ∈ Mv, #(Mv.filter (G.Adj u)) := by
        rw [Finset.sum_congr rfl hdeg_M, Finset.sum_add_distrib, hswap]
      omega
    have hMv_sub1 : #Mv - 1 = nN - 2 - G.degree v := by omega
    rw [hMv_sub1, hMv_card, show kN - 1 - 1 = kN - 2 by omega] at havg
    have hmul_id : (kN - 1) * (kN - 2) * (∑ u ∈ Mv, #(Mv.filter (G.Adj u))) +
        2 * ((kN - 1) * (kN - 2) * (∑ x ∈ Nv, G.degree x)) =
        2 * ((kN - 1) * (kN - 2) * mN) := by
      have := congrArg (fun t => (kN - 1) * (kN - 2) * t) htf_id
      linarith
    have hstep : 2 * (T0N * (nN - 1 - G.degree v) * (nN - 2 - G.degree v) +
        (kN - 1) * (kN - 2) * (∑ x ∈ Nv, G.degree x)) ≤ 2 * ((kN - 1) * (kN - 2) * mN) := by
      linarith
    have hstep' : T0N * (nN - 1 - G.degree v) * (nN - 2 - G.degree v) +
        (kN - 1) * (kN - 2) * (∑ x ∈ Nv, G.degree x) ≤ (kN - 1) * (kN - 2) * mN := by omega
    exact hstep'
  -- Sum hper_v over all v : V and apply Cauchy-Schwarz
  have hsum_v : ∑ v : V, (T0N * (nN - 1 - G.degree v) * (nN - 2 - G.degree v) +
        (kN - 1) * (kN - 2) * (∑ x ∈ G.neighborFinset v, G.degree x)) ≤
      ∑ _v : V, (kN - 1) * (kN - 2) * mN :=
    Finset.sum_le_sum (fun v _ => hper_v v)
  have hsum_deg_sq : ∑ v : V, ∑ x ∈ G.neighborFinset v, G.degree x = ∑ x : V, G.degree x ^ 2 := by
    have h1 : ∀ v : V, ∑ x ∈ G.neighborFinset v, G.degree x =
        ∑ x : V, if G.Adj v x then G.degree x else 0 := by
      intro v
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hf : #(Finset.univ.filter (fun v => G.Adj v x)) = G.degree x := by
      rw [SimpleGraph.degree]
      congr 1
      ext v
      simp [G.adj_comm]
    rw [hf, sq]
  have hsum_v' : T0N * (∑ v : V, (nN - 1 - G.degree v) * (nN - 2 - G.degree v)) +
      (kN - 1) * (kN - 2) * (∑ x : V, G.degree x ^ 2) ≤ nN * ((kN - 1) * (kN - 2) * mN) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_deg_sq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum_v
    have hpull : ∑ v : V, T0N * (nN - 1 - G.degree v) * (nN - 2 - G.degree v) =
        T0N * ∑ v : V, (nN - 1 - G.degree v) * (nN - 2 - G.degree v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _; ring
    rw [hpull] at hsum_v
    exact hsum_v
  -- Cast to ℤ cleanly
  have hsum_d_z : ∑ v : V, (G.degree v : ℤ) = 2 * (mN : ℤ) := by
    have : ((∑ v : V, G.degree v : ℕ) : ℤ) = ((2 * mN : ℕ) : ℤ) := congrArg Nat.cast hm_eq.symm
    simpa using this
  have hhk3 : (3 : ℤ) ≤ (kN : ℤ) := by exact_mod_cast hk3
  set n : ℤ := (nN : ℤ)
  set k : ℤ := (kN : ℤ)
  set m : ℤ := (mN : ℤ)
  set T0 : ℤ := (T0N : ℤ)
  set S2 : ℤ := ((∑ x : V, G.degree x ^ 2 : ℕ) : ℤ)
  have hS2_eq : S2 = ∑ x : V, (G.degree x : ℤ) ^ 2 := by simp [S2]
  have hsum_M_z : ((∑ v : V, (nN - 1 - G.degree v) * (nN - 2 - G.degree v) : ℕ) : ℤ) =
      n * (n - 1) * (n - 2) - 2 * (2 * n - 3) * m + S2 := by
    have hterm : ∀ v : V, (((nN - 1 - G.degree v) * (nN - 2 - G.degree v) : ℕ) : ℤ) =
        (n - 1) * (n - 2) - (2 * n - 3) * (G.degree v : ℤ) + (G.degree v : ℤ) ^ 2 := by
      intro v
      have hd := hdeg_lt v
      push_cast [Nat.cast_sub (show G.degree v ≤ nN - 1 by omega),
        Nat.cast_sub (show G.degree v ≤ nN - 2 by omega),
        Nat.cast_sub (show 1 ≤ nN by omega),
        Nat.cast_sub (show 2 ≤ nN by omega)]
      ring
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun v _ => hterm v),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, ← hS2_eq, hsum_d_z]
    ring
  have hsum_z : T0 * (n * (n - 1) * (n - 2) - 2 * (2 * n - 3) * m + S2) +
      (k - 1) * (k - 2) * S2 ≤ n * ((k - 1) * (k - 2) * m) := by
    have hcast : ((T0N * ∑ v : V, (nN - 1 - G.degree v) * (nN - 2 - G.degree v) +
        (kN - 1) * (kN - 2) * ∑ x : V, G.degree x ^ 2 : ℕ) : ℤ) ≤
        ((nN * ((kN - 1) * (kN - 2) * mN) : ℕ) : ℤ) := Nat.cast_le.mpr hsum_v'
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega), hsum_M_z] at hcast
    simpa [n, k, m, T0, S2] using hcast
  -- Cauchy-Schwarz: (2 * m)^2 ≤ n * S2
  have hCS : 4 * m ^ 2 ≤ n * S2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := fun v => (G.degree v : ℤ))
    rw [hsum_d_z, Finset.card_univ, ← hS2_eq] at hcs
    linarith
  have hn_pos : 0 ≤ n := Nat.cast_nonneg nN
  have hmul_n := mul_le_mul_of_nonneg_left hsum_z hn_pos
  have hcoeff_nonneg : 0 ≤ T0 + (k - 1) * (k - 2) := by
    have : 0 ≤ T0 := Nat.cast_nonneg T0N
    nlinarith
  have hcs_mul := mul_le_mul_of_nonneg_left hCS hcoeff_nonneg
  linarith


/-- Deleting an independent subset J ⊆ S removes exactly ∑_{w ∈ J} d_S(w) edges from G[S]. -/
lemma induce_edgeSet_ncard_sdiff_indep {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S J : Finset V}
    (hJS : J ⊆ S) (hJ : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) :
    (G.induce ((S \ J : Finset V) : Set V)).edgeSet.ncard + ∑ w ∈ J, #(S.filter (G.Adj w)) =
      (G.induce (S : Set V)).edgeSet.ncard := by
  have hunion : J ∪ (S \ J) = S := Finset.union_sdiff_of_subset hJS
  have hdisj : Disjoint J (S \ J) := Finset.disjoint_sdiff
  have h2S := two_mul_induce_edgeSet_ncard G S
  have h2R := two_mul_induce_edgeSet_ncard G (S \ J)
  have hsum := sum_adj_union_indep G hdisj hJ
  rw [hunion] at hsum
  have hcross : ∑ w ∈ S \ J, #(J.filter (G.Adj w)) = ∑ w ∈ J, #(S.filter (G.Adj w)) := by
    have h1 : ∑ w ∈ S \ J, #(J.filter (G.Adj w)) = ∑ x ∈ J, #((S \ J).filter (G.Adj x)) := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
    rw [h1]
    apply Finset.sum_congr rfl; intro x hx
    congr 1; ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨fun ⟨⟨hyS, _⟩, hadj⟩ => ⟨hyS, hadj⟩, fun ⟨hyS, hadj⟩ => ⟨⟨hyS, fun hyJ => hJ x hx y hyJ hadj⟩, hadj⟩⟩
  omega


/-- Pure rational helper for Subcase B2 of Theorem I's linear separator. -/
lemma quadratic_potential_sep_B2
    {nq kq N u Mq : ℚ}
    (hnq_ge6 : 6 ≤ nq) (hkq_lo : 2 * kq ≤ nq) (hkq_hi : nq ≤ 2 * kq + 1)
    (hu_eq : u = N - kq) (hu_pos : 0 < u) (hN_pos : 0 < N) (hN_le_n : N ≤ nq)
    (hMF : Mq ≤ nq ^ 2 / 50 + 2 * nq * u / 25 + u ^ 2 / 8)
    (hdu : 2 * Mq / N ≤ u)
    (hB1 : 2 * nq / 25 + u / 4 < 9 * (2 * Mq / N) / 4) :
    ∃ lam : ℚ, lam ≤ 0 ∧
      (∀ x : ℚ, 0 ≤ x → x ≤ u →
        (Mq - (nq ^ 2 / 50 + 2 * nq * u / 25 + u ^ 2 / 8)) + (2 * nq / 25 + u / 4) * x - 9 * x ^ 2 / 8 ≤
          lam * (x - 2 * Mq / N)) ∧
      (∀ x : ℚ, u ≤ x →
        ((Mq - nq ^ 2 / 50) / u) * x - x ^ 2 ≤ lam * (x - 2 * Mq / N)) := by
  set FN : ℚ := nq ^ 2 / 50 + 2 * nq * u / 25 + u ^ 2 / 8
  set dbar : ℚ := 2 * Mq / N
  set p1 : ℚ := 2 * nq / 25 + u / 4
  set p2 : ℚ := (Mq - nq ^ 2 / 50) / u
  set lam : ℚ := p1 - 9 * dbar / 4
  set gM : ℚ := (Mq - FN) + dbar * (p1 - 9 * dbar / 8)
  set dbarF : ℚ := 2 * FN / N
  set gF : ℚ := dbarF * (p1 - 9 * dbarF / 8)
  have hFN_pos : 0 < FN := by
    dsimp only [FN]
    have h1 : 0 < nq ^ 2 / 50 := by nlinarith only [hnq_ge6]
    have h2 : 0 ≤ 2 * nq * u / 25 := by nlinarith only [hnq_ge6, hu_pos]
    have h3 : 0 ≤ u ^ 2 / 8 := by nlinarith only [hu_pos]
    linarith only [h1, h2, h3]
  have hdbarF_pos : 0 < dbarF := div_pos (by linarith only [hFN_pos]) hN_pos
  have hg_mono : gM ≤ gF := by
    have hdiff : gF - gM = (FN - Mq) / N ^ 2 * (N ^ 2 + 2 * N * p1 - 9 * (FN + Mq) / 2) := by
      dsimp only [gM, gF, dbar, dbarF]; field_simp [hN_pos.ne']; ring
    set rq : ℚ := nq - 2 * kq
    have hrq1 : rq ≤ 1 := by dsimp only [rq]; linarith only [hkq_hi]
    have hN_r : N = (nq - rq) / 2 + u := by dsimp only [rq]; linarith only [hu_eq]
    have hexp : N ^ 2 + 2 * N * p1 - 9 * FN =
        3 * nq ^ 2 / 20 + 69 * nq * u / 100 + 3 * u ^ 2 / 8 -
          rq * (29 * nq / 50 + 5 * u / 4) + rq ^ 2 / 4 := by
      rw [hN_r]; dsimp only [p1, FN]; ring
    have hpos1 : 0 < N ^ 2 + 2 * N * p1 - 9 * FN := by
      have h1 : rq * (29 * nq / 50 + 5 * u / 4) ≤ 29 * nq / 50 + 5 * u / 4 := by
        nlinarith only [hrq1, hnq_ge6, hu_pos]
      have h2 : 0 < 3 * nq ^ 2 / 20 - 29 * nq / 50 := by nlinarith only [hnq_ge6]
      have h3 : 0 < 69 * nq * u / 100 - 5 * u / 4 := by nlinarith only [hnq_ge6, hu_pos]
      have h4 : 0 ≤ 3 * u ^ 2 / 8 + rq ^ 2 / 4 :=
        add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
          (div_nonneg (sq_nonneg _) (by norm_num))
      linarith only [hexp, h1, h2, h3, h4]
    have hpos2 : 0 ≤ N ^ 2 + 2 * N * p1 - 9 * (FN + Mq) / 2 := by linarith only [hpos1, hMF]
    have hfac : 0 ≤ (FN - Mq) / N ^ 2 := div_nonneg (by linarith only [hMF]) (sq_nonneg N)
    have hge0 : 0 ≤ gF - gM := by rw [hdiff]; exact mul_nonneg hfac hpos2
    linarith only [hge0]
  have hgF_sos : gF = dbarF / N * (-(u - 2 * nq / 5) ^ 2 / 32 - (nq / 25 + u / 8) * (nq - 2 * kq)) := by
    have h1 : N * p1 - 9 * FN / 4 = -(u - 2 * nq / 5) ^ 2 / 32 - (nq / 25 + u / 8) * (nq - 2 * kq) := by
      have hNku : N = kq + u := by linarith only [hu_eq]
      rw [hNku]; dsimp only [p1, FN]; ring
    dsimp only [gF, dbarF]
    have h2 : 2 * FN / N * (p1 - 9 * (2 * FN / N) / 8) = (2 * FN / N) / N * (N * p1 - 9 * FN / 4) := by
      field_simp [hN_pos.ne']; ring
    rw [h2, h1]
  have hgF_le : gF ≤ -(dbarF / (32 * N)) * (u - 2 * nq / 5) ^ 2 := by
    have hrem : 0 ≤ (nq / 25 + u / 8) * (nq - 2 * kq) := by nlinarith only [hnq_ge6, hu_pos, hkq_lo]
    have hfac : 0 ≤ dbarF / N := div_nonneg hdbarF_pos.le hN_pos.le
    have hstep : dbarF / N * (-(u - 2 * nq / 5) ^ 2 / 32 - (nq / 25 + u / 8) * (nq - 2 * kq)) ≤
        dbarF / N * (-(u - 2 * nq / 5) ^ 2 / 32) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrem]) hfac
    have hR : dbarF / N * (-(u - 2 * nq / 5) ^ 2 / 32) = -(dbarF / (32 * N)) * (u - 2 * nq / 5) ^ 2 := by
      field_simp [hN_pos.ne']
    linarith only [hgF_sos, hstep, hR]
  have hgF_nonpos : gF ≤ 0 := by
    have : 0 ≤ dbarF / (32 * N) * (u - 2 * nq / 5) ^ 2 :=
      mul_nonneg (div_nonneg hdbarF_pos.le (by linarith only [hN_pos])) (sq_nonneg _)
    linarith only [hgF_le, this]
  refine ⟨lam, by dsimp only [lam]; linarith only [hB1], ?_, ?_⟩
  · intro x _ _
    have hP1_eq : (Mq - FN) + p1 * x - 9 * x ^ 2 / 8 - lam * (x - dbar) =
        -9 / 8 * (x - dbar) ^ 2 + gM := by dsimp only [lam, gM]; ring
    have hsq0 : 0 ≤ 9 / 8 * (x - dbar) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith only [hP1_eq, hsq0, hg_mono, hgF_nonpos]
  · intro x hux
    set s : ℚ := p2 - 2 * u - lam
    have hP12_u : (Mq - FN) + p1 * u - 9 * u ^ 2 / 8 = p2 * u - u ^ 2 := by
      dsimp only [FN, p1, p2]; field_simp [hu_pos.ne']; ring
    have hhu : p2 * u - u ^ 2 - lam * (u - dbar) = -9 / 8 * (u - dbar) ^ 2 + gM := by
      rw [← hP12_u]; dsimp only [lam, gM]; ring
    have hhu_le : p2 * u - u ^ 2 - lam * (u - dbar) ≤ gF := by
      have : 0 ≤ 9 / 8 * (u - dbar) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
      linarith only [hhu, this, hg_mono]
    have hh_eq : p2 * x - x ^ 2 - lam * (x - dbar) =
        (p2 * u - u ^ 2 - lam * (u - dbar)) + s * (x - u) - (x - u) ^ 2 := by
      dsimp only [s]; ring
    by_cases hs0 : s ≤ 0
    · have h1 : s * (x - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs0 (by linarith only [hux])
      have h2 : 0 ≤ (x - u) ^ 2 := sq_nonneg _
      linarith only [hh_eq, hhu_le, hgF_nonpos, h1, h2]
    · push Not at hs0
      have hp2_le_F : p2 ≤ p1 - u / 8 := by
        have h1 : (Mq - nq ^ 2 / 50) / u ≤ (FN - nq ^ 2 / 50) / u :=
          div_le_div_of_nonneg_right (by linarith only [hMF]) hu_pos.le
        have h2 : (FN - nq ^ 2 / 50) / u = p1 - u / 8 := by
          dsimp only [FN, p1]; field_simp [hu_pos.ne']; ring
        linarith only [h1, h2]
      have hs_le : s ≤ u / 8 := by dsimp only [s, lam]; linarith only [hp2_le_F, hdu]
      have hdbar_gt : 17 * u < 18 * dbar := by dsimp only [s, lam] at hs0; linarith only [hs0, hp2_le_F]
      have hdbar_le_F : dbar ≤ dbarF := div_le_div_of_nonneg_right (by linarith only [hMF]) hN_pos.le
      have h17_lt : 17 * N * u < 36 * FN := by
        have h1 : 17 * u < 18 * (2 * FN / N) := by linarith only [hdbar_gt, hdbar_le_F]
        have h2 := mul_lt_mul_of_pos_left h1 hN_pos
        have hR : N * (18 * (2 * FN / N)) = 36 * FN := by field_simp [hN_pos.ne']; ring
        linarith only [h2, hR]
      have hu_lt_fifth : u < nq / 5 := by
        by_contra hge
        push Not at hge
        set t : ℚ := u - nq / 5
        have ht0 : 0 ≤ t := by dsimp only [t]; linarith only [hge]
        have h12k : 5 * nq ≤ 12 * kq := by linarith only [hnq_ge6, hkq_hi]
        have hN_lo : 5 * nq / 12 + u ≤ N := by linarith only [hu_eq, h12k]
        have h17_ge : 17 * (5 * nq / 12 + u) * u - 36 * FN ≤ 17 * N * u - 36 * FN := by
          nlinarith only [hN_lo, hu_pos]
        have hexp : 17 * (5 * nq / 12 + u) * u - 36 * FN =
            931 * nq ^ 2 / 1500 + 2761 * nq * t / 300 + 25 * t ^ 2 / 2 := by
          have hu_t : u = nq / 5 + t := by dsimp only [t]; ring
          dsimp only [FN]; rw [hu_t]; ring
        have hpos : 0 < 931 * nq ^ 2 / 1500 + 2761 * nq * t / 300 + 25 * t ^ 2 / 2 := by
          nlinarith only [hnq_ge6, ht0]
        linarith only [h17_lt, h17_ge, hexp, hpos]
      have hgF_neg : gF + s ^ 2 / 4 < 0 := by
        have hs2 : s ^ 2 / 4 ≤ u ^ 2 / 256 := by nlinarith only [hs0, hs_le]
        have hdiff_ge : nq / 5 < 2 * nq / 5 - u := by linarith only [hu_lt_fifth]
        have hsq_gt : (nq / 5) ^ 2 < (u - 2 * nq / 5) ^ 2 := by
          have h5 : 0 < nq / 5 := by linarith only [hnq_ge6]
          nlinarith only [h5, hdiff_ge]
        have hdF_gt : 17 * u / 18 < dbarF := by linarith only [hdbar_gt, hdbar_le_F]
        have hfrac_gt : 17 * u / (18 * 32 * nq) < dbarF / (32 * N) := by
          have h1 : 17 * u / (18 * 32 * nq) ≤ 17 * u / (18 * 32 * N) := by
            have hnum : 0 ≤ 17 * u := by linarith only [hu_pos]
            exact div_le_div_of_nonneg_left hnum (by linarith only [hN_pos]) (by linarith only [hN_le_n])
          have h2 : 17 * u / (18 * 32 * N) < dbarF / (32 * N) := by
            have hL : 17 * u / (18 * 32 * N) = (17 * u / 18) / (32 * N) := by ring
            rw [hL]; exact div_lt_div_of_pos_right hdF_gt (by linarith only [hN_pos])
          linarith only [h1, h2]
        have hprod : (17 * u / (18 * 32 * nq)) * (nq / 5) ^ 2 <
            (dbarF / (32 * N)) * (u - 2 * nq / 5) ^ 2 := by
          have hA : 0 < 17 * u / (18 * 32 * nq) := div_pos (by linarith only [hu_pos]) (by linarith only [hnq_ge6])
          have hB : 0 < (nq / 5) ^ 2 := sq_pos_of_pos (by linarith only [hnq_ge6])
          nlinarith only [hfrac_gt, hsq_gt, hA, hB]
        have hsimp : (17 * u / (18 * 32 * nq)) * (nq / 5) ^ 2 = 17 * nq * u / 14400 := by
          field_simp [show nq ≠ 0 by linarith only [hnq_ge6]]; ring
        have hcomp : u ^ 2 / 256 < 17 * nq * u / 14400 := by
          have h1 : 5 * u < nq := by linarith only [hu_lt_fifth]
          nlinarith only [h1, hu_pos]
        linarith only [hgF_le, hs2, hprod, hsimp, hcomp]
      have hquad : p2 * x - x ^ 2 - lam * (x - dbar) =
          (p2 * u - u ^ 2 - lam * (u - dbar)) + s ^ 2 / 4 - (x - u - s / 2) ^ 2 := by
        rw [hh_eq]; ring
      have hsq0 : 0 ≤ (x - u - s / 2) ^ 2 := sq_nonneg _
      linarith only [hquad, hhu_le, hgF_neg, hsq0]

/-- Pure rational algebra core for Theorem I's inductive step:
    given n >= 6, k = n/2, k < N <= n, u = N - k, M <= F(N), and finite vertex degrees d_v, S_v
    satisfying the two neighborhood-deletion bounds, derive False! -/
lemma quadratic_potential_step_contra
    {W : Type} [DecidableEq W] (S : Finset W)
    {n k M : ℕ} (hn6 : 6 ≤ n) (hk_lo : 2 * k ≤ n) (hk_hi : n ≤ 2 * k + 1)
    (hN_gt : k < #S) (hN_le : #S ≤ n)
    (hM_gt : n ^ 2 < 50 * M)
    (hM_le : (M : ℚ) ≤ (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((#S - k : ℕ) : ℚ) / 25 + (((#S - k : ℕ) : ℚ) ^ 2) / 8)
    (d Sv : W → ℕ)
    (hsum_d : ∑ v ∈ S, d v = 2 * M)
    (hsum_Sv : ∑ v ∈ S, Sv v = ∑ v ∈ S, (d v) ^ 2)
    (hd0 : ∀ v ∈ S, d v = 0 → Sv v = 0)
    (hb1 : ∀ v ∈ S, 1 ≤ d v → d v ≤ #S - k →
      ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
        ((M : ℚ) - ((n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((#S - k : ℕ) : ℚ) / 25 + (((#S - k : ℕ) : ℚ) ^ 2) / 8)) +
        (2 * (n : ℚ) / 25 + ((#S - k : ℕ) : ℚ) / 4) * (d v : ℚ) - 9 * ((d v : ℚ) ^ 2) / 8)
    (hb2 : ∀ v ∈ S, #S - k < d v →
      ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
        (((M : ℚ) - (n : ℚ) ^ 2 / 50) / ((#S - k : ℕ) : ℚ)) * (d v : ℚ) - (d v : ℚ) ^ 2) :
    False := by
  set N : ℚ := (#S : ℚ)
  set nq : ℚ := (n : ℚ)
  set kq : ℚ := (k : ℚ)
  set u : ℚ := ((#S - k : ℕ) : ℚ)
  set Mq : ℚ := (M : ℚ)
  have hu_eq : u = N - kq := by
    have h : (#S - k : ℕ) + k = #S := Nat.sub_add_cancel (by omega)
    have hz : ((#S - k : ℕ) : ℚ) + (k : ℚ) = (#S : ℚ) := by exact_mod_cast h
    linarith
  have hu_pos : (0 : ℚ) < u := by
    dsimp only [u]; exact Nat.cast_pos.mpr (by omega)
  have hN_pos : (0 : ℚ) < N := by
    dsimp only [N]; exact Nat.cast_pos.mpr (by omega)
  have hnq_ge6 : (6 : ℚ) ≤ nq := by dsimp only [nq]; exact_mod_cast hn6
  have hkq_lo : 2 * kq ≤ nq := by dsimp only [kq, nq]; exact_mod_cast hk_lo
  have hkq_hi : nq ≤ 2 * kq + 1 := by dsimp only [kq, nq]; exact_mod_cast hk_hi
  have hN_le_n : N ≤ nq := by dsimp only [N, nq]; exact_mod_cast hN_le
  have hM_gt_q : nq ^ 2 / 50 < Mq := by
    have h1 : nq ^ 2 < 50 * Mq := by dsimp only [nq, Mq]; exact_mod_cast hM_gt
    linarith
  have hM_pos : (0 : ℚ) < Mq := by nlinarith only [hM_gt_q, hnq_ge6]
  set FN : ℚ := nq ^ 2 / 50 + 2 * nq * u / 25 + u ^ 2 / 8
  have hMF : Mq ≤ FN := hM_le
  set dbar : ℚ := 2 * Mq / N
  set p1 : ℚ := 2 * nq / 25 + u / 4
  set p2 : ℚ := (Mq - nq ^ 2 / 50) / u
  have hdbar_pos : 0 < dbar := div_pos (by linarith) hN_pos
  have hp1_pos : 0 < p1 := by dsimp only [p1]; linarith
  have hp2_pos : 0 < p2 := div_pos (by linarith) hu_pos
  let P1 : ℚ → ℚ := fun x => (Mq - FN) + p1 * x - 9 * x ^ 2 / 8
  let P2 : ℚ → ℚ := fun x => p2 * x - x ^ 2
  have hP12_u : P1 u = P2 u := by
    dsimp only [P1, P2, FN, p1, p2]
    field_simp [hu_pos.ne']
    ring
  -- Step 3: Core lemma p2 < dbar with quantitative slack
  have hslack_lt : u < kq → 7 * u / 400 ≤ dbar - p2 := by
    intro huk
    have hNu : N * u * (dbar - p2) = N * (nq ^ 2 / 50) - (kq - u) * Mq := by
      dsimp only [dbar, p2]
      have hNku : N = kq + u := by linarith
      field_simp [hN_pos.ne', hu_pos.ne']
      rw [hNku]; ring
    have hgeF : N * (nq ^ 2 / 50) - (kq - u) * FN ≤ N * (nq ^ 2 / 50) - (kq - u) * Mq := by
      have : 0 ≤ kq - u := by linarith
      nlinarith only [this, hMF]
    have hexp : N * (nq ^ 2 / 50) - (kq - u) * FN =
        u * (nq * (nq - 2 * kq) / 25 + u * (nq - 2 * kq) / 16 + 7 * nq * u / 400 + u ^ 2 / 8) := by
      have hNku : N = kq + u := by linarith
      dsimp only [FN]; rw [hNku]; ring
    have hpos_inner : 7 * nq * u / 400 ≤
        nq * (nq - 2 * kq) / 25 + u * (nq - 2 * kq) / 16 + 7 * nq * u / 400 + u ^ 2 / 8 := by
      have h1 : 0 ≤ nq * (nq - 2 * kq) / 25 := by nlinarith only [hnq_ge6, hkq_lo]
      have h2 : 0 ≤ u * (nq - 2 * kq) / 16 := by nlinarith only [hu_pos, hkq_lo]
      have h3 : 0 ≤ u ^ 2 / 8 := by positivity
      linarith
    have hNu_ge : 7 * nq * u ^ 2 / 400 ≤ N * u * (dbar - p2) := by
      have hmul := mul_le_mul_of_nonneg_left hpos_inner hu_pos.le
      nlinarith only [hNu, hgeF, hexp, hmul]
    have hNu_ge2 : 7 * N * u ^ 2 / 400 ≤ N * u * (dbar - p2) := by
      have h1 : 7 * N * u ^ 2 / 400 ≤ 7 * nq * u ^ 2 / 400 := by
        have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
        nlinarith only [hN_le_n, hu2]
      linarith
    have hNu_pos : 0 < N * u := mul_pos hN_pos hu_pos
    have hfin : (N * u) * (7 * u / 400) ≤ (N * u) * (dbar - p2) := by linarith
    exact le_of_mul_le_mul_left hfin hNu_pos
  have hslack_ge : kq ≤ u → nq ^ 2 / (50 * u) ≤ dbar - p2 := by
    intro hku
    have hNu : N * u * (dbar - p2) = N * (nq ^ 2 / 50) + (u - kq) * Mq := by
      dsimp only [dbar, p2]
      have hNku : N = kq + u := by linarith
      field_simp [hN_pos.ne', hu_pos.ne']
      rw [hNku]; ring
    have hge : N * (nq ^ 2 / 50) ≤ N * u * (dbar - p2) := by
      have : 0 ≤ (u - kq) * Mq := mul_nonneg (by linarith) hM_pos.le
      linarith
    have hNu_pos : 0 < N * u := mul_pos hN_pos hu_pos
    have hL : (N * u) * (nq ^ 2 / (50 * u)) = N * (nq ^ 2 / 50) := by
      field_simp [hu_pos.ne']
    have hfin : (N * u) * (nq ^ 2 / (50 * u)) ≤ (N * u) * (dbar - p2) := by linarith
    exact le_of_mul_le_mul_left hfin hNu_pos
  have hp2_lt_dbar : p2 < dbar := by
    by_cases huk : u < kq
    · have := hslack_lt huk; linarith
    · push Not at huk
      have h1 := hslack_ge huk
      have hpos : 0 < nq ^ 2 / (50 * u) := div_pos (by nlinarith only [hnq_ge6]) (by linarith)
      linarith
  -- Step 4: Existence of a linear separator lam <= 0
  have hsep : ∃ lam : ℚ, lam ≤ 0 ∧
      (∀ x : ℚ, 0 ≤ x → x ≤ u → P1 x ≤ lam * (x - dbar)) ∧
      (∀ x : ℚ, u ≤ x → P2 x ≤ lam * (x - dbar)) := by
    by_cases hdu : u < dbar
    · -- Case A: dbar > u, set lam = p2 - 2 * dbar
      refine ⟨p2 - 2 * dbar, by linarith, ?_, ?_⟩
      · intro x hx0 hxu
        have hP12 : P1 x - P2 x = (u - x) * (x / 8 - (FN - Mq) / u) := by
          dsimp only [P1, P2, FN, p1, p2]
          field_simp [hu_pos.ne']; ring
        have hP12_le : P1 x - P2 x ≤ x * (u - x) / 8 := by
          have h1 : 0 ≤ (u - x) * ((FN - Mq) / u) :=
            mul_nonneg (by linarith) (div_nonneg (by linarith) hu_pos.le)
          nlinarith only [hP12, h1]
        have hP2_eq : P2 x - (p2 - 2 * dbar) * (x - dbar) = -(x - dbar) ^ 2 + dbar * (p2 - dbar) := by
          dsimp only [P2]; ring
        have hsq : -(x - dbar) ^ 2 + x * (u - x) / 8 =
            -9 / 8 * (x - (u + 16 * dbar) / 18) ^ 2 + (u ^ 2 - 32 * dbar * (dbar - u)) / 288 := by ring
        have hsq_le : -(x - dbar) ^ 2 + x * (u - x) / 8 ≤ u ^ 2 / 288 := by
          have h1 : 0 ≤ 9 / 8 * (x - (u + 16 * dbar) / 18) ^ 2 := by positivity
          have h2 : 0 ≤ 32 * dbar * (dbar - u) := by nlinarith only [hdbar_pos, hdu]
          linarith
        have hmain : u ^ 2 / 288 ≤ dbar * (dbar - p2) := by
          by_cases huk : u < kq
          · have h1 := hslack_lt huk
            have h2 : u * (7 * u / 400) ≤ dbar * (dbar - p2) := by
              nlinarith only [h1, hdu, hu_pos]
            nlinarith only [h2, hu_pos]
          · push Not at huk
            have h1 := hslack_ge huk
            have hpos_q : 0 ≤ nq ^ 2 / (50 * u) := div_nonneg (sq_nonneg nq) (by linarith)
            have h2 : u * (nq ^ 2 / (50 * u)) ≤ dbar * (dbar - p2) := by
              nlinarith only [h1, hdu, hu_pos, hpos_q]
            have h3 : u * (nq ^ 2 / (50 * u)) = nq ^ 2 / 50 := by field_simp [hu_pos.ne']
            have hu_lt_n : u < nq := by linarith [show 0 < kq by linarith]
            have h4 : u ^ 2 ≤ nq ^ 2 := by nlinarith only [hu_pos, hu_lt_n]
            have h5 : 0 ≤ nq ^ 2 := sq_nonneg nq
            linarith only [h2, h3, h4, h5]
        linarith
      · intro x _
        have hP2_eq : P2 x - (p2 - 2 * dbar) * (x - dbar) = -(x - dbar) ^ 2 + dbar * (p2 - dbar) := by
          dsimp only [P2]; ring
        have h1 : 0 ≤ (x - dbar) ^ 2 := sq_nonneg _
        have h2 : dbar * (p2 - dbar) ≤ 0 := by nlinarith only [hdbar_pos, hp2_lt_dbar]
        linarith
    · push Not at hdu
      -- Case B: dbar <= u
      by_cases hB1 : 9 * dbar / 4 ≤ p1
      · -- Subcase B1: p1 >= 9/4 * dbar, set lam = 0
        refine ⟨0, le_refl 0, ?_, ?_⟩
        · intro x _ _
          have hM_bound : Mq ≤ 2 * N * p1 / 9 := by
            dsimp only [dbar] at hB1
            have h1 := mul_le_mul_of_nonneg_left hB1 hN_pos.le
            have hL : N * (9 * (2 * Mq / N) / 4) = 9 * Mq / 2 := by field_simp [hN_pos.ne']; ring
            linarith
          have hN_le_half : N ≤ nq / 2 + u := by linarith
          have hP1_sq : P1 x = -9 / 8 * (x - 4 * p1 / 9) ^ 2 + (Mq - FN) + 2 * p1 ^ 2 / 9 := by
            dsimp only [P1]; ring
          have hsq0 : 0 ≤ 9 / 8 * (x - 4 * p1 / 9) ^ 2 := by positivity
          have hcomp : 2 * p1 * (nq / 2 + u + p1) / 9 - FN =
              -(109 * nq ^ 2 / 11250 + 23 * nq * u / 900 + u ^ 2 / 18) := by
            dsimp only [p1, FN]; ring
          have hneg : 2 * p1 * (nq / 2 + u + p1) / 9 - FN ≤ 0 := by
            have : 0 ≤ 109 * nq ^ 2 / 11250 + 23 * nq * u / 900 + u ^ 2 / 18 := by positivity
            linarith
          have hstep : Mq - FN + 2 * p1 ^ 2 / 9 ≤ 2 * p1 * (nq / 2 + u + p1) / 9 - FN := by
            have : 2 * N * p1 / 9 ≤ 2 * (nq / 2 + u) * p1 / 9 := by nlinarith only [hN_le_half, hp1_pos]
            linarith
          linarith
        · intro x hux
          have h1 : P2 x = x * (p2 - x) := by dsimp only [P2]; ring
          have h2 : p2 - x ≤ 0 := by linarith
          have h3 : 0 ≤ x := by linarith
          nlinarith only [h1, h2, h3]
      · -- Subcase B2: p1 < 9/4 * dbar, invoke standalone pure-ℚ helper
        push Not at hB1
        exact quadratic_potential_sep_B2 hnq_ge6 hkq_lo hkq_hi hu_eq hu_pos hN_pos hN_le_n hMF hdu hB1
  -- Sum S_v - d_v^2 <= lam * (d_v - dbar) over v ∈ S (strict at some v0 with d v0 >= 1)!
  obtain ⟨lam, hlam0, hP1_le, hP2_le⟩ := hsep
  have hex_pos : ∃ v0 ∈ S, 1 ≤ d v0 := by
    by_contra hall0
    push Not at hall0
    have hzero : ∑ v ∈ S, d v = 0 := Finset.sum_eq_zero (fun v hv => by have := hall0 v hv; omega)
    have hM0 : M = 0 := by omega
    rw [hM0] at hM_gt; omega
  obtain ⟨v0, hv0S, hv0_pos⟩ := hex_pos
  have hle_all : ∀ v ∈ S, ((Sv v : ℚ) - (d v : ℚ) ^ 2) ≤ lam * ((d v : ℚ) - dbar) := by
    intro v hv
    by_cases hdv0 : d v = 0
    · rw [hd0 v hv hdv0, hdv0]; simp
      exact mul_nonpos_of_nonpos_of_nonneg hlam0 hdbar_pos.le
    · by_cases hdv_u : d v ≤ #S - k
      · have h1 := hb1 v hv (by omega) hdv_u
        have h2 := hP1_le (d v : ℚ) (Nat.cast_nonneg _) (by dsimp only [u]; exact_mod_cast hdv_u)
        dsimp only [P1] at h2; linarith
      · have h1 := hb2 v hv (by omega)
        have h2 := hP2_le (d v : ℚ) (by dsimp only [u]; exact_mod_cast (show #S - k ≤ d v by omega))
        dsimp only [P2] at h2; linarith
  have hlt_v0 : ((Sv v0 : ℚ) - (d v0 : ℚ) ^ 2) < lam * ((d v0 : ℚ) - dbar) := by
    by_cases hdv_u : d v0 ≤ #S - k
    · have h1 := hb1 v0 hv0S hv0_pos hdv_u
      have h2 := hP1_le (d v0 : ℚ) (Nat.cast_nonneg _) (by dsimp only [u]; exact_mod_cast hdv_u)
      dsimp only [P1] at h2; linarith
    · have h1 := hb2 v0 hv0S (by omega)
      have h2 := hP2_le (d v0 : ℚ) (by dsimp only [u]; exact_mod_cast (show #S - k ≤ d v0 by omega))
      dsimp only [P2] at h2; linarith
  have hsum_lt : ∑ v ∈ S, ((Sv v : ℚ) - (d v : ℚ) ^ 2) < ∑ v ∈ S, lam * ((d v : ℚ) - dbar) :=
    Finset.sum_lt_sum hle_all ⟨v0, hv0S, hlt_v0⟩
  have hLHS0 : ∑ v ∈ S, ((Sv v : ℚ) - (d v : ℚ) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ v ∈ S, (Sv v : ℚ)) = ((∑ v ∈ S, Sv v : ℕ) : ℚ) := by simp
    have h2 : (∑ v ∈ S, (d v : ℚ) ^ 2) = ((∑ v ∈ S, (d v) ^ 2 : ℕ) : ℚ) := by simp
    rw [h1, h2, hsum_Sv]; ring
  have hRHS0 : ∑ v ∈ S, lam * ((d v : ℚ) - dbar) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1 : (∑ v ∈ S, (d v : ℚ)) = ((∑ v ∈ S, d v : ℕ) : ℚ) := by simp
    rw [h1, hsum_d]
    have h2 : ((2 * M : ℕ) : ℚ) = 2 * Mq := by push_cast; rfl
    have h3 : ((#S : ℕ) : ℚ) = N := rfl
    rw [h2, h3]; dsimp only [dbar]; field_simp [hN_pos.ne']; ring
  linarith

/-- Theorem I (`800 * e(G) > 73 * n^2`, hence `11 * e(G) > n^2`):
    Every triangle-free counterexample to Erdős #128 satisfies 800 * e(G) > 73 * n^2
    (all finite n, elementary quadratic-potential induction). -/
theorem eight_hundred_mul_edges_gt {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard := by
  classical
  set n := Fintype.card V
  set k := n / 2
  have hn6 : 6 ≤ n := six_le_card G hTF hH
  have hk_lo : 2 * k ≤ n := by omega
  have hk_hi : n ≤ 2 * k + 1 := by omega
  -- Strong induction on N ∈ [k, n]
  have hind : ∀ N : ℕ, k ≤ N → N ≤ n →
      ∀ S : Finset V, #S = N →
        (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((N - k : ℕ) : ℚ) / 25 + (((N - k : ℕ) : ℚ) ^ 2) / 8 <
          ((G.induce (S : Set V)).edgeSet.ncard : ℚ) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hNk hNn S hSN
      by_cases hbase : N = k
      · subst hbase
        have h50 : 50 * (G.induce (S : Set V)).edgeSet.ncard > n ^ 2 := by
          apply hH (S : Set V)
          rw [Set.ncard_coe_finset, hSN]; omega
        have h50q : (n : ℚ) ^ 2 < 50 * ((G.induce (S : Set V)).edgeSet.ncard : ℚ) := by
          exact_mod_cast h50
        simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_div, add_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        linarith
      · have hN_gt : k < N := by omega
        by_contra hle
        push Not at hle
        set M := (G.induce (S : Set V)).edgeSet.ncard
        -- M > n^2 / 50 since S contains a k-subset
        have hM_gt : n ^ 2 < 50 * M := by
          obtain ⟨S₀, hS₀S, hS₀k⟩ := Finset.exists_subset_card_eq (by omega : k ≤ #S)
          have h50 := hH (S₀ : Set V) (by rw [Set.ncard_coe_finset, hS₀k]; omega)
          have hmono : (G.induce (S₀ : Set V)).edgeSet.ncard ≤ M := by
            have h1 := two_mul_induce_edgeSet_ncard G S₀
            have h2 := two_mul_induce_edgeSet_ncard G S
            have hle2 : ∑ u ∈ S₀, #(S₀.filter (G.Adj u)) ≤ ∑ u ∈ S, #(S.filter (G.Adj u)) :=
              (Finset.sum_le_sum (fun u _ => Finset.card_le_card (Finset.filter_subset_filter _ hS₀S))).trans
                (Finset.sum_le_sum_of_subset hS₀S)
            omega
          omega
        let d : V → ℕ := fun v => #(S.filter (G.Adj v))
        let Sv : V → ℕ := fun v => ∑ w ∈ S.filter (G.Adj v), d w
        have hsum_d : ∑ v ∈ S, d v = 2 * M := (two_mul_induce_edgeSet_ncard G S).symm
        have hsum_Sv : ∑ v ∈ S, Sv v = ∑ v ∈ S, (d v) ^ 2 := by
          calc ∑ v ∈ S, ∑ w ∈ S.filter (G.Adj v), d w
              = ∑ v ∈ S, ∑ w ∈ S, if G.Adj v w then d w else 0 := by
                apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_filter]
            _ = ∑ w ∈ S, ∑ v ∈ S, if G.Adj v w then d w else 0 := Finset.sum_comm
            _ = ∑ w ∈ S, ∑ v ∈ S, if G.Adj w v then d w else 0 := by
                apply Finset.sum_congr rfl; intro w _
                apply Finset.sum_congr rfl; intro v _; simp [G.adj_comm]
            _ = ∑ w ∈ S, ∑ _v ∈ S.filter (G.Adj w), d w := by
                apply Finset.sum_congr rfl; intro w _; rw [← Finset.sum_filter]
            _ = ∑ w ∈ S, (d w) ^ 2 := by
                apply Finset.sum_congr rfl; intro w _; rw [Finset.sum_const, smul_eq_mul]; ring
        have hd0 : ∀ v ∈ S, d v = 0 → Sv v = 0 := by
          intro v _ hdv
          dsimp only [Sv]
          rw [Finset.card_eq_zero.mp hdv, Finset.sum_empty]
        have hNv_indep : ∀ v ∈ S, ∀ x ∈ S.filter (G.Adj v), ∀ y ∈ S.filter (G.Adj v), ¬ G.Adj x y := by
          intro v _ x hx y hy hxy
          exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2 hxy (Finset.mem_filter.mp hy).2
        have hb1 : ∀ v ∈ S, 1 ≤ d v → d v ≤ #S - k →
            ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
              ((M : ℚ) - ((n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((#S - k : ℕ) : ℚ) / 25 + (((#S - k : ℕ) : ℚ) ^ 2) / 8)) +
              (2 * (n : ℚ) / 25 + ((#S - k : ℕ) : ℚ) / 4) * (d v : ℚ) - 9 * ((d v : ℚ) ^ 2) / 8 := by
          intro v hv hdv1 hdv_u
          let J := S.filter (G.Adj v)
          have hJS : J ⊆ S := Finset.filter_subset _ _
          have hcard_sdiff : #(S \ J) = N - d v := by
            rw [Finset.card_sdiff_of_subset hJS, hSN]
          have hih := ih (N - d v) (by omega) (by omega) (by omega) (S \ J) hcard_sdiff
          have hedge := induce_edgeSet_ncard_sdiff_indep G hJS (hNv_indep v hv)
          have hedge_q : ((G.induce ((S \ J : Finset V) : Set V)).edgeSet.ncard : ℚ) + (Sv v : ℚ) = (M : ℚ) := by
            exact_mod_cast hedge
          have hsub_eq : ((N - d v - k : ℕ) : ℚ) = ((#S - k : ℕ) : ℚ) - (d v : ℚ) := by
            have hnat : (N - d v - k) + d v = #S - k := by omega
            have hq : ((N - d v - k : ℕ) : ℚ) + (d v : ℚ) = ((#S - k : ℕ) : ℚ) := by exact_mod_cast hnat
            linarith
          rw [hsub_eq] at hih
          linarith
        have hb2 : ∀ v ∈ S, #S - k < d v →
            ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
              (((M : ℚ) - (n : ℚ) ^ 2 / 50) / ((#S - k : ℕ) : ℚ)) * (d v : ℚ) - (d v : ℚ) ^ 2 := by
          intro v hv hdv_gt
          let Nv := S.filter (G.Adj v)
          set uN := #S - k
          have huN1 : 1 ≤ uN := by omega
          have huN_le : uN ≤ #Nv := by change #S - k ≤ d v; omega
          -- Every uN-subset J ⊆ Nv satisfies n^2 + 50 * ∑_{w ∈ J} d w < 50 * M
          have hperJ : ∀ J ∈ Nv.powersetCard uN, n ^ 2 + 50 * ∑ w ∈ J, d w < 50 * M := by
            intro J hJ
            have hJsub : J ⊆ Nv := (Finset.mem_powersetCard.mp hJ).1
            have hJcard : #J = uN := (Finset.mem_powersetCard.mp hJ).2
            have hJS : J ⊆ S := hJsub.trans (Finset.filter_subset _ _)
            have hJindep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y :=
              fun x hx y hy => hNv_indep v hv x (hJsub hx) y (hJsub hy)
            have hcard_k : #(S \ J) = k := by
              rw [Finset.card_sdiff_of_subset hJS, hJcard]; omega
            have h50 := hH ((S \ J : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard_k]; omega)
            have hedge := induce_edgeSet_ncard_sdiff_indep G hJS hJindep
            change (G.induce ((S \ J : Finset V) : Set V)).edgeSet.ncard + ∑ w ∈ J, d w = M at hedge
            omega
          have hne_pow : (Nv.powersetCard uN).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            have h0 : (#Nv).choose uN = 0 := by rw [← Finset.card_powersetCard, hemp, Finset.card_empty]
            have hpos := Nat.choose_pos huN_le
            omega
          have hsum_lt := Finset.sum_lt_sum_of_nonempty hne_pow hperJ
          have hsum_J : ∑ J ∈ Nv.powersetCard uN, ∑ w ∈ J, d w = (#Nv - 1).choose (uN - 1) * Sv v := by
            calc ∑ J ∈ Nv.powersetCard uN, ∑ w ∈ J, d w
                = ∑ J ∈ Nv.powersetCard uN, ∑ w ∈ Nv, if w ∈ J then d w else 0 := by
                  apply Finset.sum_congr rfl; intro J hJ
                  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                    Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hJ).1]
              _ = ∑ w ∈ Nv, ∑ J ∈ Nv.powersetCard uN, if w ∈ J then d w else 0 := Finset.sum_comm
              _ = ∑ w ∈ Nv, #((Nv.powersetCard uN).filter (w ∈ ·)) * d w := by
                  apply Finset.sum_congr rfl; intro w _
                  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
              _ = ∑ w ∈ Nv, (#Nv - 1).choose (uN - 1) * d w := by
                  apply Finset.sum_congr rfl; intro w hw; rw [card_powersetCard_mem Nv hw huN1]
              _ = (#Nv - 1).choose (uN - 1) * Sv v := (Finset.mul_sum _ _ _).symm
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_J, Finset.sum_const, Finset.sum_const,
            Finset.card_powersetCard, smul_eq_mul, smul_eq_mul] at hsum_lt
          have hchoose : (#Nv).choose uN * uN = #Nv * (#Nv - 1).choose (uN - 1) := by
            have := Nat.add_one_mul_choose_eq (#Nv - 1) (uN - 1)
            rw [show #Nv - 1 + 1 = #Nv by omega, show uN - 1 + 1 = uN by omega] at this
            linarith
          have hpos_ch : 0 < (#Nv).choose uN := Nat.choose_pos huN_le
          have hmul_lt := Nat.mul_lt_mul_of_pos_left hsum_lt (by omega : 0 < #Nv)
          have hnat_lt : (#Nv).choose uN * (uN * (50 * Sv v) + #Nv * n ^ 2) <
              (#Nv).choose uN * (#Nv * (50 * M)) := by
            have hL : #Nv * ((#Nv).choose uN * n ^ 2 + 50 * ((#Nv - 1).choose (uN - 1) * Sv v)) =
                (#Nv).choose uN * (uN * (50 * Sv v) + #Nv * n ^ 2) := by
              calc #Nv * ((#Nv).choose uN * n ^ 2 + 50 * ((#Nv - 1).choose (uN - 1) * Sv v))
                  = (#Nv).choose uN * (#Nv * n ^ 2) + (#Nv * (#Nv - 1).choose (uN - 1)) * (50 * Sv v) := by ring
                _ = (#Nv).choose uN * (#Nv * n ^ 2) + ((#Nv).choose uN * uN) * (50 * Sv v) := by rw [← hchoose]
                _ = (#Nv).choose uN * (uN * (50 * Sv v) + #Nv * n ^ 2) := by ring
            have hR : #Nv * ((#Nv).choose uN * (50 * M)) = (#Nv).choose uN * (#Nv * (50 * M)) := by ring
            omega
          have hclean : uN * (50 * Sv v) + d v * n ^ 2 < d v * (50 * M) :=
            Nat.lt_of_mul_lt_mul_left hnat_lt
          have hq : (uN : ℚ) * (50 * (Sv v : ℚ)) + (d v : ℚ) * (n : ℚ) ^ 2 < (d v : ℚ) * (50 * (M : ℚ)) := by
            exact_mod_cast hclean
          have huq_pos : (0 : ℚ) < (uN : ℚ) := by exact_mod_cast huN1
          have hSv_lt : (Sv v : ℚ) < (((M : ℚ) - (n : ℚ) ^ 2 / 50) / (uN : ℚ)) * (d v : ℚ) := by
            have h1 : (uN : ℚ) * (Sv v : ℚ) < (uN : ℚ) * ((((M : ℚ) - (n : ℚ) ^ 2 / 50) / (uN : ℚ)) * (d v : ℚ)) := by
              have hR : (uN : ℚ) * ((((M : ℚ) - (n : ℚ) ^ 2 / 50) / (uN : ℚ)) * (d v : ℚ)) =
                  ((M : ℚ) - (n : ℚ) ^ 2 / 50) * (d v : ℚ) := by field_simp [huq_pos.ne']
              linarith
            exact lt_of_mul_lt_mul_left h1 huq_pos.le
          linarith
        exact quadratic_potential_step_contra S hn6 hk_lo hk_hi (by omega) (by omega) hM_gt
          (by rw [hSN]; exact hle) d Sv hsum_d hsum_Sv hd0 hb1 hb2
  -- Step 5: Apply at N = n, S = Finset.univ!
  have hfull := hind n (by omega) (le_refl n) Finset.univ (by simp [n])
  have hedge_univ : (G.induce ((Finset.univ : Finset V) : Set V)).edgeSet.ncard = G.edgeSet.ncard := by
    have h1 := two_mul_induce_edgeSet_ncard G (Finset.univ : Finset V)
    have h2 : 2 * G.edgeSet.ncard = ∑ u : V, #((Finset.univ : Finset V).filter (G.Adj u)) := by
      have hcard : G.edgeSet.ncard = #G.edgeFinset := by rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl; intro u _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset]
      congr 1; ext v; simp
    omega
  rw [hedge_univ] at hfull
  have hu_ge_half : (n : ℚ) / 2 ≤ ((n - k : ℕ) : ℚ) := by
    have h1 : n ≤ 2 * (n - k) := by omega
    have h2 : (n : ℚ) ≤ 2 * ((n - k : ℕ) : ℚ) := by exact_mod_cast h1
    linarith
  have hF_ge : 73 * (n : ℚ) ^ 2 / 800 ≤
      (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((n - k : ℕ) : ℚ) / 25 + (((n - k : ℕ) : ℚ) ^ 2) / 8 := by
    have hnq : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    nlinarith only [hu_ge_half, hnq]
  have hq : 73 * (n : ℚ) ^ 2 < 800 * (G.edgeSet.ncard : ℚ) := by linarith
  exact_mod_cast hq


/-- Immediate corollary of `eight_hundred_mul_edges_gt`: 12 * e(G) > n^2. -/
theorem twelve_mul_edges_gt_sq {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    Fintype.card V ^ 2 < 12 * G.edgeSet.ncard := by
  have h := eight_hundred_mul_edges_gt G hTF hH
  omega

/-- Ramsey R(3, 3) = 6: every triangle-free graph on >= 6 vertices has an independent set of size 3. -/
lemma exists_indep_three_of_six_le {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) {A : Finset V} (hA : 6 ≤ #A) :
    ∃ J : Finset V, J ⊆ A ∧ #J = 3 ∧ ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < #A)
  let Nv := (A.erase v).filter (G.Adj v)
  let Mv := (A.erase v).filter (fun w => ¬ G.Adj v w)
  have hsum : #Nv + #Mv = #A - 1 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
  by_cases hN3 : 3 ≤ #Nv
  · obtain ⟨J, hJN, hJ3⟩ := Finset.exists_subset_card_eq hN3
    refine ⟨J, hJN.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)), hJ3, ?_⟩
    intro x hx y hy
    exact filter_adj_indep hTF (A.erase v) v x (hJN hx) y (hJN hy)
  · have hM3 : 3 ≤ #Mv := by omega
    obtain ⟨T, hTM, hT3⟩ := Finset.exists_subset_card_eq hM3
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT3
    have hnon : ¬ G.Adj a b ∨ ¬ G.Adj b c ∨ ¬ G.Adj a c := by
      by_contra hall
      push Not at hall
      exact not_adj_of_cliqueFree_three hTF hall.1 hall.2.1 hall.2.2
    have hv_not : ∀ x ∈ ({a, b, c} : Finset V), x ≠ v ∧ ¬ G.Adj v x := by
      intro x hx
      have hxM := Finset.mem_filter.mp (hTM hx)
      exact ⟨(Finset.mem_erase.mp hxM.1).1, hxM.2⟩
    have hpair_ext : ∀ p q : V, p ∈ ({a, b, c} : Finset V) → q ∈ ({a, b, c} : Finset V) →
        p ≠ q → ¬ G.Adj p q → ∃ J : Finset V, J ⊆ A ∧ #J = 3 ∧ ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := by
      intro p q hp hq hpq hnpq
      refine ⟨{v, p, q}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hv
        · exact Finset.erase_subset _ _ (Finset.mem_filter.mp (hTM hp)).1
        · exact Finset.erase_subset _ _ (Finset.mem_filter.mp (hTM hq)).1
      · have hvp := (hv_not p hp).1.symm
        have hvq := (hv_not q hq).1.symm
        rw [Finset.card_insert_of_notMem (by simp [hvp, hvq]), Finset.card_pair hpq]
      · intro x hx y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with hxe | hxe | hxe <;> rcases hy with hye | hye | hye <;> rw [hxe, hye]
        · exact G.loopless.irrefl _
        · exact (hv_not p hp).2
        · exact (hv_not q hq).2
        · exact fun h => (hv_not p hp).2 h.symm
        · exact G.loopless.irrefl _
        · exact hnpq
        · exact fun h => (hv_not q hq).2 h.symm
        · exact fun h => hnpq h.symm
        · exact G.loopless.irrefl _
    rcases hnon with h1 | h2 | h3
    · exact hpair_ext a b (by simp) (by simp) hab h1
    · exact hpair_ext b c (by simp) (by simp) hbc h2
    · exact hpair_ext a c (by simp) (by simp) hac h3

/-- Theorem B2: Every counterexample has at least 12 vertices. -/
theorem twelve_le_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    12 ≤ Fintype.card V := by
  classical
  have hn6 := six_le_card G hTF hH
  have hineq := neighborhood_avg_ineq G hTF hH
  by_contra hlt
  push Not at hlt
  -- Eliminate n = 6, 7, 9, 11 directly by negative discriminant in hineq,
  -- n = 10 by R(3, 4) = 9 + Theorem A (5*4 < 20 false), and n = 8 by R(3, 3) = 6!
  have hn_cases : Fintype.card V = 6 ∨ Fintype.card V = 7 ∨ Fintype.card V = 8 ∨
      Fintype.card V = 9 ∨ Fintype.card V = 10 ∨ Fintype.card V = 11 := by omega
  rcases hn_cases with hn | hn | hn | hn | hn | hn
  · simp only [hn] at hineq; norm_num at hineq; nlinarith [sq_nonneg ((G.edgeSet.ncard : ℤ) - 10)]
  · simp only [hn] at hineq; norm_num at hineq; nlinarith [sq_nonneg ((G.edgeSet.ncard : ℤ) - 10)]
  · -- n = 8: pick independent set I of size 3 via R(3, 3) = 6
    obtain ⟨I, -, hI3, hI⟩ := exists_indep_three_of_six_le G hTF (A := Finset.univ) (by simp [hn])
    have hdeg2 : ∀ v ∈ Finset.univ \ I, 2 ≤ #(I.filter (G.Adj v)) := by
      intro v hv
      have hvI : v ∉ I := (Finset.mem_sdiff.mp hv).2
      have hcard4 : #(insert v I) = 4 := by rw [Finset.card_insert_of_notMem hvI, hI3]
      have h50 := hH ((insert v I : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard4, hn]; omega)
      rw [hn] at h50
      have hedge : 2 * (G.induce ((insert v I : Finset V) : Set V)).edgeSet.ncard =
          2 * #(I.filter (G.Adj v)) := by
        rw [show insert v I = I ∪ {v} by ext x; simp, two_mul_induce_edgeSet_ncard,
          sum_adj_union_indep G (Finset.disjoint_singleton_right.mpr hvI) hI]
        simp
      omega
    have hcomp_indep : G.IsIndepSet ((Finset.univ \ I : Finset V) : Set V) := by
      intro u hu v hv _ huv
      have hu2 := hdeg2 u hu
      have hv2 := hdeg2 v hv
      have hdisj : Disjoint (I.filter (G.Adj u)) (I.filter (G.Adj v)) := by
        rw [Finset.disjoint_left]
        intro x hxu hxv
        exact not_adj_of_cliqueFree_three hTF huv (Finset.mem_filter.mp hxv).2 (Finset.mem_filter.mp hxu).2
      have hle : #(I.filter (G.Adj u)) + #(I.filter (G.Adj v)) ≤ #I := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      omega
    have h5 := five_mul_indep_lt_two_mul_card G hTF hH _ hcomp_indep
    rw [Set.ncard_coe_finset, Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, hn, hI3] at h5
    omega
  · simp only [hn] at hineq; norm_num at hineq; nlinarith [sq_nonneg ((G.edgeSet.ncard : ℤ) - 16)]
  · -- n = 10: R(3, 4) = 9 <= 10 gives independent set of size 4, contradicting 5 * 4 < 20!
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    have hdv : (G.neighborSet v).ncard ≤ 3 := by
      have h5 := five_mul_deg_lt_two_mul_card G hTF hH v
      omega
    let Mv := (Finset.univ.erase v).filter (fun w => ¬ G.Adj v w)
    have hMv_card : 6 ≤ #Mv := by
      have hNv_card : #((Finset.univ.erase v).filter (G.Adj v)) = (G.neighborSet v).ncard := by
        rw [Set.ncard_eq_toFinset_card']
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Set.mem_toFinset,
          SimpleGraph.mem_neighborSet]
        exact ⟨fun h => h.2, fun h => ⟨(G.ne_of_adj h).symm, h⟩⟩
      have hsum : #((Finset.univ.erase v).filter (G.Adj v)) + #Mv = #(Finset.univ.erase v) :=
        Finset.card_filter_add_card_filter_not _
      have herase : #(Finset.univ.erase v) = 9 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hn]
      omega
    obtain ⟨J, hJM, hJ3, hJ⟩ := exists_indep_three_of_six_le G hTF hMv_card
    have hvJ : v ∉ J := fun hv => (Finset.mem_erase.mp (Finset.mem_filter.mp (hJM hv)).1).1 rfl
    have hI4_indep : G.IsIndepSet ((insert v J : Finset V) : Set V) := by
      intro x hx y hy _ hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
      · exact G.loopless.irrefl _ hxy
      · exact (Finset.mem_filter.mp (hJM hy')).2 hxy
      · exact (Finset.mem_filter.mp (hJM hx')).2 hxy.symm
      · exact hJ x hx' y hy' hxy
    have h5 := five_mul_indep_lt_two_mul_card G hTF hH _ hI4_indep
    rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem hvJ, hJ3, hn] at h5
    omega
  · simp only [hn] at hineq; norm_num at hineq; nlinarith [sq_nonneg ((G.edgeSet.ncard : ℤ) - 21)]

/-- Shared helper: any non-bipartite triangle-free graph has a shortest odd induced cycle
    of length L >= 5. -/
lemma exists_shortest_odd_walk_of_nonbip {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (hnot2col : ¬ G.Colorable 2) :
    ∃ L : ℕ, Odd L ∧ 5 ≤ L ∧
      (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1))) ∧
      ∃ f : ℕ → V, f L = f 0 ∧ (∀ i < L, G.Adj (f i) (f (i + 1))) ∧
        (∀ i j, i < j → j < L → f i ≠ f j) ∧
        (∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ G.Adj (f i) (f j)) := by
  classical
  have hex_odd : ∃ L : ℕ, Odd L ∧ ∃ f : ℕ → V, f L = f 0 ∧ ∀ i < L, G.Adj (f i) (f (i + 1)) := by
    rw [SimpleGraph.two_colorable_iff_forall_loop_even] at hnot2col
    push Not at hnot2col
    obtain ⟨u, w, hneven⟩ := hnot2col
    refine ⟨w.length, Nat.not_even_iff_odd.mp hneven, fun i => w.getVert i, ?_, ?_⟩
    · simp
    · intro i hi
      exact w.adj_getVert_succ hi
  set L := Nat.find hex_odd with hL_def
  have hL_spec : Odd L ∧ ∃ f : ℕ → V, f L = f 0 ∧ ∀ i < L, G.Adj (f i) (f (i + 1)) :=
    Nat.find_spec hex_odd
  have hL_min : ∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1)) :=
    fun L' hlt hodd => fun h => Nat.find_min hex_odd hlt ⟨hodd, h⟩
  obtain ⟨hL_odd, f, hf_loop, hf_adj⟩ := hL_spec
  have hL5 : 5 ≤ L := by
    obtain ⟨k, hk⟩ := hL_odd
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h01 := hf_adj 0 (by omega)
      rw [show (0 + 1 : ℕ) = L by omega, hf_loop] at h01
      exact G.loopless.irrefl _ h01
    have hk1 : k ≠ 1 := by
      rintro rfl
      have h01 := hf_adj 0 (by omega)
      have h12 := hf_adj 1 (by omega)
      have h23 := hf_adj 2 (by omega)
      rw [show (2 + 1 : ℕ) = L by omega, hf_loop] at h23
      exact not_adj_of_cliqueFree_three hTF h01 h12 h23.symm
    omega
  have hf_inj : ∀ i j, i < j → j < L → f i ≠ f j := by
    intro i j hij hjL heq
    by_cases hodd1 : Odd (j - i)
    · apply hL_min (j - i) (by omega) hodd1
      refine ⟨fun t => f (i + t), ?_, ?_⟩
      · dsimp only; rw [show i + (j - i) = j by omega, add_zero, heq.symm]
      · intro t ht
        dsimp only
        rw [show i + (t + 1) = (i + t) + 1 by omega]
        exact hf_adj (i + t) (by omega)
    · have hodd2 : Odd (L - (j - i)) := by
        obtain ⟨a, ha⟩ := hL_odd
        obtain ⟨b, hb⟩ := Nat.not_odd_iff_even.mp hodd1
        exact ⟨a - b, by omega⟩
      apply hL_min (L - (j - i)) (by omega) hodd2
      refine ⟨fun t => if t ≤ L - j then f (j + t) else f (t - (L - j)), ?_, ?_⟩
      · dsimp only
        by_cases hi0 : i = 0
        · subst hi0
          rw [if_pos (by omega), if_pos (by omega), show j + (L - (j - 0)) = L by omega, add_zero, hf_loop, heq]
        · rw [if_neg (by omega), if_pos (by omega), show L - (j - i) - (L - j) = i by omega, add_zero, heq]
      · intro t ht
        dsimp only
        by_cases ht1 : t + 1 ≤ L - j
        · rw [if_pos (by omega), if_pos ht1, show j + (t + 1) = (j + t) + 1 by omega]
          exact hf_adj (j + t) (by omega)
        · by_cases ht0 : t ≤ L - j
          · have hteq : t = L - j := by omega
            subst hteq
            rw [if_pos (le_refl _), if_neg (by omega), show j + (L - j) = L by omega, hf_loop,
              show L - j + 1 - (L - j) = 1 by omega]
            exact hf_adj 0 (by omega)
          · rw [if_neg ht0, if_neg ht1, show t + 1 - (L - j) = (t - (L - j)) + 1 by omega]
            exact hf_adj (t - (L - j)) (by omega)
  have hf_nochord : ∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ G.Adj (f i) (f j) := by
    intro i j hij hjL hgap hadj
    by_cases heven1 : Even (j - i)
    · have hodd1 : Odd (j - i + 1) := by obtain ⟨b, hb⟩ := heven1; exact ⟨b, by omega⟩
      apply hL_min (j - i + 1) (by omega) hodd1
      refine ⟨fun t => if t ≤ j - i then f (i + t) else f i, ?_, ?_⟩
      · dsimp only
        rw [if_neg (by omega), if_pos (by omega), add_zero]
      · intro t ht
        dsimp only
        by_cases ht1 : t + 1 ≤ j - i
        · rw [if_pos (by omega), if_pos ht1, show i + (t + 1) = (i + t) + 1 by omega]
          exact hf_adj (i + t) (by omega)
        · have hteq : t = j - i := by omega
          subst hteq
          rw [if_pos (le_refl _), if_neg (by omega), show i + (j - i) = j by omega]
          exact hadj.symm
    · have heven2 : Even (L - (j - i)) := by
        obtain ⟨a, ha⟩ := hL_odd
        obtain ⟨b, hb⟩ := Nat.not_even_iff_odd.mp heven1
        exact ⟨a - b, by omega⟩
      have hodd2 : Odd (L - (j - i) + 1) := by obtain ⟨b, hb⟩ := heven2; exact ⟨b, by omega⟩
      apply hL_min (L - (j - i) + 1) (by omega) hodd2
      refine ⟨fun t => if t ≤ L - j then f (j + t) else if t ≤ L - (j - i) then f (t - (L - j)) else f j, ?_, ?_⟩
      · dsimp only
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), add_zero]
      · intro t ht
        dsimp only
        by_cases ht1 : t + 1 ≤ L - j
        · rw [if_pos (by omega), if_pos ht1, show j + (t + 1) = (j + t) + 1 by omega]
          exact hf_adj (j + t) (by omega)
        · by_cases ht0 : t ≤ L - j
          · have hteq : t = L - j := by omega
            subst hteq
            by_cases hi0 : i = 0
            · subst hi0
              rw [if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
                show j + (L - j) = L by omega, hf_loop]
              exact hadj
            · rw [if_pos (le_refl _), if_neg (by omega), if_pos (by omega),
                show j + (L - j) = L by omega, hf_loop, show L - j + 1 - (L - j) = 1 by omega]
              exact hf_adj 0 (by omega)
          · by_cases ht2 : t + 1 ≤ L - (j - i)
            · rw [if_neg ht0, if_pos (by omega), if_neg ht1, if_pos ht2,
                show t + 1 - (L - j) = (t - (L - j)) + 1 by omega]
              exact hf_adj (t - (L - j)) (by omega)
            · have hteq : t = L - (j - i) := by omega
              subst hteq
              rw [if_neg ht0, if_pos (le_refl _), if_neg ht1, if_neg (by omega),
                show L - (j - i) - (L - j) = i by omega]
              exact hadj
  exact ⟨L, hL_odd, hL5, hL_min, f, hf_loop, hf_adj, hf_inj, hf_nochord⟩

/-- Every counterexample is non-bipartite. -/
lemma not_colorable_two_of_counterexample {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ¬ G.Colorable 2 := by
  classical
  rintro ⟨col⟩
  let C0 : Set V := {v | col v = 0}
  let C1 : Set V := {v | col v = 1}
  have hC0 : G.IsIndepSet C0 := fun x hx y hy _ hxy => by
    have hne := col.valid hxy; exact hne (hx.trans hy.symm)
  have hC1 : G.IsIndepSet C1 := fun x hx y hy _ hxy => by
    have hne := col.valid hxy; exact hne (hx.trans hy.symm)
  have h50 := five_mul_indep_lt_two_mul_card G hTF hH C0 hC0
  have h51 := five_mul_indep_lt_two_mul_card G hTF hH C1 hC1
  have hsum : C0.ncard + C1.ncard = Fintype.card V := by
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    have hdisj : Disjoint C0.toFinset C1.toFinset := by
      rw [Finset.disjoint_left]
      intro v hv0 hv1
      have h0 : col v = 0 := by simpa [C0] using hv0
      have h1 : col v = 1 := by simpa [C1] using hv1
      have : (0 : Fin 2) = 1 := h0.symm.trans h1
      exact absurd this (by decide)
    rw [← Finset.card_union_of_disjoint hdisj]
    have hunion : C0.toFinset ∪ C1.toFinset = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Set.mem_toFinset, C0, C1, Finset.mem_univ, iff_true]
      change col v = 0 ∨ col v = 1
      cases hcv : col v with
      | mk val hlt =>
        have : val = 0 ∨ val = 1 := by omega
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    rw [hunion, Finset.card_univ]
  have hpos := six_le_card G hTF hH
  omega

/-- Shared helper: every counterexample has a shortest odd induced cycle of length L >= 5. -/
lemma exists_shortest_odd_walk {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ∃ L : ℕ, Odd L ∧ 5 ≤ L ∧
      (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1))) ∧
      ∃ f : ℕ → V, f L = f 0 ∧ (∀ i < L, G.Adj (f i) (f (i + 1))) ∧
        (∀ i j, i < j → j < L → f i ≠ f j) ∧
        (∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ G.Adj (f i) (f j)) :=
  exists_shortest_odd_walk_of_nonbip G hTF (not_colorable_two_of_counterexample G hTF hH)

/-- Theorem D (Razborov 2021 induced 2K_2-free theorem, 8-line elementary proof):
    Every counterexample contains an induced 2K_2. -/
theorem exists_induced_twoK2 {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ∃ a b c d : V, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
  classical
  by_contra hno2K2
  have h2K2 : ∀ a b c d : V, G.Adj a b → G.Adj c d →
      a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d := by
    intro a b c d hab hcd hac had hbc hbd
    by_contra hnone
    push Not at hnone
    exact hno2K2 ⟨a, b, c, d, hac, had, hbc, hbd, hab, hcd, hnone.1, hnone.2.1, hnone.2.2.1, hnone.2.2.2⟩
  obtain ⟨L, hL_odd, hL5, -, f, hf_loop, hf_adj, hf_inj, hf_nochord⟩ := exists_shortest_odd_walk G hTF hH
  -- Step 3: L = 5 (if L >= 7 then {f 0, f 1} and {f 3, f 4} form an induced 2K_2!)
  have hL_eq_5 : L = 5 := by
    by_contra hne5
    have hL7 : 7 ≤ L := by obtain ⟨k, hk⟩ := hL_odd; omega
    have h := h2K2 (f 0) (f 1) (f 3) (f 4)
      (hf_adj 0 (by omega)) (hf_adj 3 (by omega))
      (hf_inj 0 3 (by omega) (by omega)) (hf_inj 0 4 (by omega) (by omega))
      (hf_inj 1 3 (by omega) (by omega)) (hf_inj 1 4 (by omega) (by omega))
    rcases h with h03 | h04 | h13 | h14
    · exact hf_nochord 0 3 (by omega) (by omega) (by omega) h03
    · exact hf_nochord 0 4 (by omega) (by omega) (by omega) h04
    · exact hf_nochord 1 3 (by omega) (by omega) (by omega) h13
    · exact hf_nochord 1 4 (by omega) (by omega) (by omega) h14
  -- Step 4: We have an induced C_5 = (f 0, f 1, f 2, f 3, f 4)!
  have hc_adj : ∀ i : Fin 5, G.Adj (f i.val) (f ((i + 1 : Fin 5).val)) := by
    intro i
    fin_cases i
    · exact hf_adj 0 (by omega)
    · exact hf_adj 1 (by omega)
    · exact hf_adj 2 (by omega)
    · exact hf_adj 3 (by omega)
    · have h4 := hf_adj 4 (by omega)
      rw [show (4 + 1 : ℕ) = L by omega, hf_loop] at h4
      exact h4
  have hc_nadj : ∀ i : Fin 5, ¬ G.Adj (f i.val) (f ((i + 2 : Fin 5).val)) := by
    intro i
    fin_cases i
    · exact hf_nochord 0 2 (by omega) (by omega) (by omega)
    · exact hf_nochord 1 3 (by omega) (by omega) (by omega)
    · exact hf_nochord 2 4 (by omega) (by omega) (by omega)
    · intro h; exact hf_nochord 0 3 (by omega) (by omega) (by omega) h.symm
    · intro h; exact hf_nochord 1 4 (by omega) (by omega) (by omega) h.symm
  have hc_inj : ∀ i j : Fin 5, i ≠ j → f i.val ≠ f j.val := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact hf_inj i.val j.val hlt (by omega)
    · exact (hf_inj j.val i.val hgt (by omega)).symm
  -- Every vertex x either is isolated (degree 0) or has an exact pair {i-1, i+1} of neighbors on C_5!
  have hclass : ∀ x : V, (∀ y : V, ¬ G.Adj x y) ∨
      ∃ i : Fin 5, G.Adj x (f ((i + 4 : Fin 5).val)) ∧ G.Adj x (f ((i + 1 : Fin 5).val)) := by
    intro x
    by_cases hiso : ∀ y : V, ¬ G.Adj x y
    · exact Or.inl hiso
    · right
      push Not at hiso
      obtain ⟨y, hxy⟩ := hiso
      -- First show x has at least one neighbor on C_5
      have hx_some : ∃ j : Fin 5, G.Adj x (f j.val) := by
        by_contra hnone
        push Not at hnone
        -- y cannot cover all 5 edges of C_5 without forming a triangle
        have hex_edge : ∃ j : Fin 5, ¬ G.Adj y (f j.val) ∧ ¬ G.Adj y (f ((j + 1 : Fin 5).val)) := by
          by_contra hall
          push Not at hall
          have htri : ∀ j : Fin 5, ¬ (G.Adj y (f j.val) ∧ G.Adj y (f ((j + 1 : Fin 5).val))) :=
            fun j ⟨h1, h2⟩ => not_adj_of_cliqueFree_three hTF h1 (hc_adj j) h2
          by_cases hy0 : G.Adj y (f (0 : Fin 5).val)
          · have hy1 : ¬ G.Adj y (f (1 : Fin 5).val) := fun h => htri 0 ⟨hy0, h⟩
            have hy2 : G.Adj y (f (2 : Fin 5).val) := (hall 1) hy1
            have hy3 : ¬ G.Adj y (f (3 : Fin 5).val) := fun h => htri 2 ⟨hy2, h⟩
            have hy4 : G.Adj y (f (4 : Fin 5).val) := (hall 3) hy3
            exact htri 4 ⟨hy4, hy0⟩
          · have hy1 : G.Adj y (f (1 : Fin 5).val) := (hall 0) hy0
            have hy2 : ¬ G.Adj y (f (2 : Fin 5).val) := fun h => htri 1 ⟨hy1, h⟩
            have hy3 : G.Adj y (f (3 : Fin 5).val) := (hall 2) hy2
            have hy4 : ¬ G.Adj y (f (4 : Fin 5).val) := fun h => htri 3 ⟨hy3, h⟩
            exact (hall 4) hy4 |> hy0
        obtain ⟨j, hyj, hyj1⟩ := hex_edge
        have hxj : ¬ G.Adj x (f j.val) := hnone j
        have hxj1 : ¬ G.Adj x (f ((j + 1 : Fin 5).val)) := hnone (j + 1)
        have hne1 : x ≠ f j.val := fun h => hxj1 (h ▸ hc_adj j)
        have hne2 : x ≠ f ((j + 1 : Fin 5).val) := fun h => hxj (h ▸ (hc_adj j).symm)
        have hne3 : y ≠ f j.val := fun h => hxj (h ▸ hxy)
        have hne4 : y ≠ f ((j + 1 : Fin 5).val) := fun h => hxj1 (h ▸ hxy)
        rcases h2K2 x y (f j.val) (f ((j + 1 : Fin 5).val)) hxy (hc_adj j) hne1 hne2 hne3 hne4 with
          h | h | h | h
        · exact hxj h
        · exact hxj1 h
        · exact hyj h
        · exact hyj1 h
      obtain ⟨j, hxj⟩ := hx_some
      -- At least one of j+2 or j+3 MUST be adjacent to x (else {x, f j} and {f(j+2), f(j+3)} is induced 2K_2!)
      have hxj23 : G.Adj x (f ((j + 2 : Fin 5).val)) ∨ G.Adj x (f ((j + 3 : Fin 5).val)) := by
        by_contra hneither
        push Not at hneither
        have hne_xj2 : x ≠ f ((j + 2 : Fin 5).val) := fun h => hc_nadj j (h ▸ hxj.symm)
        have hne_xj3 : x ≠ f ((j + 3 : Fin 5).val) := fun h =>
          hc_nadj (j + 3) (by simpa [show j + 3 + 2 = j by fin_cases j <;> rfl] using h ▸ hxj)
        have hne_jj2 : f j.val ≠ f ((j + 2 : Fin 5).val) :=
          hc_inj j (j + 2) (by intro h; fin_cases j <;> simp at h)
        have hne_jj3 : f j.val ≠ f ((j + 3 : Fin 5).val) :=
          hc_inj j (j + 3) (by intro h; fin_cases j <;> simp at h)
        have hadj23 : G.Adj (f ((j + 2 : Fin 5).val)) (f ((j + 3 : Fin 5).val)) := by
          simpa [show j + 2 + 1 = j + 3 by fin_cases j <;> rfl] using hc_adj (j + 2)
        have hna_j2 : ¬ G.Adj (f j.val) (f ((j + 2 : Fin 5).val)) := hc_nadj j
        have hna_j3 : ¬ G.Adj (f j.val) (f ((j + 3 : Fin 5).val)) := fun h =>
          hc_nadj (j + 3) (by simpa [show j + 3 + 2 = j by fin_cases j <;> rfl] using h.symm)
        rcases h2K2 x (f j.val) (f ((j + 2 : Fin 5).val)) (f ((j + 3 : Fin 5).val))
            hxj hadj23 hne_xj2 hne_xj3 hne_jj2 hne_jj3 with h | h | h | h
        · exact hneither.1 h
        · exact hneither.2 h
        · exact hna_j2 h
        · exact hna_j3 h
      rcases hxj23 with hxj2 | hxj3
      · refine ⟨j + 1, ?_, ?_⟩
        · simpa [show j + 1 + 4 = j by fin_cases j <;> rfl] using hxj
        · simpa [show j + 1 + 1 = j + 2 by fin_cases j <;> rfl] using hxj2
      · refine ⟨j + 4, ?_, ?_⟩
        · simpa [show j + 4 + 4 = j + 3 by fin_cases j <;> rfl] using hxj3
        · simpa [show j + 4 + 1 = j by fin_cases j <;> rfl] using hxj
  -- Step 5: Assign each vertex a class c(x) : Fin 5, giving 5 independent sets A_i ∪ A_{i+2} summing to 2n!
  have hex_cls : ∀ x : V, ∃ i : Fin 5, (∀ y : V, ¬ G.Adj x y) ∨
      (G.Adj x (f ((i + 4 : Fin 5).val)) ∧ G.Adj x (f ((i + 1 : Fin 5).val))) := by
    intro x
    rcases hclass x with h | ⟨i, hi⟩
    · exact ⟨0, Or.inl h⟩
    · exact ⟨i, Or.inr hi⟩
  choose cls hcls using hex_cls
  have hpair_indep : ∀ i : Fin 5, G.IsIndepSet {x : V | cls x = i ∨ cls x = i + 2} := by
    intro i x hx y hy _ hxy
    change cls x = i ∨ cls x = i + 2 at hx
    change cls y = i ∨ cls y = i + 2 at hy
    rcases hcls x with hiso | ⟨hx4, hx1⟩
    · exact hiso y hxy
    rcases hcls y with hiso | ⟨hy4, hy1⟩
    · exact hiso x hxy.symm
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx] at hx1; rw [hy] at hy1
      exact not_adj_of_cliqueFree_three hTF hxy hy1 hx1
    · rw [hx] at hx1; rw [hy, show i + 2 + 4 = i + 1 by fin_cases i <;> rfl] at hy4
      exact not_adj_of_cliqueFree_three hTF hxy hy4 hx1
    · rw [hx, show i + 2 + 4 = i + 1 by fin_cases i <;> rfl] at hx4; rw [hy] at hy1
      exact not_adj_of_cliqueFree_three hTF hxy hy1 hx4
    · rw [hx] at hx1; rw [hy] at hy1
      exact not_adj_of_cliqueFree_three hTF hxy hy1 hx1
  have hlt_all : ∀ i : Fin 5, 5 * ({x : V | cls x = i ∨ cls x = i + 2}).ncard < 2 * Fintype.card V :=
    fun i => five_mul_indep_lt_two_mul_card G hTF hH _ (hpair_indep i)
  have hsum_lt : ∑ i : Fin 5, 5 * ({x : V | cls x = i ∨ cls x = i + 2}).ncard <
      ∑ _i : Fin 5, 2 * Fintype.card V := by
    apply Finset.sum_lt_sum_of_nonempty (by simp)
    intro i _
    exact hlt_all i
  have hsum_eq : ∑ i : Fin 5, ({x : V | cls x = i ∨ cls x = i + 2}).ncard = 2 * Fintype.card V := by
    have hcard : ∀ i : Fin 5, ({x : V | cls x = i ∨ cls x = i + 2}).ncard =
        #(Finset.univ.filter (fun x => cls x = i)) + #(Finset.univ.filter (fun x => cls x = i + 2)) := by
      intro i
      rw [Set.ncard_eq_toFinset_card']
      have hdisj : Disjoint (Finset.univ.filter (fun x => cls x = i))
          (Finset.univ.filter (fun x => cls x = i + 2)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h1 := (Finset.mem_filter.mp hx1).2
        have h2 := (Finset.mem_filter.mp hx2).2
        have heq : i = i + 2 := h1.symm.trans h2
        fin_cases i <;> simp at heq
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1
      ext x
      simp
    simp_rw [hcard, Finset.sum_add_distrib]
    have htot : ∑ i : Fin 5, #(Finset.univ.filter (fun x => cls x = i)) = Fintype.card V := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := cls) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have htot2 : ∑ i : Fin 5, #(Finset.univ.filter (fun x => cls x = i + 2)) = Fintype.card V := by
      rw [← htot]
      refine Fintype.sum_equiv (Equiv.addRight (2 : Fin 5)) _ _ (fun i => rfl)
    omega
  rw [← Finset.mul_sum, hsum_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_lt
  omega

/-- Finite arithmetic verification for Theorem C (12 <= n <= 34, < 1000 kernel checks). -/
lemma girth5_arith_kill :
    ∀ n ∈ Finset.Icc 12 34,
      ∀ m ∈ Finset.Icc (n ^ 2 / 12 + 1) (3 * n),
        ∀ a ∈ Finset.Icc 1 (2 * n / 5),
          n ^ 2 < 12 * m → 4 * m ^ 2 ≤ n ^ 2 * (n - 1) →
          5 * a < 2 * n → 4 * m ≤ n * (a + 2) → ¬ (n = 12 ∧ a = 4) →
          (n / 2 - a) * (n - 2 - a - (n / 2 - a)) * (a ^ 2 / 2) +
            (n / 2 - a) * (n / 2 - a - 1) * (m - a - 1) <
          (n ^ 2 / 50 + 1) * (n - 2 - a) * (n - 2 - a - 1) := by
  decide

/-- Helper for Theorem C: in a C_3,C_4-free graph, ∑_{u ∈ N(v)} deg u <= n - 1. -/
lemma girth5_sum_deg_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hnoC4 : ∀ a b c d : V, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False)
    (v : V) :
    ∑ u ∈ G.neighborFinset v, G.degree u ≤ Fintype.card V - 1 := by
  have hpw : ((G.neighborFinset v : Set V)).PairwiseDisjoint (fun u => (G.neighborFinset u).erase v) := by
    intro u₁ hu₁ u₂ hu₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw₁ hw₂
    have hw1' := Finset.mem_erase.mp hw₁
    have hw2' := Finset.mem_erase.mp hw₂
    exact hnoC4 v u₁ w u₂ hw1'.1.symm hne
      ((SimpleGraph.mem_neighborFinset G v u₁).mp hu₁)
      ((SimpleGraph.mem_neighborFinset G u₁ w).mp hw1'.2)
      ((SimpleGraph.mem_neighborFinset G u₂ w).mp hw2'.2).symm
      ((SimpleGraph.mem_neighborFinset G v u₂).mp hu₂).symm
  have hsub : (G.neighborFinset v).biUnion (fun u => (G.neighborFinset u).erase v) ⊆
      (Finset.univ.erase v) \ G.neighborFinset v := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hw
    have hwu' := Finset.mem_erase.mp hwu
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hwu'.1, Finset.mem_univ _⟩, ?_⟩
    intro hwN
    exact not_adj_of_cliqueFree_three hTF
      ((SimpleGraph.mem_neighborFinset G v u).mp hu)
      ((SimpleGraph.mem_neighborFinset G u w).mp hwu'.2)
      ((SimpleGraph.mem_neighborFinset G v w).mp hwN)
  have hcard_bi : #((G.neighborFinset v).biUnion (fun u => (G.neighborFinset u).erase v)) =
      ∑ u ∈ G.neighborFinset v, (G.degree u - 1) := by
    rw [Finset.card_biUnion hpw]
    apply Finset.sum_congr rfl
    intro u hu
    have hvu : v ∈ G.neighborFinset u :=
      (SimpleGraph.mem_neighborFinset G u v).mpr ((SimpleGraph.mem_neighborFinset G v u).mp hu).symm
    rw [Finset.card_erase_of_mem hvu]
    rfl
  have hsub_card : #((Finset.univ.erase v) \ G.neighborFinset v) = Fintype.card V - 1 - G.degree v := by
    have hNsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj ((SimpleGraph.mem_neighborFinset G v x).mp hx)).symm, Finset.mem_univ _⟩
    have h1 := Finset.card_sdiff_add_card_eq_card hNsub
    have h2 : #(Finset.univ.erase v) = Fintype.card V - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    have h3 : #(G.neighborFinset v) = G.degree v := rfl
    omega
  have hle1 : ∑ u ∈ G.neighborFinset v, (G.degree u - 1) ≤ Fintype.card V - 1 - G.degree v := by
    rw [← hcard_bi, ← hsub_card]
    exact Finset.card_le_card hsub
  have hsum_add : ∑ u ∈ G.neighborFinset v, G.degree u =
      (∑ u ∈ G.neighborFinset v, (G.degree u - 1)) + G.degree v := by
    have h1 : ∀ u ∈ G.neighborFinset v, G.degree u = (G.degree u - 1) + 1 := by
      intro u hu
      have hvu : v ∈ G.neighborFinset u :=
        (SimpleGraph.mem_neighborFinset G u v).mpr ((SimpleGraph.mem_neighborFinset G v u).mp hu).symm
      have hpos : 0 < G.degree u := Finset.card_pos.mpr ⟨v, hvu⟩
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rfl
  have hdv_le : G.degree v ≤ Fintype.card V - 1 := by
    have hNsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj ((SimpleGraph.mem_neighborFinset G v x).mp hx)).symm, Finset.mem_univ _⟩
    have hle := Finset.card_le_card hNsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at hle
    exact hle
  omega

set_option maxHeartbeats 600000 in
/-- Theorem C (Razborov 2021 girth >= 5 theorem, elementary all-finite-n proof):
    Every counterexample contains a 4-cycle C_4. -/
theorem exists_fourCycle {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ∃ a b c d : V, a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a := by
  classical
  by_contra hnoC4_raw
  have hnoC4 : ∀ a b c d : V, a ≠ c → b ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False :=
    fun a b c d hac hbd hab hbc hcd hda => hnoC4_raw ⟨a, b, c, d, hac, hbd, hab, hbc, hcd, hda⟩
  set n := Fintype.card V
  set k := n / 2
  set m := G.edgeSet.ncard
  have hn12 : 12 ≤ n := twelve_le_card G hTF hH
  have h12m : n ^ 2 < 12 * m := twelve_mul_edges_gt_sq G hTF hH
  have h5m : 5 * m < n ^ 2 := five_mul_edges_lt_sq G hTF hH
  have hm_pos : 0 < m := by nlinarith
  have hm_eq : 2 * m = ∑ v : V, G.degree v := by
    have h1 : m = #G.edgeFinset := by
      show G.edgeSet.ncard = #G.edgeFinset
      rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  -- Step 1: In a C_3,C_4-free graph, for every v, ∑ u ∈ N(v), deg u <= n - 1
  have hsum_deg_le : ∀ v : V, ∑ u ∈ G.neighborFinset v, G.degree u ≤ n - 1 :=
    fun v => girth5_sum_deg_le G hTF hnoC4 v
  -- Step 2: Sum over v to get ∑ d(x)^2 <= n*(n-1), 4*m^2 <= n^2*(n-1), and n <= 34!
  have hsum_deg_sq_eq : ∑ v : V, ∑ u ∈ G.neighborFinset v, G.degree u = ∑ x : V, G.degree x ^ 2 := by
    have h1 : ∀ v : V, ∑ u ∈ G.neighborFinset v, G.degree u =
        ∑ u : V, if G.Adj v u then G.degree u else 0 := by
      intro v; rw [← Finset.sum_filter]; congr 1; ext u; simp
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hf : #(Finset.univ.filter (fun v => G.Adj v x)) = G.degree x := by
      rw [SimpleGraph.degree]; congr 1; ext v; simp [G.adj_comm]
    rw [hf, sq]
  have hS2_le : ∑ x : V, G.degree x ^ 2 ≤ n * (n - 1) := by
    rw [← hsum_deg_sq_eq]
    calc ∑ v : V, ∑ u ∈ G.neighborFinset v, G.degree u
        ≤ ∑ _v : V, (n - 1) := Finset.sum_le_sum (fun v _ => hsum_deg_le v)
      _ = n * (n - 1) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hCS : 4 * m ^ 2 ≤ n * ∑ x : V, G.degree x ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := fun v => (G.degree v : ℤ))
    have hsum_d : ∑ v : V, (G.degree v : ℤ) = 2 * (m : ℤ) := by
      have : ((∑ v : V, G.degree v : ℕ) : ℤ) = ((2 * m : ℕ) : ℤ) := congrArg Nat.cast hm_eq.symm
      simpa using this
    rw [hsum_d, Finset.card_univ] at hcs
    have hcs' : ((4 * m ^ 2 : ℕ) : ℤ) ≤ ((n * ∑ x : V, G.degree x ^ 2 : ℕ) : ℤ) := by
      push_cast; linarith
    exact Nat.cast_le.mp hcs'
  have h4m2_le : 4 * m ^ 2 ≤ n ^ 2 * (n - 1) := by
    calc 4 * m ^ 2 ≤ n * ∑ x : V, G.degree x ^ 2 := hCS
      _ ≤ n * (n * (n - 1)) := Nat.mul_le_mul_left n hS2_le
      _ = n ^ 2 * (n - 1) := by ring
  have hn34 : n ≤ 34 := by
    have h1 : n ^ 2 * n ^ 2 < 36 * (4 * m ^ 2) := by
      have hsq : n ^ 2 * n ^ 2 < (12 * m) * (12 * m) := Nat.mul_lt_mul'' h12m h12m
      linarith
    have h2 : n ^ 2 * n ^ 2 < n ^ 2 * (36 * (n - 1)) := by
      have hmul := Nat.mul_le_mul_left 36 h4m2_le
      linarith
    have h3 : n ^ 2 < 36 * (n - 1) := Nat.lt_of_mul_lt_mul_left h2
    by_contra hgt
    have hge35 : 35 ≤ n := by omega
    have hcontra : 36 * (n - 1) ≤ n ^ 2 := by
      have : ∀ t : ℕ, 35 ≤ t → 36 * (t - 1) ≤ t ^ 2 := by
        intro t ht
        have : (36 : ℤ) * ((t : ℤ) - 1) ≤ (t : ℤ) ^ 2 := by nlinarith
        have hsub : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := Nat.cast_sub (by omega)
        have hcast : ((36 * (t - 1) : ℕ) : ℤ) ≤ ((t ^ 2 : ℕ) : ℤ) := by push_cast [hsub]; exact this
        exact Nat.cast_le.mp hcast
      exact this n hge35
    omega
  -- Step 3: Pick an ordered edge (u, v) maximizing deg(u) + deg(v)
  let Eord : Finset (V × V) := (Finset.univ ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)
  have hEord_card : #Eord = 2 * m := by
    have h1 : #Eord = ∑ x : V, G.degree x := by
      rw [Finset.card_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.card_filter, SimpleGraph.degree]
      congr 1; ext y; simp
    rw [h1, hm_eq]
  have hEord_ne : Eord.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨u, v⟩, huv_mem, huv_max⟩ :=
    Finset.exists_max_image Eord (fun p => G.degree p.1 + G.degree p.2) hEord_ne
  have huv : G.Adj u v := (Finset.mem_filter.mp huv_mem).2
  have huv_ne : u ≠ v := G.ne_of_adj huv
  have hdu_pos : 1 ≤ G.degree u := Finset.card_pos.mpr ⟨v, (SimpleGraph.mem_neighborFinset G u v).mpr huv⟩
  have hdv_pos : 1 ≤ G.degree v := Finset.card_pos.mpr ⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr huv.symm⟩
  -- Lower bound: 4 * m <= n * (deg u + deg v)
  have h4m_le_n_duv : 4 * m ≤ n * (G.degree u + G.degree v) := by
    have hsum_E : ∑ p ∈ Eord, (G.degree p.1 + G.degree p.2) = 2 * ∑ x : V, G.degree x ^ 2 := by
      rw [Finset.sum_filter, Finset.sum_product]
      have hinner : ∀ x : V, (∑ y : V, if G.Adj x y then G.degree x + G.degree y else 0) =
          G.degree x ^ 2 + ∑ y ∈ G.neighborFinset x, G.degree y := by
        intro x
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (G.Adj x) = G.neighborFinset x := by ext y; simp
        rw [hf, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, sq]
        rfl
      rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_add_distrib, hsum_deg_sq_eq]
      ring
    have hle_max : 2 * ∑ x : V, G.degree x ^ 2 ≤ 2 * m * (G.degree u + G.degree v) := by
      rw [← hsum_E, ← hEord_card]
      calc ∑ p ∈ Eord, (G.degree p.1 + G.degree p.2)
          ≤ ∑ _p ∈ Eord, (G.degree u + G.degree v) := Finset.sum_le_sum (fun p hp => huv_max p hp)
        _ = #Eord * (G.degree u + G.degree v) := by rw [Finset.sum_const, smul_eq_mul]
    have hmul : 2 * m * (4 * m) ≤ 2 * m * (n * (G.degree u + G.degree v)) := by
      calc 2 * m * (4 * m) = 2 * (4 * m ^ 2) := by ring
        _ ≤ 2 * (n * ∑ x : V, G.degree x ^ 2) := Nat.mul_le_mul_left 2 hCS
        _ = n * (2 * ∑ x : V, G.degree x ^ 2) := by ring
        _ ≤ n * (2 * m * (G.degree u + G.degree v)) := Nat.mul_le_mul_left n hle_max
        _ = 2 * m * (n * (G.degree u + G.degree v)) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  -- Step 4: Construct I = (N(u) \ {v}) ∪ (N(v) \ {u}) and M = V \ (I ∪ {u, v})
  let Iu : Finset V := (G.neighborFinset u).erase v
  let Iv : Finset V := (G.neighborFinset v).erase u
  let I : Finset V := Iu ∪ Iv
  let M : Finset V := ((Finset.univ.erase u).erase v) \ I
  have hIu_card : #Iu = G.degree u - 1 := by
    rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G u v).mpr huv)]; rfl
  have hIv_card : #Iv = G.degree v - 1 := by
    rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G v u).mpr huv.symm)]; rfl
  have hdisj_IuIv : Disjoint Iu Iv := by
    rw [Finset.disjoint_left]
    intro x hxu hxv
    exact not_adj_of_cliqueFree_three hTF huv
      ((SimpleGraph.mem_neighborFinset G v x).mp (Finset.mem_erase.mp hxv).2)
      ((SimpleGraph.mem_neighborFinset G u x).mp (Finset.mem_erase.mp hxu).2)
  set a := G.degree u + G.degree v - 2
  have hI_card : #I = a := by
    rw [Finset.card_union_of_disjoint hdisj_IuIv, hIu_card, hIv_card]
    omega
  have hI_indep : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxu | hxv <;> rcases Finset.mem_union.mp hy with hyu | hyv
    · exact not_adj_of_cliqueFree_three hTF
        ((SimpleGraph.mem_neighborFinset G u x).mp (Finset.mem_erase.mp hxu).2) hxy
        ((SimpleGraph.mem_neighborFinset G u y).mp (Finset.mem_erase.mp hyu).2)
    · exact hnoC4 u x y v
        (Finset.mem_erase.mp hyv).1.symm (Finset.mem_erase.mp hxu).1
        ((SimpleGraph.mem_neighborFinset G u x).mp (Finset.mem_erase.mp hxu).2) hxy
        ((SimpleGraph.mem_neighborFinset G v y).mp (Finset.mem_erase.mp hyv).2).symm huv.symm
    · exact hnoC4 v x y u
        (Finset.mem_erase.mp hyu).1.symm (Finset.mem_erase.mp hxv).1
        ((SimpleGraph.mem_neighborFinset G v x).mp (Finset.mem_erase.mp hxv).2) hxy
        ((SimpleGraph.mem_neighborFinset G u y).mp (Finset.mem_erase.mp hyu).2).symm huv
    · exact not_adj_of_cliqueFree_three hTF
        ((SimpleGraph.mem_neighborFinset G v x).mp (Finset.mem_erase.mp hxv).2) hxy
        ((SimpleGraph.mem_neighborFinset G v y).mp (Finset.mem_erase.mp hyv).2)
  have h5a : 5 * a < 2 * n := by
    have hIset : G.IsIndepSet (I : Set V) := fun x hx y hy _ => hI_indep x hx y hy
    have h5 := five_mul_indep_lt_two_mul_card G hTF hH (I : Set V) hIset
    rw [Set.ncard_coe_finset, hI_card] at h5
    exact h5
  have ha_pos : 1 ≤ a := by
    have h1 : n * n < n * (3 * (G.degree u + G.degree v)) := by
      calc n * n = n ^ 2 := (sq n).symm
        _ < 12 * m := h12m
        _ = 3 * (4 * m) := by ring
        _ ≤ 3 * (n * (G.degree u + G.degree v)) := Nat.mul_le_mul_left 3 h4m_le_n_duv
        _ = n * (3 * (G.degree u + G.degree v)) := by ring
    have h2 : n < 3 * (G.degree u + G.degree v) := Nat.lt_of_mul_lt_mul_left h1
    omega
  have hI_sub : I ⊆ (Finset.univ.erase u).erase v := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxu | hxv
    · have h1 := Finset.mem_erase.mp hxu
      have hux := (SimpleGraph.mem_neighborFinset G u x).mp h1.2
      exact Finset.mem_erase.mpr ⟨h1.1, Finset.mem_erase.mpr ⟨(G.ne_of_adj hux).symm, Finset.mem_univ _⟩⟩
    · have h1 := Finset.mem_erase.mp hxv
      have hvx := (SimpleGraph.mem_neighborFinset G v x).mp h1.2
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hvx).symm, Finset.mem_erase.mpr ⟨h1.1, Finset.mem_univ _⟩⟩
  have hM_card : #M = n - 2 - a := by
    have h1 := Finset.card_sdiff_add_card_eq_card hI_sub
    have hv_in : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨huv_ne.symm, Finset.mem_univ _⟩
    have h2 : #((Finset.univ.erase u).erase v) = n - 2 := by
      rw [Finset.card_erase_of_mem hv_in, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
      omega
    rw [hI_card, h2] at h1
    change #M + a = n - 2 at h1
    omega
  have hdisj_IM : Disjoint I M := Finset.disjoint_sdiff
  -- Every w ∈ M has at most 1 neighbor in Iu and at most 1 neighbor in Iv, hence <= 2 in I
  have hdI_le2 : ∀ w ∈ M, #(I.filter (G.Adj w)) ≤ 2 := by
    intro w hw
    have hwu_ne : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).2).1
    have hwv_ne : w ≠ v := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).1
    have h1 : #(Iu.filter (G.Adj w)) ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      by_contra hne
      exact hnoC4 w x u y hwu_ne hne
        (Finset.mem_filter.mp hx).2
        ((SimpleGraph.mem_neighborFinset G u x).mp (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2).symm
        ((SimpleGraph.mem_neighborFinset G u y).mp (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2)
        (Finset.mem_filter.mp hy).2.symm
    have h2 : #(Iv.filter (G.Adj w)) ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      by_contra hne
      exact hnoC4 w x v y hwv_ne hne
        (Finset.mem_filter.mp hx).2
        ((SimpleGraph.mem_neighborFinset G v x).mp (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2).symm
        ((SimpleGraph.mem_neighborFinset G v y).mp (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2)
        (Finset.mem_filter.mp hy).2.symm
    have hunion : I.filter (G.Adj w) = Iu.filter (G.Adj w) ∪ Iv.filter (G.Adj w) := Finset.filter_union _ _ _
    rw [hunion, Finset.card_union_of_disjoint
      (hdisj_IuIv.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    omega
  -- Upper bound on e(I, M) := ∑ w ∈ M, #(I.filter (G.Adj w)) <= a^2 / 2
  set eIM := ∑ w ∈ M, #(I.filter (G.Adj w))
  have heIM_le : eIM ≤ a ^ 2 / 2 := by
    have hswap : eIM = ∑ x ∈ I, #(M.filter (G.Adj x)) := by
      simp only [eIM, Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro w _
      simp [G.adj_comm]
    rw [hswap, Finset.sum_union hdisj_IuIv]
    have hIu_sum : ∑ x ∈ Iu, #(M.filter (G.Adj x)) ≤ (G.degree u - 1) * (G.degree v - 1) := by
      calc ∑ x ∈ Iu, #(M.filter (G.Adj x))
          ≤ ∑ _x ∈ Iu, (G.degree v - 1) := by
            apply Finset.sum_le_sum
            intro x hx
            have hux : G.Adj u x := (SimpleGraph.mem_neighborFinset G u x).mp (Finset.mem_erase.mp hx).2
            have hmax := huv_max (u, x) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hux⟩)
            have hdx_le : G.degree x ≤ G.degree v := by dsimp only at hmax; omega
            have hsub : M.filter (G.Adj x) ⊆ (G.neighborFinset x).erase u := by
              intro w hw
              have hw' := Finset.mem_filter.mp hw
              have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw'.1).1).2).1
              exact Finset.mem_erase.mpr ⟨hwu, (SimpleGraph.mem_neighborFinset G x w).mpr hw'.2⟩
            have hu_in : u ∈ G.neighborFinset x := (SimpleGraph.mem_neighborFinset G x u).mpr hux.symm
            have hcard_e : #((G.neighborFinset x).erase u) = G.degree x - 1 := by
              rw [Finset.card_erase_of_mem hu_in]; rfl
            exact (Finset.card_le_card hsub).trans (by omega)
        _ = (G.degree u - 1) * (G.degree v - 1) := by rw [Finset.sum_const, smul_eq_mul, hIu_card]
    have hIv_sum : ∑ y ∈ Iv, #(M.filter (G.Adj y)) ≤ (G.degree v - 1) * (G.degree u - 1) := by
      calc ∑ y ∈ Iv, #(M.filter (G.Adj y))
          ≤ ∑ _y ∈ Iv, (G.degree u - 1) := by
            apply Finset.sum_le_sum
            intro y hy
            have hvy : G.Adj v y := (SimpleGraph.mem_neighborFinset G v y).mp (Finset.mem_erase.mp hy).2
            have hmax := huv_max (v, y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hvy⟩)
            have hdy_le : G.degree y ≤ G.degree u := by dsimp only at hmax; omega
            have hsub : M.filter (G.Adj y) ⊆ (G.neighborFinset y).erase v := by
              intro w hw
              have hw' := Finset.mem_filter.mp hw
              have hwv : w ≠ v := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw'.1).1).1
              exact Finset.mem_erase.mpr ⟨hwv, (SimpleGraph.mem_neighborFinset G y w).mpr hw'.2⟩
            have hv_in : v ∈ G.neighborFinset y := (SimpleGraph.mem_neighborFinset G y v).mpr hvy.symm
            have hcard_e : #((G.neighborFinset y).erase v) = G.degree y - 1 := by
              rw [Finset.card_erase_of_mem hv_in]; rfl
            exact (Finset.card_le_card hsub).trans (by omega)
        _ = (G.degree v - 1) * (G.degree u - 1) := by rw [Finset.sum_const, smul_eq_mul, hIv_card]
    have h2prod : 2 * (2 * ((G.degree u - 1) * (G.degree v - 1))) ≤ a ^ 2 := by
      have hsum_ab : (G.degree u - 1) + (G.degree v - 1) = a := by omega
      have h4_gen : ∀ x y : ℕ, 4 * (x * y) ≤ (x + y) ^ 2 := by
        intro x y
        have : (0 : ℤ) ≤ ((x : ℤ) - (y : ℤ)) ^ 2 := sq_nonneg _
        have : (4 : ℤ) * ((x : ℤ) * (y : ℤ)) ≤ ((x : ℤ) + (y : ℤ)) ^ 2 := by linarith
        exact_mod_cast this
      have h4n := h4_gen (G.degree u - 1) (G.degree v - 1)
      rw [hsum_ab] at h4n
      omega
    rw [mul_comm (G.degree v - 1)] at hIv_sum
    omega
  -- Exact edge decomposition: 2 * eIM + ∑ w ∈ M, #(M.filter (G.Adj w)) = 2 * (m - a - 1)
  have hedge_decomp : 2 * eIM + ∑ w ∈ M, #(M.filter (G.Adj w)) + 2 * (a + 1) = 2 * m := by
    have hpart : Finset.univ = insert u (insert v (I ∪ M)) := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, M, Finset.mem_sdiff,
        Finset.mem_erase, true_iff]
      by_cases hxu : x = u
      · exact Or.inl hxu
      · by_cases hxv : x = v
        · exact Or.inr (Or.inl hxv)
        · by_cases hxI : x ∈ I
          · exact Or.inr (Or.inr (Or.inl hxI))
          · exact Or.inr (Or.inr (Or.inr ⟨⟨hxv, hxu, trivial⟩, hxI⟩))
    have hu_not : u ∉ insert v (I ∪ M) := by
      simp only [Finset.mem_insert, Finset.mem_union, not_or]
      refine ⟨huv_ne, ?_, ?_⟩
      · intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hI_sub h)).2).1 rfl
      · intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).2).1 rfl
    have hv_not : v ∉ I ∪ M := by
      simp only [Finset.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · intro h; exact (Finset.mem_erase.mp (hI_sub h)).1 rfl
      · intro h; exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
    have hsum_all : 2 * m = G.degree u + G.degree v + (∑ x ∈ I, G.degree x) + (∑ w ∈ M, G.degree w) := by
      rw [hm_eq, hpart, Finset.sum_insert hu_not, Finset.sum_insert hv_not, Finset.sum_union hdisj_IM]
      omega
    have hdeg_M : ∀ w ∈ M, G.degree w = #(I.filter (G.Adj w)) + #(M.filter (G.Adj w)) := by
      intro w hw
      have hnu : ¬ G.Adj w u := fun h =>
        (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).1, (SimpleGraph.mem_neighborFinset G u w).mpr h.symm⟩))
      have hnv : ¬ G.Adj w v := fun h =>
        (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_right _ (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).2).1,
            (SimpleGraph.mem_neighborFinset G v w).mpr h.symm⟩))
      have heq : G.neighborFinset w = I.filter (G.Adj w) ∪ M.filter (G.Adj w) := by
        ext z
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_filter,
          M, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hadj
          by_cases hzI : z ∈ I
          · exact Or.inl ⟨hzI, hadj⟩
          · exact Or.inr ⟨⟨⟨fun h => hnv (h ▸ hadj), fun h => hnu (h ▸ hadj)⟩, hzI⟩, hadj⟩
        · rintro (⟨_, hadj⟩ | ⟨_, hadj⟩) <;> exact hadj
      rw [SimpleGraph.degree, heq, Finset.card_union_of_disjoint
        (hdisj_IM.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hdeg_Iu : ∀ x ∈ Iu, G.degree x = 1 + #(M.filter (G.Adj x)) := by
      intro x hx
      have hux : G.Adj u x := (SimpleGraph.mem_neighborFinset G u x).mp (Finset.mem_erase.mp hx).2
      have heq : G.neighborFinset x = insert u (M.filter (G.Adj x)) := by
        ext z
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_filter,
          M, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hadj
          by_cases hzu : z = u
          · exact Or.inl hzu
          · refine Or.inr ⟨⟨⟨?_, hzu⟩, ?_⟩, hadj⟩
            · rintro rfl
              exact not_adj_of_cliqueFree_three hTF huv hadj.symm hux
            · intro hzI
              exact hI_indep x (Finset.mem_union_left _ hx) z hzI hadj
        · rintro (rfl | ⟨_, hadj⟩)
          · exact hux.symm
          · exact hadj
      have hu_not_M : u ∉ M.filter (G.Adj x) := fun h =>
        (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1).2).1 rfl
      rw [SimpleGraph.degree, heq, Finset.card_insert_of_notMem hu_not_M]; omega
    have hdeg_Iv : ∀ y ∈ Iv, G.degree y = 1 + #(M.filter (G.Adj y)) := by
      intro y hy
      have hvy : G.Adj v y := (SimpleGraph.mem_neighborFinset G v y).mp (Finset.mem_erase.mp hy).2
      have heq : G.neighborFinset y = insert v (M.filter (G.Adj y)) := by
        ext z
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_filter,
          M, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hadj
          by_cases hzv : z = v
          · exact Or.inl hzv
          · refine Or.inr ⟨⟨⟨hzv, ?_⟩, ?_⟩, hadj⟩
            · rintro rfl
              exact not_adj_of_cliqueFree_three hTF huv hvy hadj.symm
            · intro hzI
              exact hI_indep y (Finset.mem_union_right _ hy) z hzI hadj
        · rintro (rfl | ⟨_, hadj⟩)
          · exact hvy.symm
          · exact hadj
      have hv_not_M : v ∉ M.filter (G.Adj y) := fun h =>
        (Finset.mem_erase.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1).1 rfl
      rw [SimpleGraph.degree, heq, Finset.card_insert_of_notMem hv_not_M]; omega
    have hsum_I : ∑ x ∈ I, G.degree x = a + eIM := by
      have hswap : eIM = ∑ x ∈ I, #(M.filter (G.Adj x)) := by
        simp only [eIM, Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro w _
        simp [G.adj_comm]
      rw [hswap, Finset.sum_union hdisj_IuIv, Finset.sum_union hdisj_IuIv,
        Finset.sum_congr rfl hdeg_Iu, Finset.sum_congr rfl hdeg_Iv,
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
        hIu_card, hIv_card]
      omega
    have hsum_M : ∑ w ∈ M, G.degree w = eIM + ∑ w ∈ M, #(M.filter (G.Adj w)) := by
      rw [Finset.sum_congr rfl hdeg_M, Finset.sum_add_distrib]
    omega
  -- Step 5: Handle the single tight case (n = 12, a = 4) in 10 lines
  by_cases h12_4 : n = 12 ∧ a = 4
  · obtain ⟨hn12_eq, ha4_eq⟩ := h12_4
    have hM6 : #M = 6 := by omega
    have heIM8 : eIM ≤ 8 := by rw [ha4_eq] at heIM_le; norm_num at heIM_le; exact heIM_le
    -- Every w ∈ M has at least 1 neighbor in I (else insert w I is indep of size 5, contradicting 5*5 < 24)
    have hdI_ge1 : ∀ w ∈ M, 1 ≤ #(I.filter (G.Adj w)) := by
      intro w hw
      by_contra h0
      have hzero : #(I.filter (G.Adj w)) = 0 := by omega
      have hwI : w ∉ I := (Finset.mem_sdiff.mp hw).2
      have hind : G.IsIndepSet ((insert w I : Finset V) : Set V) := by
        intro x hx y hy _ hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
        · exact G.loopless.irrefl _ hxy
        · have := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hzero) hy'
          exact this hxy
        · have := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hzero) hx'
          exact this hxy.symm
        · exact hI_indep x hx' y hy' hxy
      have h5 := five_mul_indep_lt_two_mul_card G hTF hH _ hind
      rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem hwI, hI_card, ha4_eq] at h5
      omega
    let M1 := M.filter (fun w => #(I.filter (G.Adj w)) = 1)
    have hM1_ge4 : 4 ≤ #M1 := by
      let M2 := M.filter (fun w => ¬ #(I.filter (G.Adj w)) = 1)
      have hsum_c : #M1 + #M2 = 6 := by rw [Finset.card_filter_add_card_filter_not, hM6]
      have heIM_split : eIM = (∑ w ∈ M1, #(I.filter (G.Adj w))) + ∑ w ∈ M2, #(I.filter (G.Adj w)) := by
        exact (Finset.sum_filter_add_sum_filter_not M (fun w => #(I.filter (G.Adj w)) = 1) _).symm
      have hs1 : ∑ w ∈ M1, #(I.filter (G.Adj w)) = #M1 := by
        calc ∑ w ∈ M1, #(I.filter (G.Adj w))
            = ∑ _w ∈ M1, 1 := Finset.sum_congr rfl (fun w hw => (Finset.mem_filter.mp hw).2)
          _ = #M1 := by simp
      have hs2 : 2 * #M2 ≤ ∑ w ∈ M2, #(I.filter (G.Adj w)) := by
        calc 2 * #M2 = ∑ _w ∈ M2, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ w ∈ M2, #(I.filter (G.Adj w)) := by
              apply Finset.sum_le_sum
              intro w hw
              have hw' := Finset.mem_filter.mp hw
              have hge1 := hdI_ge1 w hw'.1
              omega
      omega
    obtain ⟨T, hTM1, hT3⟩ := Finset.exists_subset_card_eq (show 3 ≤ #M1 by omega)
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hT3
    have hnon : ¬ G.Adj x y ∨ ¬ G.Adj y z ∨ ¬ G.Adj x z := by
      by_contra hall; push Not at hall
      exact not_adj_of_cliqueFree_three hTF hall.1 hall.2.1 hall.2.2
    have hkill_pair : ∀ p q : V, p ∈ M1 → q ∈ M1 → p ≠ q → ¬ G.Adj p q → False := by
      intro p q hp hq hpq hnpq
      have hpM : p ∈ M := (Finset.mem_filter.mp hp).1
      have hqM : q ∈ M := (Finset.mem_filter.mp hq).1
      have hdp : #(I.filter (G.Adj p)) = 1 := (Finset.mem_filter.mp hp).2
      have hdq : #(I.filter (G.Adj q)) = 1 := (Finset.mem_filter.mp hq).2
      have hdisj_Ipq : Disjoint I ({p, q} : Finset V) :=
        hdisj_IM.mono_right (Finset.insert_subset hpM (Finset.singleton_subset_iff.mpr hqM))
      have hcard6 : #(I ∪ {p, q}) = 6 := by
        rw [Finset.card_union_of_disjoint hdisj_Ipq, hI_card, ha4_eq, Finset.card_pair hpq]
      have h50 := hH ((I ∪ {p, q} : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard6]; omega)
      have h50' : 50 * (G.induce ((I ∪ {p, q} : Finset V) : Set V)).edgeSet.ncard > 12 ^ 2 := by
        simpa [n, hn12_eq] using h50
      have hedge : 2 * (G.induce ((I ∪ {p, q} : Finset V) : Set V)).edgeSet.ncard = 4 := by
        rw [two_mul_induce_edgeSet_ncard, sum_adj_union_indep G hdisj_Ipq hI_indep,
          Finset.sum_pair hpq, hdp, hdq, Finset.sum_pair hpq]
        have hp0 : ({p, q} : Finset V).filter (G.Adj p) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht'
          · exact G.loopless.irrefl _
          · rw [Finset.mem_singleton.mp ht']; exact hnpq
        have hq0 : ({p, q} : Finset V).filter (G.Adj q) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht'
          · exact fun h => hnpq h.symm
          · rw [Finset.mem_singleton.mp ht']; exact G.loopless.irrefl _
        rw [hp0, hq0]; simp
      omega
    rcases hnon with h1 | h2 | h3
    · exact hkill_pair x y (hTM1 (by simp)) (hTM1 (by simp)) hxy h1
    · exact hkill_pair y z (hTM1 (by simp)) (hTM1 (by simp)) hyz h2
    · exact hkill_pair x z (hTM1 (by simp)) (hTM1 (by simp)) hxz h3
  -- Step 6: All other (n, m, a) with 12 <= n <= 34 die by averaging over r = k - a subsets of M!
  · set r := k - a
    set T0 := n ^ 2 / 50 + 1
    have hr1 : 1 ≤ r := by omega
    have hrM : r ≤ #M := by omega
    have hM2 : 2 ≤ #M := by omega
    have havg := avg_indep_union_ge G hdisj_IM hI_indep (r := r) (T := 2 * T0) hr1 hrM hM2 (by
      intro S hS
      have hScard : #(I ∪ S) = k := by
        rw [Finset.card_union_of_disjoint (hdisj_IM.mono_right (Finset.mem_powersetCard.mp hS).1),
          hI_card, (Finset.mem_powersetCard.mp hS).2]
        omega
      have h50 := hH ((I ∪ S : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hScard]; omega)
      omega)
    -- Combine havg with hedge_decomp and heIM_le:
    -- 2 * T0 * #M * (#M - 1) <= 2 * r * (#M - 1) * eIM + r * (r - 1) * (2 * (m - a - 1) - 2 * eIM)
    -- => T0 * #M * (#M - 1) <= r * (#M - r) * eIM + r * (r - 1) * (m - a - 1)
    have hma1 : a + 1 ≤ m := by nlinarith
    have hdM_eq : ∑ w ∈ M, #(M.filter (G.Adj w)) = 2 * (m - a - 1) - 2 * eIM := by omega
    have heIM_le_ma : eIM ≤ m - a - 1 := by omega
    have hstep_nat : T0 * #M * (#M - 1) ≤ r * (#M - r) * (a ^ 2 / 2) + r * (r - 1) * (m - a - 1) := by
      have hrel_gen : ∀ r' M' c d : ℕ, r' ≤ M' → 1 ≤ M' → 1 ≤ r' → c ≤ d →
          2 * r' * (M' - 1) * c + r' * (r' - 1) * (2 * d - 2 * c) =
          2 * (r' * (M' - r') * c + r' * (r' - 1) * d) := by
        intro r' M' c d hrM' hM1' hr1' hcd
        have hz : ((2 * r' * (M' - 1) * c + r' * (r' - 1) * (2 * d - 2 * c) : ℕ) : ℤ) =
            ((2 * (r' * (M' - r') * c + r' * (r' - 1) * d) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub hM1', Nat.cast_sub hr1', Nat.cast_sub hrM',
            Nat.cast_sub (show 2 * c ≤ 2 * d by omega)]
          ring
        exact Nat.cast_injective hz
      have hrel := hrel_gen r #M eIM (m - a - 1) hrM (by omega) hr1 heIM_le_ma
      have h1 : 2 * (T0 * #M * (#M - 1)) ≤
          2 * (r * (#M - r) * eIM + r * (r - 1) * (m - a - 1)) := by
        rw [hdM_eq, hrel] at havg
        linarith
      have h2 : r * (#M - r) * eIM ≤ r * (#M - r) * (a ^ 2 / 2) := Nat.mul_le_mul_left _ heIM_le
      omega
    have hm_le_3n : m ≤ 3 * n := by
      by_contra hgt
      have h1 : 3 * n + 1 ≤ m := by omega
      have h2 : 4 * (3 * n + 1) ^ 2 ≤ 4 * m ^ 2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left h1 2)
      have h3 : n ^ 2 * (n - 1) ≤ n ^ 2 * 33 := Nat.mul_le_mul_left (n ^ 2) (by omega)
      have h4 : 4 * (3 * n + 1) ^ 2 ≤ n ^ 2 * 33 := h2.trans (h4m2_le.trans h3)
      have h5 : 36 * n ^ 2 < 4 * (3 * n + 1) ^ 2 := by
        have : 4 * (3 * n + 1) ^ 2 = 36 * n ^ 2 + 24 * n + 4 := by ring
        omega
      omega
    have h4m_le_na2 : 4 * m ≤ n * (a + 2) := by
      have ha2 : a + 2 = G.degree u + G.degree v := by omega
      rw [ha2]
      exact h4m_le_n_duv
    have hkill := girth5_arith_kill n (Finset.mem_Icc.mpr ⟨hn12, hn34⟩)
      m (Finset.mem_Icc.mpr ⟨by omega, hm_le_3n⟩)
      a (Finset.mem_Icc.mpr ⟨ha_pos, by omega⟩)
      h12m h4m2_le h5a h4m_le_na2 h12_4
    rw [hM_card] at hstep_nat
    exact absurd hstep_nat (not_le_of_gt hkill)

/-- Helper for Theorem E: in a triangle-free graph, every vertex has at most 2 neighbors on a
    shortest odd cycle. -/
lemma shortest_odd_walk_deg_le_two {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) {L : ℕ} (hL_odd : Odd L) (hL5 : 5 ≤ L)
    (hL_min : ∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1)))
    {f : ℕ → V} (hf_loop : f L = f 0) (hf_adj : ∀ i < L, G.Adj (f i) (f (i + 1)))
    (w : V) :
    #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 := by
  by_contra hgt
  have hge3 : 3 ≤ #((Finset.range L).filter (fun i => G.Adj w (f i))) := by omega
  obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq hge3
  obtain ⟨a0, b0, c0, hab0, hac0, hbc0, rfl⟩ := Finset.card_eq_three.mp hT3
  -- Sort {a0, b0, c0} into i < j < k < L
  have hsort : ∃ i j k : ℕ, i < j ∧ j < k ∧ k < L ∧ G.Adj w (f i) ∧ G.Adj w (f j) ∧ G.Adj w (f k) := by
    have ha := Finset.mem_filter.mp (hTsub (by simp : a0 ∈ ({a0, b0, c0} : Finset ℕ)))
    have hb := Finset.mem_filter.mp (hTsub (by simp : b0 ∈ ({a0, b0, c0} : Finset ℕ)))
    have hc := Finset.mem_filter.mp (hTsub (by simp : c0 ∈ ({a0, b0, c0} : Finset ℕ)))
    have haL := Finset.mem_range.mp ha.1
    have hbL := Finset.mem_range.mp hb.1
    have hcL := Finset.mem_range.mp hc.1
    rcases lt_or_gt_of_ne hab0 with hab | hba <;>
    rcases lt_or_gt_of_ne hbc0 with hbc | hcb <;>
    rcases lt_or_gt_of_ne hac0 with hac | hca
    · exact ⟨a0, b0, c0, hab, hbc, hcL, ha.2, hb.2, hc.2⟩
    · omega
    · exact ⟨a0, c0, b0, hac, hcb, hbL, ha.2, hc.2, hb.2⟩
    · exact ⟨c0, a0, b0, hca, hab, hbL, hc.2, ha.2, hb.2⟩
    · exact ⟨b0, a0, c0, hba, hac, hcL, hb.2, ha.2, hc.2⟩
    · exact ⟨b0, c0, a0, hbc, hca, haL, hb.2, hc.2, ha.2⟩
    · omega
    · exact ⟨c0, b0, a0, hcb, hba, haL, hc.2, hb.2, ha.2⟩
  obtain ⟨i, j, k, hij, hjk, hkL, hwi, hwj, hwk⟩ := hsort
  -- No two of i, j, k can be adjacent on the cycle (triangle-free)
  have hd1 : 2 ≤ j - i := by
    by_contra h1
    have hj_eq : j = i + 1 := by omega
    rw [hj_eq] at hwj
    exact not_adj_of_cliqueFree_three hTF hwi (hf_adj i (by omega)) hwj
  have hd2 : 2 ≤ k - j := by
    by_contra h2
    have hk_eq : k = j + 1 := by omega
    rw [hk_eq] at hwk
    exact not_adj_of_cliqueFree_three hTF hwj (hf_adj j (by omega)) hwk
  have hd3 : 2 ≤ L - (k - i) := by
    by_contra h3
    have hki : k = L - 1 ∧ i = 0 := by omega
    have hk_adj : G.Adj (f k) (f 0) := by
      have := hf_adj k (by omega)
      rwa [show k + 1 = L by omega, hf_loop] at this
    rw [hki.2] at hwi
    exact not_adj_of_cliqueFree_three hTF hwk hk_adj hwi
  -- Helper: an odd arc from p to q (with p < q < L, q - p + 2 < L) gives a shorter odd closed walk via w
  have harc_short : ∀ p q : ℕ, p < q → q < L → Odd (q - p) → q - p + 2 < L →
      G.Adj w (f p) → G.Adj w (f q) → False := by
    intro p q hpq hqL hodd hshort hwp hwq
    have hodd2 : Odd (q - p + 2) := by obtain ⟨t, ht⟩ := hodd; exact ⟨t + 1, by omega⟩
    apply hL_min (q - p + 2) hshort hodd2
    refine ⟨fun t => if t = 0 then w else if t ≤ q - p + 1 then f (p + (t - 1)) else w, ?_, ?_⟩
    · dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    · intro t ht
      dsimp only
      by_cases ht0 : t = 0
      · subst ht0
        rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
        simpa using hwp
      · by_cases ht1 : t + 1 ≤ q - p + 1
        · rw [if_neg ht0, if_pos (by omega), if_neg (by omega), if_pos ht1,
            show p + (t + 1 - 1) = (p + (t - 1)) + 1 by omega]
          exact hf_adj (p + (t - 1)) (by omega)
        · have hteq : t = q - p + 1 := by omega
          subst hteq
          rw [if_neg ht0, if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
            show p + (q - p + 1 - 1) = q by omega]
          exact hwq.symm
  -- Since (j - i) + (k - j) + (L - (k - i)) = L is odd, at least one of the three arcs is odd!
  by_cases ho1 : Odd (j - i)
  · exact harc_short i j hij (by omega) ho1 (by omega) hwi hwj
  · by_cases ho2 : Odd (k - j)
    · exact harc_short j k hjk hkL ho2 (by omega) hwj hwk
    · -- Third arc L - (k - i) must be odd, length d3 + 2 <= L - 2 < L
      have ho3 : Odd (L - (k - i) + 2) := by
        obtain ⟨a, ha⟩ := hL_odd
        obtain ⟨b, hb⟩ := Nat.not_odd_iff_even.mp ho1
        obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.mp ho2
        exact ⟨a - b - c + 1, by omega⟩
      apply hL_min (L - (k - i) + 2) (by omega) ho3
      refine ⟨fun t =>
        if t = 0 then w
        else if t ≤ L - k + 1 then f (k + (t - 1))
        else if t ≤ L - (k - i) + 1 then f (t - (L - k + 1))
        else w, ?_, ?_⟩
      · dsimp only
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      · intro t ht
        dsimp only
        by_cases ht0 : t = 0
        · subst ht0
          rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
          simpa using hwk
        · by_cases ht1 : t + 1 ≤ L - k + 1
          · rw [if_neg ht0, if_pos (by omega), if_neg (by omega), if_pos ht1,
              show k + (t + 1 - 1) = (k + (t - 1)) + 1 by omega]
            exact hf_adj (k + (t - 1)) (by omega)
          · by_cases ht2 : t ≤ L - k + 1
            · have hteq : t = L - k + 1 := by omega
              subst hteq
              by_cases hi0 : i = 0
              · subst hi0
                rw [if_neg ht0, if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
                  if_neg (by omega), show k + (L - k + 1 - 1) = L by omega, hf_loop]
                exact hwi.symm
              · rw [if_neg ht0, if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
                  if_pos (by omega), show k + (L - k + 1 - 1) = L by omega, hf_loop,
                  show L - k + 1 + 1 - (L - k + 1) = 1 by omega]
                exact hf_adj 0 (by omega)
            · by_cases ht3 : t + 1 ≤ L - (k - i) + 1
              · rw [if_neg ht0, if_neg ht2, if_pos (by omega), if_neg (by omega), if_neg ht1, if_pos ht3,
                  show t + 1 - (L - k + 1) = (t - (L - k + 1)) + 1 by omega]
                exact hf_adj (t - (L - k + 1)) (by omega)
              · have hteq : t = L - (k - i) + 1 := by omega
                subst hteq
                rw [if_neg ht0, if_neg ht2, if_pos (le_refl _), if_neg (by omega), if_neg ht1, if_neg (by omega),
                  show L - (k - i) + 1 - (L - k + 1) = i by omega]
                exact hwi.symm

set_option maxHeartbeats 600000 in
/-- Häggkvist (1982): Every non-bipartite triangle-free graph with 8 * δ(G) > 3 * n
    is homomorphic to C_5. -/
theorem haggkvist_hom_c5 {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (hnonbip : ¬ G.Colorable 2)
    (hall : ∀ v : V, 3 * Fintype.card V < 8 * (G.neighborSet v).ncard) :
    ∃ cls : V → Fin 5, ∀ u v : V, G.Adj u v → cls v = cls u + 1 ∨ cls v = cls u + 4 := by
  classical
  set n := Fintype.card V
  have h8d : ∀ v : V, 3 * n < 8 * G.degree v := by
    intro v
    have hv := hall v
    have hdeq : G.degree v = (G.neighborSet v).ncard := by
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
    omega
  -- Step 1: Take shortest odd induced cycle C of length L >= 5; show L = 5
  obtain ⟨L, hL_odd, hL5, hL_min, f, hf_loop, hf_adj, hf_inj, hf_nochord⟩ :=
    exists_shortest_odd_walk_of_nonbip G hTF hnonbip
  have hn_pos : 0 < n := Fintype.card_pos_iff.mpr ⟨f 0⟩
  have hL_eq_5 : L = 5 := by
    have hsum_eq : ∑ i ∈ Finset.range L, G.degree (f i) =
        ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
      have h1 : ∀ i ∈ Finset.range L, G.degree (f i) = #(Finset.univ.filter (fun w => G.Adj w (f i))) := by
        intro i _
        rw [SimpleGraph.degree]
        congr 1; ext w; simp [G.adj_comm]
      rw [Finset.sum_congr rfl h1]
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hsum_le : ∑ i ∈ Finset.range L, G.degree (f i) ≤ 2 * n := by
      rw [hsum_eq]
      calc ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i)))
          ≤ ∑ _w : V, 2 := Finset.sum_le_sum (fun w _ =>
            shortest_odd_walk_deg_le_two G hTF hL_odd hL5 hL_min hf_loop hf_adj w)
        _ = 2 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_gt : 3 * L * n < 8 * ∑ i ∈ Finset.range L, G.degree (f i) := by
      calc 3 * L * n = ∑ _i ∈ Finset.range L, 3 * n := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
        _ < ∑ i ∈ Finset.range L, 8 * G.degree (f i) :=
            Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) (fun i _ => h8d (f i))
        _ = 8 * ∑ i ∈ Finset.range L, G.degree (f i) := (Finset.mul_sum _ _ _).symm
    have h3L : 3 * L * n < 16 * n := by omega
    have hLlt : 3 * L < 16 := by nlinarith
    omega
  -- Step 2: Induced C_5 = (f 0, f 1, f 2, f 3, f 4) and partition V = A_0 ⊔ ... ⊔ A_4 ⊔ B
  have hc_adj : ∀ i : Fin 5, G.Adj (f i.val) (f ((i + 1 : Fin 5).val)) := by
    intro i
    fin_cases i
    · exact hf_adj 0 (by omega)
    · exact hf_adj 1 (by omega)
    · exact hf_adj 2 (by omega)
    · exact hf_adj 3 (by omega)
    · have h4 := hf_adj 4 (by omega)
      rw [show (4 + 1 : ℕ) = L by omega, hf_loop] at h4
      exact h4
  have hc_nadj : ∀ i : Fin 5, ¬ G.Adj (f i.val) (f ((i + 2 : Fin 5).val)) := by
    intro i
    fin_cases i
    · exact hf_nochord 0 2 (by omega) (by omega) (by omega)
    · exact hf_nochord 1 3 (by omega) (by omega) (by omega)
    · exact hf_nochord 2 4 (by omega) (by omega) (by omega)
    · intro h; exact hf_nochord 0 3 (by omega) (by omega) (by omega) h.symm
    · intro h; exact hf_nochord 1 4 (by omega) (by omega) (by omega) h.symm
  have hc_inj : ∀ i j : Fin 5, i ≠ j → f i.val ≠ f j.val := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact hf_inj i.val j.val hlt (by omega)
    · exact (hf_inj j.val i.val hgt (by omega)).symm
  let A : Fin 5 → Finset V := fun i =>
    Finset.univ.filter (fun w => G.Adj w (f ((i + 4 : Fin 5).val)) ∧ G.Adj w (f ((i + 1 : Fin 5).val)))
  let B : Finset V := Finset.univ \ Finset.univ.biUnion A
  -- Every vertex has <= 2 neighbors on C_5
  have hdeg_C5_le2 : ∀ w : V, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) ≤ 2 := by
    intro w
    have hbij : #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) =
        #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (Finset.mem_filter.mp hj).2⟩
      · intro j₁ _ j₂ _ h; exact Fin.ext h
      · intro i hi
        have hi' := Finset.mem_filter.mp hi
        exact ⟨⟨i, by have := Finset.mem_range.mp hi'.1; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.2⟩, rfl⟩
    rw [hbij]
    exact shortest_odd_walk_deg_le_two G hTF hL_odd hL5 hL_min hf_loop hf_adj w
  -- A_i are pairwise disjoint
  have hA_disj : ∀ i j : Fin 5, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact not_adj_of_cliqueFree_three hTF hi.1 (hc_adj _) hj.1
      | exact not_adj_of_cliqueFree_three hTF hi.1 (hc_adj _) hj.2
      | exact not_adj_of_cliqueFree_three hTF hi.2 (hc_adj _) hj.1
      | exact not_adj_of_cliqueFree_three hTF hi.2 (hc_adj _) hj.2
      | exact not_adj_of_cliqueFree_three hTF hj.1 (hc_adj _) hi.1
      | exact not_adj_of_cliqueFree_three hTF hj.1 (hc_adj _) hi.2
      | exact not_adj_of_cliqueFree_three hTF hj.2 (hc_adj _) hi.1
  -- Every w ∈ B has <= 1 neighbor on C_5
  have hB_le1 : ∀ w ∈ B, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) ≤ 1 := by
    intro w hw
    rw [Finset.card_le_one]
    intro j₁ hj₁ j₂ hj₂
    by_contra hne
    have h1 := (Finset.mem_filter.mp hj₁).2
    have h2 := (Finset.mem_filter.mp hj₂).2
    have hw_not_A : ∀ i : Fin 5, w ∉ A i := fun i hi =>
      (Finset.mem_sdiff.mp hw).2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
    fin_cases j₁ <;> fin_cases j₂
    all_goals first
      | exact (hne rfl).elim
      | exact not_adj_of_cliqueFree_three hTF h1 (hc_adj _) h2
      | exact not_adj_of_cliqueFree_three hTF h2 (hc_adj _) h1
      | exact hw_not_A 0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h1 h2⟩)
      | exact hw_not_A 0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h2 h1⟩)
      | exact hw_not_A 1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h1 h2⟩)
      | exact hw_not_A 1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h2 h1⟩)
      | exact hw_not_A 2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h1 h2⟩)
      | exact hw_not_A 2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h2 h1⟩)
      | exact hw_not_A 3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h1 h2⟩)
      | exact hw_not_A 3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h2 h1⟩)
      | exact hw_not_A 4 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h1 h2⟩)
      | exact hw_not_A 4 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using And.intro h2 h1⟩)
  -- Partition count: (∑ i : Fin 5, #(A i)) + #B = n
  have hpart_n : (∑ i : Fin 5, #(A i)) + #B = n := by
    have hbi : #(Finset.univ.biUnion A) = ∑ i : Fin 5, #(A i) :=
      Finset.card_biUnion (fun i _ j _ hij => hA_disj i j hij)
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Finset.univ.biUnion A))
    rw [hbi, Finset.card_univ] at hs
    change #B + ∑ i : Fin 5, #(A i) = n at hs
    omega
  -- Key bound: #B + ∑ i : Fin 5, G.degree (f i.val) <= 2 * n
  have hB_sum_le : #B + ∑ i : Fin 5, G.degree (f i.val) ≤ 2 * n := by
    have hsum_C5 : ∑ i : Fin 5, G.degree (f i.val) =
        ∑ w : V, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) := by
      have h1 : ∀ i : Fin 5, G.degree (f i.val) = #(Finset.univ.filter (fun w => G.Adj w (f i.val))) := by
        intro i; rw [SimpleGraph.degree]; congr 1; ext w; simp [G.adj_comm]
      rw [Finset.sum_congr rfl (fun i _ => h1 i)]
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hdisj_AB : Disjoint (Finset.univ.biUnion A) B := Finset.disjoint_sdiff
    have hsplit : ∑ w : V, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) =
        (∑ w ∈ Finset.univ.biUnion A, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val)))) +
        (∑ w ∈ B, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val)))) := by
      rw [← Finset.sum_union hdisj_AB]
      congr 1; ext w
      simp only [Finset.mem_univ, Finset.mem_union, B, Finset.mem_sdiff, true_and, true_iff]
      exact em _
    have h1 : ∑ w ∈ Finset.univ.biUnion A, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) ≤
        2 * #(Finset.univ.biUnion A) := by
      calc _ ≤ ∑ _w ∈ Finset.univ.biUnion A, 2 := Finset.sum_le_sum (fun w _ => hdeg_C5_le2 w)
        _ = 2 * #(Finset.univ.biUnion A) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h2 : ∑ w ∈ B, #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) ≤ #B := by
      calc _ ≤ ∑ _w ∈ B, 1 := Finset.sum_le_sum hB_le1
        _ = #B := by simp
    have hbi_eq : #(Finset.univ.biUnion A) + #B = n := by
      rw [← Finset.card_union_of_disjoint hdisj_AB]
      have hunion : Finset.univ.biUnion A ∪ B = Finset.univ := by
        ext w; simp only [Finset.mem_union, B, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [hunion, Finset.card_univ]
    omega
  have h8B_lt : 8 * #B < n := by
    have h15 : 15 * n < 8 * ∑ i : Fin 5, G.degree (f i.val) := by
      calc 15 * n = ∑ _i : Fin 5, 3 * n := by simp; ring
        _ < ∑ i : Fin 5, 8 * G.degree (f i.val) :=
            Finset.sum_lt_sum_of_nonempty (by simp) (fun i _ => h8d (f i.val))
        _ = 8 * ∑ i : Fin 5, G.degree (f i.val) := (Finset.mul_sum _ _ _).symm
    omega
  -- Step 3 (Lemma 1): No vertex x has neighbors in BOTH A i and A (i + 1)
  have hno_adj_A : ∀ (x : V) (i : Fin 5), ¬ ((∃ y₁ ∈ A i, G.Adj x y₁) ∧ (∃ y₂ ∈ A (i + 1), G.Adj x y₂)) := by
    intro x i ⟨⟨y₁, hy₁, hxy₁⟩, ⟨y₂, hy₂, hxy₂⟩⟩
    have hy₁' := (Finset.mem_filter.mp hy₁).2
    have hy₂' := (Finset.mem_filter.mp hy₂).2
    have hy₁_a : G.Adj y₁ (f ((i + 4 : Fin 5).val)) := hy₁'.1
    have hy₁_b : G.Adj y₁ (f ((i + 1 : Fin 5).val)) := hy₁'.2
    have hy₂_a : G.Adj y₂ (f i.val) := by simpa [show i + 1 + 4 = i by fin_cases i <;> rfl] using hy₂'.1
    have hy₂_b : G.Adj y₂ (f ((i + 2 : Fin 5).val)) := by
      simpa [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl] using hy₂'.2
    -- All 8 vertices {f 0, f 1, f 2, f 3, f 4, x, y₁, y₂} are distinct
    let C5 : Finset V := Finset.univ.image (fun j : Fin 5 => f j.val)
    have hC5_card : #C5 = 5 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => by
        by_contra hne; exact hc_inj a b hne hab), Finset.card_univ, Fintype.card_fin]
    have hx_not_C5 : x ∉ C5 := by
      intro hx
      obtain ⟨j, -, hfj⟩ := Finset.mem_image.mp hx
      subst hfj
      have hj_cases : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
        fin_cases i <;> fin_cases j <;> decide
      rcases hj_cases with hj | hj | hj | hj | hj <;> rw [hj] at hxy₁ hxy₂
      · exact not_adj_of_cliqueFree_three hTF hxy₁ hy₁_b (hc_adj i)
      · exact not_adj_of_cliqueFree_three hTF hxy₂ hy₂_b (by simpa [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl] using hc_adj (i + 1))
      · exact not_adj_of_cliqueFree_three hTF hxy₁ hy₁_b (by simpa [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl] using (hc_adj (i + 1)).symm)
      · exact not_adj_of_cliqueFree_three hTF hxy₁ hy₁_a (by simpa [show i + 3 + 1 = i + 4 by fin_cases i <;> rfl] using hc_adj (i + 3))
      · exact not_adj_of_cliqueFree_three hTF hxy₂ hy₂_a (by simpa [show i + 4 + 1 = i by fin_cases i <;> rfl] using hc_adj (i + 4))
    have hy₁_not_C5 : y₁ ∉ C5 := by
      intro hy
      obtain ⟨j, -, hfj⟩ := Finset.mem_image.mp hy
      rw [← hfj] at hy₁_a hy₁_b hxy₁
      have hj_cases : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
        fin_cases i <;> fin_cases j <;> decide
      rcases hj_cases with rfl | rfl | rfl | rfl | rfl
      · exact not_adj_of_cliqueFree_three hTF hxy₁ hy₂_a.symm hxy₂
      · exact G.loopless.irrefl _ hy₁_b
      · exact hc_nadj (i + 2) (by simpa [show i + 2 + 2 = i + 4 by fin_cases i <;> rfl] using hy₁_a)
      · exact hc_nadj (i + 1) (by simpa [show i + 1 + 2 = i + 3 by fin_cases i <;> rfl] using hy₁_b.symm)
      · exact G.loopless.irrefl _ hy₁_a
    have hy₂_not_C5 : y₂ ∉ C5 := by
      intro hy
      obtain ⟨j, -, hfj⟩ := Finset.mem_image.mp hy
      rw [← hfj] at hy₂_a hy₂_b hxy₂
      have hj_cases : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
        fin_cases i <;> fin_cases j <;> decide
      rcases hj_cases with rfl | rfl | rfl | rfl | rfl
      · exact G.loopless.irrefl _ hy₂_a
      · exact not_adj_of_cliqueFree_three hTF hxy₂ hy₁_b.symm hxy₁
      · exact G.loopless.irrefl _ hy₂_b
      · exact hc_nadj (i + 3) (by simpa [show i + 3 + 2 = i by fin_cases i <;> rfl] using hy₂_a)
      · exact hc_nadj (i + 2) (by simpa [show i + 2 + 2 = i + 4 by fin_cases i <;> rfl] using hy₂_b.symm)
    have hxy₁_ne : x ≠ y₁ := G.ne_of_adj hxy₁
    have hxy₂_ne : x ≠ y₂ := G.ne_of_adj hxy₂
    have hy₁y₂_ne : y₁ ≠ y₂ := by
      intro heq
      have := Finset.disjoint_left.mp (hA_disj i (i + 1) (by intro h; fin_cases i <;> simp at h)) hy₁
      exact this (heq ▸ hy₂)
    let S : Finset V := insert x (insert y₁ (insert y₂ C5))
    have hS_card : #S = 8 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy₁_ne, hxy₂_ne, hx_not_C5]),
        Finset.card_insert_of_notMem (by simp [hy₁y₂_ne, hy₁_not_C5]),
        Finset.card_insert_of_notMem hy₂_not_C5, hC5_card]
    -- Every vertex w has at most 3 neighbors in S
    have hS_deg_le3 : ∀ w : V, #(S.filter (G.Adj w)) ≤ 3 := by
      intro w
      have hC5_w : #(C5.filter (G.Adj w)) ≤ 2 := by
        have hbij : #(C5.filter (G.Adj w)) = #((Finset.univ : Finset (Fin 5)).filter (fun j => G.Adj w (f j.val))) := by
          refine Finset.card_bij (fun z hz => (Finset.mem_image.mp (Finset.mem_filter.mp hz).1).choose) ?_ ?_ ?_
          · intro z hz
            have hspec := (Finset.mem_image.mp (Finset.mem_filter.mp hz).1).choose_spec
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspec.2.symm ▸ (Finset.mem_filter.mp hz).2⟩
          · intro z₁ hz₁ z₂ hz₂ heq
            have hs1 := (Finset.mem_image.mp (Finset.mem_filter.mp hz₁).1).choose_spec
            have hs2 := (Finset.mem_image.mp (Finset.mem_filter.mp hz₂).1).choose_spec
            rw [← hs1.2, ← hs2.2, heq]
          · intro j hj
            have hfz : f j.val ∈ C5.filter (G.Adj w) :=
              Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, (Finset.mem_filter.mp hj).2⟩
            refine ⟨f j.val, hfz, ?_⟩
            have hs := (Finset.mem_image.mp (Finset.mem_filter.mp hfz).1).choose_spec
            by_contra hne
            exact hc_inj _ j hne hs.2
        rw [hbij]; exact hdeg_C5_le2 w
      have hsplit_S : #(S.filter (G.Adj w)) =
          #(({x, y₁, y₂} : Finset V).filter (G.Adj w)) + #(C5.filter (G.Adj w)) := by
        have hdisj_3 : Disjoint ({x, y₁, y₂} : Finset V) C5 := by
          rw [Finset.disjoint_left]
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        have hS_eq : S = ({x, y₁, y₂} : Finset V) ∪ C5 := by
          ext z; simp [S]
        rw [hS_eq, Finset.filter_union, Finset.card_union_of_disjoint
          (hdisj_3.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      by_cases hwx : G.Adj w x
      · -- x is adjacent to y₁ and y₂, so neither y₁ nor y₂ can be adjacent to w
        have hsub1 : ({x, y₁, y₂} : Finset V).filter (G.Adj w) ⊆ {x} := by
          intro z hz
          have hz' := Finset.mem_filter.mp hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz' ⊢
          rcases hz'.1 with rfl | rfl | rfl
          · rfl
          · exact (not_adj_of_cliqueFree_three hTF hwx hxy₁ hz'.2).elim
          · exact (not_adj_of_cliqueFree_three hTF hwx hxy₂ hz'.2).elim
        have hle1 : #(({x, y₁, y₂} : Finset V).filter (G.Adj w)) ≤ 1 :=
          (Finset.card_le_card hsub1).trans (by simp)
        omega
      · by_cases hwy12 : G.Adj w y₁ ∧ G.Adj w y₂
        · -- Both y₁ and y₂ adjacent to w: kills f i, f(i+1), f(i+2), f(i+4), leaving only f(i+3)!
          have hsubC : C5.filter (G.Adj w) ⊆ {f ((i + 3 : Fin 5).val)} := by
            intro z hz
            have hz' := Finset.mem_filter.mp hz
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz'.1
            simp only [Finset.mem_singleton]
            have hj_cases : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
              fin_cases i <;> fin_cases j <;> decide
            rcases hj_cases with rfl | rfl | rfl | rfl | rfl
            · exact (not_adj_of_cliqueFree_three hTF hwy12.2 hy₂_a hz'.2).elim
            · exact (not_adj_of_cliqueFree_three hTF hwy12.1 hy₁_b hz'.2).elim
            · exact (not_adj_of_cliqueFree_three hTF hwy12.2 hy₂_b hz'.2).elim
            · rfl
            · exact (not_adj_of_cliqueFree_three hTF hwy12.1 hy₁_a hz'.2).elim
          have hleC : #(C5.filter (G.Adj w)) ≤ 1 := (Finset.card_le_card hsubC).trans (by simp)
          have hsub2 : ({x, y₁, y₂} : Finset V).filter (G.Adj w) ⊆ {y₁, y₂} := by
            intro z hz
            have hz' := Finset.mem_filter.mp hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz' ⊢
            rcases hz'.1 with rfl | rfl | rfl
            · exact (hwx hz'.2).elim
            · exact Or.inl rfl
            · exact Or.inr rfl
          have hle2 : #(({x, y₁, y₂} : Finset V).filter (G.Adj w)) ≤ 2 :=
            (Finset.card_le_card hsub2).trans (Finset.card_le_two)
          omega
        · -- At most 1 of {x, y₁, y₂} is adjacent to w
          have hle1 : #(({x, y₁, y₂} : Finset V).filter (G.Adj w)) ≤ 1 := by
            rw [Finset.card_le_one]
            intro a ha b hb
            have ha' := Finset.mem_filter.mp ha
            have hb' := Finset.mem_filter.mp hb
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
            rcases ha'.1 with rfl | rfl | rfl <;> rcases hb'.1 with rfl | rfl | rfl
            all_goals
              first
              | rfl
              | exact (hwx ha'.2).elim
              | exact (hwx hb'.2).elim
              | exact (hwy12 ⟨ha'.2, hb'.2⟩).elim
              | exact (hwy12 ⟨hb'.2, ha'.2⟩).elim
          omega
    -- Sum degrees over S: 8 * (3n) < 8 * ∑ z ∈ S, deg z <= 8 * (3n), contradiction!
    have hsum_S_eq : ∑ z ∈ S, G.degree z = ∑ w : V, #(S.filter (G.Adj w)) := by
      have h1 : ∀ z ∈ S, G.degree z = #(Finset.univ.filter (fun w => G.Adj w z)) := by
        intro z _; rw [SimpleGraph.degree]; congr 1; ext w; simp [G.adj_comm]
      rw [Finset.sum_congr rfl h1]
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hsum_S_le : ∑ z ∈ S, G.degree z ≤ 3 * n := by
      rw [hsum_S_eq]
      calc ∑ w : V, #(S.filter (G.Adj w))
          ≤ ∑ _w : V, 3 := Finset.sum_le_sum (fun w _ => hS_deg_le3 w)
        _ = 3 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_S_gt : 8 * (3 * n) < 8 * ∑ z ∈ S, G.degree z := by
      calc 8 * (3 * n) = ∑ _z ∈ S, 3 * n := by rw [Finset.sum_const, hS_card, smul_eq_mul]
        _ < ∑ z ∈ S, 8 * G.degree z :=
            Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) (fun z _ => h8d z)
        _ = 8 * ∑ z ∈ S, G.degree z := (Finset.mul_sum _ _ _).symm
    omega
  -- Step 4 (Lemma 2): Every vertex x maps to c(x) : Fin 5 with N(x) \ B ⊆ A(c x + 4) ∪ A(c x + 1)
  have hex_c : ∀ x : V, ∃ i : Fin 5, ∀ j : Fin 5, (∃ y ∈ A j, G.Adj x y) →
      j = i + 4 ∨ j = i + 1 := by
    intro x
    have hna := hno_adj_A x
    by_cases h0 : ∃ y ∈ A 0, G.Adj x y
    · have h1 : ¬ ∃ y ∈ A 1, G.Adj x y := fun h => hna 0 ⟨h0, h⟩
      have h4 : ¬ ∃ y ∈ A 4, G.Adj x y := fun h => hna 4 ⟨h, by simpa using h0⟩
      by_cases h2 : ∃ y ∈ A 2, G.Adj x y
      · have h3 : ¬ ∃ y ∈ A 3, G.Adj x y := fun h => hna 2 ⟨h2, h⟩
        refine ⟨1, fun j hj => ?_⟩
        fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (h1 hj).elim | exact (h3 hj).elim | exact (h4 hj).elim
      · refine ⟨4, fun j hj => ?_⟩
        fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (h1 hj).elim | exact (h2 hj).elim | exact (h4 hj).elim
    · by_cases h1 : ∃ y ∈ A 1, G.Adj x y
      · have h2 : ¬ ∃ y ∈ A 2, G.Adj x y := fun h => hna 1 ⟨h1, h⟩
        by_cases h3 : ∃ y ∈ A 3, G.Adj x y
        · have h4 : ¬ ∃ y ∈ A 4, G.Adj x y := fun h => hna 3 ⟨h3, h⟩
          refine ⟨2, fun j hj => ?_⟩
          fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (h0 hj).elim | exact (h2 hj).elim | exact (h4 hj).elim
        · refine ⟨0, fun j hj => ?_⟩
          fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (h0 hj).elim | exact (h2 hj).elim | exact (h3 hj).elim
      · by_cases h2 : ∃ y ∈ A 2, G.Adj x y
        · have h3 : ¬ ∃ y ∈ A 3, G.Adj x y := fun h => hna 2 ⟨h2, h⟩
          refine ⟨3, fun j hj => ?_⟩
          fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (h0 hj).elim | exact (h1 hj).elim | exact (h3 hj).elim
        · by_cases h3 : ∃ y ∈ A 3, G.Adj x y
          · have h4 : ¬ ∃ y ∈ A 4, G.Adj x y := fun h => hna 3 ⟨h3, h⟩
            refine ⟨4, fun j hj => ?_⟩
            fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (h0 hj).elim | exact (h1 hj).elim | exact (h2 hj).elim | exact (h4 hj).elim
          · refine ⟨0, fun j hj => ?_⟩
            fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (h0 hj).elim | exact (h1 hj).elim | exact (h2 hj).elim | exact (h3 hj).elim
  choose cls hcls using hex_c
  -- Step 5 (Lemma 3): For every i : Fin 5, {x | cls x = i ∨ cls x = i + 2} is independent!
  have hN_sub : ∀ x : V, G.neighborFinset x ⊆ A (cls x + 4) ∪ A (cls x + 1) ∪ B := by
    intro x y hy
    have hxy : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp hy
    by_cases hyB : y ∈ B
    · exact Finset.mem_union_right _ hyB
    · have hyU : y ∈ Finset.univ.biUnion A := by
        by_contra hnot
        exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp hyU
      rcases hcls x j ⟨y, hyj, hxy⟩ with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hyj)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hyj)
  have hpair_indep : ∀ i : Fin 5, G.IsIndepSet {x : V | cls x = i ∨ cls x = i + 2} := by
    intro i x hx y hy _ hxy
    change cls x = i ∨ cls x = i + 2 at hx
    change cls y = i ∨ cls y = i + 2 at hy
    have hdisj_N : Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
      rw [Finset.disjoint_left]
      intro z hzx hzy
      exact not_adj_of_cliqueFree_three hTF hxy
        ((SimpleGraph.mem_neighborFinset G y z).mp hzy)
        ((SimpleGraph.mem_neighborFinset G x z).mp hzx)
    have hcard_union : G.degree x + G.degree y = #(G.neighborFinset x ∪ G.neighborFinset y) := by
      rw [Finset.card_union_of_disjoint hdisj_N]; rfl
    have hsame : ∀ j : Fin 5, cls x = j → cls y = j → False := by
      intro j hcx hcy
      have hsub : G.neighborFinset x ∪ G.neighborFinset y ⊆ (A (j + 4) ∪ A (j + 1)) ∪ B := by
        refine Finset.union_subset ?_ ?_
        · simpa [hcx] using hN_sub x
        · simpa [hcy] using hN_sub y
      have hle : G.degree x + G.degree y ≤ #(A (j + 4) ∪ A (j + 1)) + #B := by
        rw [hcard_union]
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hA_sub_f : A (j + 4) ∪ A (j + 1) ⊆ G.neighborFinset (f j.val) := by
        intro z hz
        rw [SimpleGraph.mem_neighborFinset]
        rcases Finset.mem_union.mp hz with h1 | h2
        · exact (by simpa [show j + 4 + 1 = j by fin_cases j <;> rfl] using (Finset.mem_filter.mp h1).2.2 : G.Adj z (f j.val)).symm
        · exact (by simpa [show j + 1 + 4 = j by fin_cases j <;> rfl] using (Finset.mem_filter.mp h2).2.1 : G.Adj z (f j.val)).symm
      have hf_disj : Disjoint (G.neighborFinset (f j.val)) (G.neighborFinset (f ((j + 1 : Fin 5).val))) := by
        rw [Finset.disjoint_left]
        intro z hz1 hz2
        exact not_adj_of_cliqueFree_three hTF (hc_adj j)
          ((SimpleGraph.mem_neighborFinset G _ z).mp hz2)
          ((SimpleGraph.mem_neighborFinset G _ z).mp hz1)
      have hf_sum : G.degree (f j.val) + G.degree (f ((j + 1 : Fin 5).val)) ≤ n := by
        have h1 : G.degree (f j.val) + G.degree (f ((j + 1 : Fin 5).val)) =
            #(G.neighborFinset (f j.val) ∪ G.neighborFinset (f ((j + 1 : Fin 5).val))) := by
          rw [Finset.card_union_of_disjoint hf_disj]; rfl
        rw [h1]
        exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simp [n])
      have hAle : #(A (j + 4) ∪ A (j + 1)) ≤ G.degree (f j.val) := Finset.card_le_card hA_sub_f
      have hdf1 := h8d (f ((j + 1 : Fin 5).val))
      have hdx := h8d x
      have hdy := h8d y
      omega
    have hdiff : ∀ a b : V, G.Adj a b → cls a = i → cls b = i + 2 → False := by
      intro a b hab hca hcb
      have hdisj_ab : Disjoint (G.neighborFinset a) (G.neighborFinset b) := by
        rw [Finset.disjoint_left]
        intro z hza hzb
        exact not_adj_of_cliqueFree_three hTF hab
          ((SimpleGraph.mem_neighborFinset G b z).mp hzb)
          ((SimpleGraph.mem_neighborFinset G a z).mp hza)
      have hsub : G.neighborFinset a ∪ G.neighborFinset b ⊆
          (A (i + 4) ∪ A (i + 1) ∪ A (i + 3)) ∪ B := by
        refine Finset.union_subset ?_ ?_
        · intro z hz
          have hza := hN_sub a hz; rw [hca] at hza
          simp only [Finset.mem_union] at hza ⊢
          rcases hza with (h1 | h2) | h3
          · exact Or.inl (Or.inl (Or.inl h1))
          · exact Or.inl (Or.inl (Or.inr h2))
          · exact Or.inr h3
        · intro z hz
          have hzb := hN_sub b hz
          rw [hcb, show i + 2 + 4 = i + 1 by fin_cases i <;> rfl,
            show i + 2 + 1 = i + 3 by fin_cases i <;> rfl] at hzb
          simp only [Finset.mem_union] at hzb ⊢
          rcases hzb with (h1 | h2) | h3
          · exact Or.inl (Or.inl (Or.inr h1))
          · exact Or.inl (Or.inr h2)
          · exact Or.inr h3
      have hle3 : G.degree a + G.degree b ≤ #(A (i + 4)) + #(A (i + 1)) + #(A (i + 3)) + #B := by
        have h1 : G.degree a + G.degree b ≤ #((A (i + 4) ∪ A (i + 1) ∪ A (i + 3)) ∪ B) := by
          have hu : G.degree a + G.degree b = #(G.neighborFinset a ∪ G.neighborFinset b) := by
            rw [Finset.card_union_of_disjoint hdisj_ab]; rfl
          rw [hu]
          exact Finset.card_le_card hsub
        have h2 : #((A (i + 4) ∪ A (i + 1) ∪ A (i + 3)) ∪ B) ≤
            #(A (i + 4) ∪ A (i + 1) ∪ A (i + 3)) + #B := Finset.card_union_le _ _
        have h3 : #(A (i + 4) ∪ A (i + 1) ∪ A (i + 3)) ≤ #(A (i + 4)) + #(A (i + 1)) + #(A (i + 3)) :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
        omega
      -- Every neighbor of f(i+1) lies in A i ∪ A(i+2) ∪ B!
      have hf1_sub : G.neighborFinset (f ((i + 1 : Fin 5).val)) ⊆ (A i ∪ A (i + 2)) ∪ B := by
        intro z hz
        have hfz : G.Adj (f ((i + 1 : Fin 5).val)) z := (SimpleGraph.mem_neighborFinset G _ z).mp hz
        by_cases hzB : z ∈ B
        · exact Finset.mem_union_right _ hzB
        · have hzU : z ∈ Finset.univ.biUnion A := by
            by_contra hnot; exact hzB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
          obtain ⟨j, -, hzj⟩ := Finset.mem_biUnion.mp hzU
          have hzj' := (Finset.mem_filter.mp hzj).2
          have hj_cases : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
            fin_cases i <;> fin_cases j <;> decide
          rcases hj_cases with rfl | rfl | rfl | rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzj)
          · exact (not_adj_of_cliqueFree_three hTF (hc_adj i) hfz
              (by simpa [show i + 1 + 4 = i by fin_cases i <;> rfl] using hzj'.1.symm)).elim
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzj)
          · exact (not_adj_of_cliqueFree_three hTF
              (by simpa [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl] using hc_adj (i + 1))
              (by simpa [show i + 3 + 4 = i + 2 by fin_cases i <;> rfl] using hzj'.1.symm) hfz).elim
          · exact (not_adj_of_cliqueFree_three hTF (hc_adj i) hfz
              (by simpa [show i + 4 + 1 = i by fin_cases i <;> rfl] using hzj'.2.symm)).elim
      have hf1_le : G.degree (f ((i + 1 : Fin 5).val)) ≤ #(A i) + #(A (i + 2)) + #B := by
        have h1 : G.degree (f ((i + 1 : Fin 5).val)) ≤ #((A i ∪ A (i + 2)) ∪ B) := Finset.card_le_card hf1_sub
        have h2 : #((A i ∪ A (i + 2)) ∪ B) ≤ #(A i ∪ A (i + 2)) + #B := Finset.card_union_le _ _
        have h3 : #(A i ∪ A (i + 2)) ≤ #(A i) + #(A (i + 2)) := Finset.card_union_le _ _
        omega
      -- Combine: sum of all 5 #(A j) equals n - #B!
      have hsumA5 : #(A i) + #(A (i + 1)) + #(A (i + 2)) + #(A (i + 3)) + #(A (i + 4)) =
          ∑ j : Fin 5, #(A j) := by
        fin_cases i <;> simp [Fin.sum_univ_five] <;> omega
      have h8_sum : G.degree a + G.degree b + G.degree (f ((i + 1 : Fin 5).val)) +
          ∑ j : Fin 5, G.degree (f j.val) ≤ 3 * n := by omega
      have h8_gt : 8 * (3 * n) < 8 * (G.degree a + G.degree b + G.degree (f ((i + 1 : Fin 5).val)) +
          ∑ j : Fin 5, G.degree (f j.val)) := by
        have hda := h8d a
        have hdb := h8d b
        have hdf1 := h8d (f ((i + 1 : Fin 5).val))
        have h15 : 15 * n < 8 * ∑ j : Fin 5, G.degree (f j.val) := by
          calc 15 * n = ∑ _j : Fin 5, 3 * n := by simp; ring
            _ < ∑ j : Fin 5, 8 * G.degree (f j.val) :=
                Finset.sum_lt_sum_of_nonempty (by simp) (fun j _ => h8d (f j.val))
            _ = 8 * ∑ j : Fin 5, G.degree (f j.val) := (Finset.mul_sum _ _ _).symm
        omega
      omega
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hsame i hx hy
    · exact hdiff x y hxy hx hy
    · exact hdiff y x hxy.symm hy hx
    · exact hsame (i + 2) hx hy
  refine ⟨cls, fun u v huv => ?_⟩
  have hcases : cls v = cls u ∨ cls v = cls u + 1 ∨ cls v = cls u + 2 ∨ cls v = cls u + 3 ∨ cls v = cls u + 4 := by
    generalize cls u = a; generalize cls v = b; fin_cases a <;> fin_cases b <;> decide
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · exact (hpair_indep (cls u) (Or.inl rfl) (Or.inl h0) (G.ne_of_adj huv) huv).elim
  · exact Or.inl h1
  · exact (hpair_indep (cls u) (Or.inl rfl) (Or.inr h2) (G.ne_of_adj huv) huv).elim
  · have h3' : cls u = cls v + 2 := by rw [h3]; generalize cls u = a; fin_cases a <;> rfl
    exact (hpair_indep (cls v) (Or.inr h3') (Or.inl rfl) (G.ne_of_adj huv) huv).elim
  · exact Or.inr h4

/-- Any C_5-homomorphic graph has an independent set of size >= 2n/5, contradicting Theorem A. -/
lemma not_hom_c5_of_counterexample {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (cls : V → Fin 5) (hcls : ∀ u v : V, G.Adj u v → cls v = cls u + 1 ∨ cls v = cls u + 4) :
    False := by
  classical
  have hpair_indep : ∀ i : Fin 5, G.IsIndepSet {x : V | cls x = i ∨ cls x = i + 2} := by
    intro i x hx y hy _ hxy
    change cls x = i ∨ cls x = i + 2 at hx
    change cls y = i ∨ cls y = i + 2 at hy
    have hadj := hcls x y hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hadj
    · rcases hadj with h | h <;> (fin_cases i <;> simp at h)
    · rcases hadj with h | h <;> (fin_cases i <;> simp at h)
    · rcases hadj with h | h <;> (fin_cases i <;> simp at h)
    · rcases hadj with h | h <;> (fin_cases i <;> simp at h)
  have hlt_all : ∀ i : Fin 5, 5 * ({x : V | cls x = i ∨ cls x = i + 2}).ncard < 2 * Fintype.card V :=
    fun i => five_mul_indep_lt_two_mul_card G hTF hH _ (hpair_indep i)
  have hsum_lt : ∑ i : Fin 5, 5 * ({x : V | cls x = i ∨ cls x = i + 2}).ncard <
      ∑ _i : Fin 5, 2 * Fintype.card V :=
    Finset.sum_lt_sum_of_nonempty (by simp) (fun i _ => hlt_all i)
  have hsum_eq : ∑ i : Fin 5, ({x : V | cls x = i ∨ cls x = i + 2}).ncard = 2 * Fintype.card V := by
    have hcard : ∀ i : Fin 5, ({x : V | cls x = i ∨ cls x = i + 2}).ncard =
        #(Finset.univ.filter (fun x => cls x = i)) + #(Finset.univ.filter (fun x => cls x = i + 2)) := by
      intro i
      rw [Set.ncard_eq_toFinset_card']
      have hdisj : Disjoint (Finset.univ.filter (fun x => cls x = i))
          (Finset.univ.filter (fun x => cls x = i + 2)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have heq : i = i + 2 := (Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2
        fin_cases i <;> simp at heq
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1; ext x; simp
    simp_rw [hcard, Finset.sum_add_distrib]
    have htot : ∑ i : Fin 5, #(Finset.univ.filter (fun x => cls x = i)) = Fintype.card V := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := cls) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have htot2 : ∑ i : Fin 5, #(Finset.univ.filter (fun x => cls x = i + 2)) = Fintype.card V := by
      rw [← htot]
      exact Fintype.sum_equiv (Equiv.addRight (2 : Fin 5)) _ _ (fun i => rfl)
    omega
  rw [← Finset.mul_sum, hsum_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_lt
  omega


/-- Directed adjacency sum in a disjoint union J ∪ S (without assuming J is independent). -/
lemma sum_adj_union {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {J S : Finset V}
    (hdisj : Disjoint J S) :
    ∑ u ∈ J ∪ S, #((J ∪ S).filter (G.Adj u)) =
      (∑ u ∈ J, #(J.filter (G.Adj u))) +
      2 * (∑ w ∈ S, #(J.filter (G.Adj w))) +
      (∑ u ∈ S, #(S.filter (G.Adj u))) := by
  rw [Finset.sum_union hdisj]
  have hfilter : ∀ u, #((J ∪ S).filter (G.Adj u)) = #(J.filter (G.Adj u)) + #(S.filter (G.Adj u)) := by
    intro u
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  simp_rw [hfilter, Finset.sum_add_distrib]
  have hJS : ∑ u ∈ J, #(S.filter (G.Adj u)) = ∑ w ∈ S, #(J.filter (G.Adj w)) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro u _
    simp [G.adj_comm]
  omega

/-- Scaled averaging lemma for arbitrary disjoint Finsets J, K (cancels (#K - 1) cleanly). -/
lemma avg_union_ge_scaled {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {J K : Finset V} {r T : ℕ}
    (hdisj : Disjoint J K) (hr1 : 1 ≤ r) (hrK : r ≤ #K) (hK2 : 2 ≤ #K)
    (hbound : ∀ S ∈ K.powersetCard r, T ≤ 25 * (2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard)) :
    T * #K ≤
      25 * (#K * (∑ u ∈ J, #(J.filter (G.Adj u))) +
        2 * r * (∑ w ∈ K, #(J.filter (G.Adj w))) +
        r * (∑ u ∈ K, #(K.filter (G.Adj u)))) := by
  have hsum_le : (#K).choose r * T ≤
      25 * ∑ S ∈ K.powersetCard r, 2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard := by
    rw [Finset.mul_sum]
    calc (#K).choose r * T
        = ∑ _S ∈ K.powersetCard r, T := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hbound
  have hsum_eq : ∑ S ∈ K.powersetCard r, 2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard =
      (#K).choose r * (∑ u ∈ J, #(J.filter (G.Adj u))) +
      2 * (#K - 1).choose (r - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
      (if 2 ≤ r then (#K - 2).choose (r - 2) * (∑ u ∈ K, #(K.filter (G.Adj u))) else 0) := by
    have hstep : ∀ S ∈ K.powersetCard r,
        2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard =
        (∑ u ∈ J, #(J.filter (G.Adj u))) +
        2 * (∑ w ∈ S, #(J.filter (G.Adj w))) +
        (∑ u ∈ S, #(S.filter (G.Adj u))) := by
      intro S hS
      rw [two_mul_induce_edgeSet_ncard]
      exact sum_adj_union G (hdisj.mono_right (Finset.mem_powersetCard.mp hS).1)
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_powersetCard, smul_eq_mul, ← Finset.mul_sum]
    congr 1
    · congr 1
      have h1 : ∑ S ∈ K.powersetCard r, ∑ w ∈ S, #(J.filter (G.Adj w)) =
          ∑ w ∈ K, #((K.powersetCard r).filter (w ∈ ·)) * #(J.filter (G.Adj w)) := by
        calc ∑ S ∈ K.powersetCard r, ∑ w ∈ S, #(J.filter (G.Adj w))
            = ∑ S ∈ K.powersetCard r, ∑ w ∈ K, if w ∈ S then #(J.filter (G.Adj w)) else 0 := by
              apply Finset.sum_congr rfl
              intro S hS
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hS).1]
          _ = ∑ w ∈ K, ∑ S ∈ K.powersetCard r, if w ∈ S then #(J.filter (G.Adj w)) else 0 := Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro w _
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [h1, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [card_powersetCard_mem K hw hr1]
    · by_cases hr2 : 2 ≤ r
      · rw [if_pos hr2]
        have h2 : ∑ S ∈ K.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u)) =
            ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u), #((K.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) := by
          calc ∑ S ∈ K.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u))
              = ∑ S ∈ K.powersetCard r, ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro S hS
                have hSK := (Finset.mem_powersetCard.mp hS).1
                calc ∑ u ∈ S, #(S.filter (G.Adj u))
                    = ∑ u ∈ K, if u ∈ S then #(S.filter (G.Adj u)) else 0 := by
                      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSK]
                  _ = ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u), if u ∈ S ∧ v ∈ S then 1 else 0 := by
                      apply Finset.sum_congr rfl
                      intro u _
                      by_cases hu : u ∈ S
                      · simp only [hu, true_and, if_true, ← Finset.card_filter]
                        congr 1; ext v; simp only [Finset.mem_filter]
                        exact ⟨fun ⟨hv, hadj⟩ => ⟨⟨hSK hv, hadj⟩, hv⟩, fun ⟨⟨_, hadj⟩, hv⟩ => ⟨hv, hadj⟩⟩
                      · simp [hu]
            _ = ∑ u ∈ K, ∑ S ∈ K.powersetCard r, ∑ v ∈ K.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := Finset.sum_comm
            _ = ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u), ∑ S ∈ K.powersetCard r,
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl; intro u _; exact Finset.sum_comm
            _ = _ := by
                apply Finset.sum_congr rfl; intro u _
                apply Finset.sum_congr rfl; intro v _
                rw [← Finset.card_filter]
        rw [h2, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have hinner : ∑ v ∈ K.filter (G.Adj u), #((K.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
            ∑ _v ∈ K.filter (G.Adj u), (#K - 2).choose (r - 2) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hv' := Finset.mem_filter.mp hv
          exact card_powersetCard_mem_pair K hu hv'.1 (G.ne_of_adj hv'.2) hr2
        rw [hinner, Finset.sum_const, smul_eq_mul, mul_comm]
      · rw [if_neg hr2]
        have hr_eq : r = 1 := by omega
        apply Finset.sum_eq_zero
        intro S hS
        have hScard : #S = 1 := by rw [(Finset.mem_powersetCard.mp hS).2, hr_eq]
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hScard
        simp
  rw [hsum_eq] at hsum_le
  have hpos : 0 < (#K).choose r := Nat.choose_pos hrK
  have hc1 : (#K).choose r * r = #K * (#K - 1).choose (r - 1) := by
    have := Nat.add_one_mul_choose_eq (#K - 1) (r - 1)
    rw [show #K - 1 + 1 = #K by omega, show r - 1 + 1 = r by omega] at this
    linarith
  have hc2 : 2 ≤ r → (#K).choose r * r * (r - 1) = #K * (#K - 1) * (#K - 2).choose (r - 2) := by
    intro hr2
    have hstep1 : (#K - 1).choose (r - 1) * (r - 1) = (#K - 1) * (#K - 2).choose (r - 2) := by
      have := Nat.add_one_mul_choose_eq (#K - 2) (r - 2)
      rw [show #K - 2 + 1 = #K - 1 by omega, show r - 2 + 1 = r - 1 by omega] at this
      linarith
    calc (#K).choose r * r * (r - 1)
        = (#K * (#K - 1).choose (r - 1)) * (r - 1) := by rw [hc1]
      _ = #K * ((#K - 1).choose (r - 1) * (r - 1)) := by ring
      _ = #K * ((#K - 1) * (#K - 2).choose (r - 2)) := by rw [hstep1]
      _ = #K * (#K - 1) * (#K - 2).choose (r - 2) := by ring
  have hmul := Nat.mul_le_mul_left (#K * (#K - 1)) hsum_le
  set dJ := ∑ u ∈ J, #(J.filter (G.Adj u))
  set eJK := ∑ w ∈ K, #(J.filter (G.Adj w))
  set dK := ∑ u ∈ K, #(K.filter (G.Adj u))
  have hcore : T * #K * (#K - 1) ≤ 25 * (#K * (#K - 1) * dJ + 2 * r * (#K - 1) * eJK + r * (r - 1) * dK) := by
    by_cases hr2 : 2 ≤ r
    · rw [if_pos hr2] at hmul
      have hkey : (#K).choose r * (T * #K * (#K - 1)) ≤
          (#K).choose r * (25 * (#K * (#K - 1) * dJ + 2 * r * (#K - 1) * eJK + r * (r - 1) * dK)) := by
        calc (#K).choose r * (T * #K * (#K - 1))
            = #K * (#K - 1) * ((#K).choose r * T) := by ring
          _ ≤ #K * (#K - 1) * (25 * ((#K).choose r * dJ + 2 * (#K - 1).choose (r - 1) * eJK +
                (#K - 2).choose (r - 2) * dK)) := hmul
          _ = 25 * ((#K).choose r * #K * (#K - 1) * dJ +
                2 * (#K * (#K - 1).choose (r - 1)) * (#K - 1) * eJK +
                (#K * (#K - 1) * (#K - 2).choose (r - 2)) * dK) := by ring
          _ = 25 * ((#K).choose r * #K * (#K - 1) * dJ +
                2 * ((#K).choose r * r) * (#K - 1) * eJK +
                ((#K).choose r * r * (r - 1)) * dK) := by rw [← hc1, ← hc2 hr2]
          _ = _ := by ring
      exact Nat.le_of_mul_le_mul_left hkey hpos
    · rw [if_neg hr2, add_zero] at hmul
      have hr_eq : r = 1 := by omega
      subst hr_eq
      have hkey : (#K).choose 1 * (T * #K * (#K - 1)) ≤
          (#K).choose 1 * (25 * (#K * (#K - 1) * dJ + 2 * 1 * (#K - 1) * eJK + 1 * (1 - 1) * dK)) := by
        calc (#K).choose 1 * (T * #K * (#K - 1))
            = #K * (#K - 1) * ((#K).choose 1 * T) := by ring
          _ ≤ #K * (#K - 1) * (25 * ((#K).choose 1 * dJ + 2 * (#K - 1).choose (1 - 1) * eJK)) := hmul
          _ = 25 * ((#K).choose 1 * #K * (#K - 1) * dJ +
                2 * (#K * (#K - 1).choose (1 - 1)) * (#K - 1) * eJK) := by ring
          _ = 25 * ((#K).choose 1 * #K * (#K - 1) * dJ +
                2 * ((#K).choose 1 * 1) * (#K - 1) * eJK) := by rw [← hc1]
          _ = _ := by simp; ring
      exact Nat.le_of_mul_le_mul_left hkey hpos
  have hrm : r * (r - 1) * dK ≤ r * (#K - 1) * dK :=
    Nat.mul_le_mul_right dK (Nat.mul_le_mul_left r (by omega))
  have hfact : (T * #K) * (#K - 1) ≤ (25 * (#K * dJ + 2 * r * eJK + r * dK)) * (#K - 1) := by
    have h1 : 25 * (#K * (#K - 1) * dJ + 2 * r * (#K - 1) * eJK + r * (r - 1) * dK) ≤
        25 * (#K * (#K - 1) * dJ + 2 * r * (#K - 1) * eJK + r * (#K - 1) * dK) := by omega
    have h2 : 25 * (#K * (#K - 1) * dJ + 2 * r * (#K - 1) * eJK + r * (#K - 1) * dK) =
        (25 * (#K * dJ + 2 * r * eJK + r * dK)) * (#K - 1) := by ring
    omega
  exact Nat.le_of_mul_le_mul_right hfact (by omega)

/-- Elementary C_5 cyclic product upper bound via deviation from mean. -/
lemma c5_adj_sum_le (u : Fin 5 → ℕ) (S B : ℕ)
    (hS : ∑ i : Fin 5, u i = S)
    (hdev : ∀ i : Fin 5, 5 * u i ≤ S + B ∧ S ≤ 5 * u i + B) :
    50 * (∑ i : Fin 5, u i * u (i + 1)) ≤ 10 * S ^ 2 + 10 * B ^ 2 := by
  have hSz : (u 0 : ℤ) + u 1 + u 2 + u 3 + u 4 = (S : ℤ) := by
    have h1 : ∑ i : Fin 5, u i = u 0 + u 1 + u 2 + u 3 + u 4 := by simp [Fin.sum_univ_five]
    exact_mod_cast (h1.symm.trans hS)
  have hsq : ∀ i : Fin 5, (5 * (u i : ℤ) - (S : ℤ)) ^ 2 ≤ (B : ℤ) ^ 2 := by
    intro i
    have h1 : 5 * (u i : ℤ) - (S : ℤ) ≤ (B : ℤ) := by have := (hdev i).1; omega
    have h2 : -(B : ℤ) ≤ 5 * (u i : ℤ) - (S : ℤ) := by have := (hdev i).2; omega
    nlinarith
  have h0 := hsq 0; have h1 := hsq 1; have h2 := hsq 2; have h3 := hsq 3; have h4 := hsq 4
  have hz : 50 * ((u 0 : ℤ) * u 1 + u 1 * u 2 + u 2 * u 3 + u 3 * u 4 + u 4 * u 0) ≤
      10 * (S : ℤ) ^ 2 + 10 * (B : ℤ) ^ 2 := by
    have hid : 10 * ((u 0 : ℤ) + u 1 + u 2 + u 3 + u 4) ^ 2 +
        2 * ((5 * (u 0 : ℤ) - S) ^ 2 + (5 * (u 1 : ℤ) - S) ^ 2 + (5 * (u 2 : ℤ) - S) ^ 2 +
          (5 * (u 3 : ℤ) - S) ^ 2 + (5 * (u 4 : ℤ) - S) ^ 2) -
        50 * ((u 0 : ℤ) * u 1 + u 1 * u 2 + u 2 * u 3 + u 3 * u 4 + u 4 * u 0) =
        25 * (((u 0 : ℤ) - u 1) ^ 2 + ((u 1 : ℤ) - u 2) ^ 2 + ((u 2 : ℤ) - u 3) ^ 2 +
          ((u 3 : ℤ) - u 4) ^ 2 + ((u 4 : ℤ) - u 0) ^ 2) +
        10 * (((u 0 : ℤ) + u 1 + u 2 + u 3 + u 4) - S) ^ 2 := by ring
    nlinarith [sq_nonneg ((u 0 : ℤ) - u 1), sq_nonneg ((u 1 : ℤ) - u 2),
      sq_nonneg ((u 2 : ℤ) - u 3), sq_nonneg ((u 3 : ℤ) - u 4), sq_nonneg ((u 4 : ℤ) - u 0)]
  have hsum_eq : ∑ i : Fin 5, u i * u (i + 1) =
      u 0 * u 1 + u 1 * u 2 + u 2 * u 3 + u 3 * u 4 + u 4 * u 0 := by
    simp [Fin.sum_univ_five]
  rw [hsum_eq]
  exact_mod_cast hz

/-- Elementary C_5 half-set sum upper bound: 5 * ∑ s_i * (k - s_i) <= n^2 for all finite n. -/
lemma c5_half_sum_le (w : Fin 5 → ℕ) (n k : ℕ)
    (hw : ∑ i : Fin 5, w i = n) (hk : 2 * k ≤ n)
    (hle : ∀ i : Fin 5, w i + w (i + 2) ≤ k) :
    5 * (∑ i : Fin 5, (w i + w (i + 2)) * (k - (w i + w (i + 2)))) ≤ n ^ 2 := by
  set s0 := w 0 + w 2
  set s1 := w 1 + w 3
  set s2 := w 2 + w 4
  set s3 := w 3 + w 0
  set s4 := w 4 + w 1
  have hsum_eq : ∑ i : Fin 5, (w i + w (i + 2)) * (k - (w i + w (i + 2))) =
      s0 * (k - s0) + s1 * (k - s1) + s2 * (k - s2) + s3 * (k - s3) + s4 * (k - s4) := by
    simp [Fin.sum_univ_five, s0, s1, s2, s3, s4]
  have htot : s0 + s1 + s2 + s3 + s4 = 2 * n := by
    have h1 : ∑ i : Fin 5, w i = w 0 + w 1 + w 2 + w 3 + w 4 := by simp [Fin.sum_univ_five]
    omega
  have hle0 : s0 ≤ k := hle 0
  have hle1 : s1 ≤ k := hle 1
  have hle2 : s2 ≤ k := hle 2
  have hle3 : s3 ≤ k := by simpa [s3] using hle 3
  have hle4 : s4 ≤ k := by simpa [s4] using hle 4
  rw [hsum_eq]
  have hz : (5 * (s0 * (k - s0) + s1 * (k - s1) + s2 * (k - s2) + s3 * (k - s3) + s4 * (k - s4)) : ℕ) ≤
      (n ^ 2 : ℕ) := by
    zify [hle0, hle1, hle2, hle3, hle4]
    have htotz : (s0 : ℤ) + s1 + s2 + s3 + s4 = 2 * (n : ℤ) := by exact_mod_cast htot
    have hkz : 2 * (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
    have hnz : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
    have hcs : ((s0 : ℤ) + s1 + s2 + s3 + s4) ^ 2 ≤
        5 * ((s0 : ℤ) ^ 2 + s1 ^ 2 + s2 ^ 2 + s3 ^ 2 + s4 ^ 2) := by
      have hid : 5 * ((s0 : ℤ) ^ 2 + s1 ^ 2 + s2 ^ 2 + s3 ^ 2 + s4 ^ 2) -
          ((s0 : ℤ) + s1 + s2 + s3 + s4) ^ 2 =
          ((s0 : ℤ) - s1) ^ 2 + ((s0 : ℤ) - s2) ^ 2 + ((s0 : ℤ) - s3) ^ 2 + ((s0 : ℤ) - s4) ^ 2 +
          ((s1 : ℤ) - s2) ^ 2 + ((s1 : ℤ) - s3) ^ 2 + ((s1 : ℤ) - s4) ^ 2 +
          ((s2 : ℤ) - s3) ^ 2 + ((s2 : ℤ) - s4) ^ 2 + ((s3 : ℤ) - s4) ^ 2 := by ring
      have hnn : 0 ≤ ((s0 : ℤ) - s1) ^ 2 + ((s0 : ℤ) - s2) ^ 2 + ((s0 : ℤ) - s3) ^ 2 + ((s0 : ℤ) - s4) ^ 2 +
          ((s1 : ℤ) - s2) ^ 2 + ((s1 : ℤ) - s3) ^ 2 + ((s1 : ℤ) - s4) ^ 2 +
          ((s2 : ℤ) - s3) ^ 2 + ((s2 : ℤ) - s4) ^ 2 + ((s3 : ℤ) - s4) ^ 2 := by positivity
      linarith
    have h4n2 : 4 * (n : ℤ) ^ 2 ≤ 5 * ((s0 : ℤ) ^ 2 + s1 ^ 2 + s2 ^ 2 + s3 ^ 2 + s4 ^ 2) := by
      rw [htotz] at hcs; linarith
    have hkn : 5 * (k : ℤ) * (2 * (n : ℤ)) ≤ 5 * (n : ℤ) ^ 2 := by
      have : 0 ≤ 5 * (n : ℤ) * ((n : ℤ) - 2 * (k : ℤ)) := mul_nonneg (by linarith) (by linarith)
      linarith
    have hid2 : 5 * ((s0 : ℤ) * ((k : ℤ) - s0) + (s1 : ℤ) * ((k : ℤ) - s1) + (s2 : ℤ) * ((k : ℤ) - s2) +
        (s3 : ℤ) * ((k : ℤ) - s3) + (s4 : ℤ) * ((k : ℤ) - s4)) =
        5 * (k : ℤ) * ((s0 : ℤ) + s1 + s2 + s3 + s4) -
        5 * ((s0 : ℤ) ^ 2 + s1 ^ 2 + s2 ^ 2 + s3 ^ 2 + s4 ^ 2) := by ring
    rw [hid2, htotz]
    linarith
  exact hz

/-- Single-candidate pure-Nat stability bound for one of the 10 C_5 candidates. -/
lemma c5_stability_cand_bound {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Uc Zc Ua Za Ub Zb : Finset V} {n r : ℕ}
    (hd_UcZc : Disjoint Uc Zc) (hd_UcUa : Disjoint Uc Ua) (hd_UcZa : Disjoint Uc Za)
    (hd_UcUb : Disjoint Uc Ub) (hd_UcZb : Disjoint Uc Zb)
    (hd_ZcUa : Disjoint Zc Ua) (hd_ZcZa : Disjoint Zc Za)
    (hd_ZcUb : Disjoint Zc Ub) (hd_ZcZb : Disjoint Zc Zb)
    (hd_UaZa : Disjoint Ua Za) (hd_UaUb : Disjoint Ua Ub) (hd_UaZb : Disjoint Ua Zb)
    (hd_ZaUb : Disjoint Za Ub) (hd_ZaZb : Disjoint Za Zb) (hd_UbZb : Disjoint Ub Zb)
    (hUca_indep : ∀ x ∈ Uc ∪ Ua, ∀ y ∈ Uc ∪ Ua, ¬ G.Adj x y)
    (hUb_indep : ∀ x ∈ Ub, ∀ y ∈ Ub, ¬ G.Adj x y)
    (hUcb_nadj : ∀ x ∈ Uc, ∀ y ∈ Ub, ¬ G.Adj x y)
    (hr1 : 1 ≤ r) (hrK : r ≤ #(Ub ∪ Zb)) (hK2 : 2 ≤ #(Ub ∪ Zb))
    (hp_lo : 49 * #(Ub ∪ Zb) ≤ 100 * r) (hp_hi : 100 * r ≤ 51 * #(Ub ∪ Zb))
    (hbound : ∀ S ∈ (Ub ∪ Zb).powersetCard r,
      n ^ 2 < 50 * (G.induce (((Uc ∪ Zc) ∪ (Ua ∪ Za) ∪ S : Finset V) : Set V)).edgeSet.ncard) :
    4 * n ^ 2 +
      98 * ((#Za * #Ub - ∑ x ∈ Za, #(Ub.filter (G.Adj x))) +
            (#Ua * #Zb - ∑ y ∈ Zb, #(Ua.filter (G.Adj y)))) <
      200 * r * #(Ua ∪ Za) +
      100 * (2 * (∑ x ∈ Zc ∪ Za, #((Uc ∪ Ua).filter (G.Adj x))) +
             (∑ x ∈ Zc ∪ Za, #((Zc ∪ Za).filter (G.Adj x)))) +
      102 * ((∑ x ∈ Zc, #(Ub.filter (G.Adj x))) +
             (∑ y ∈ Zb, #(Uc.filter (G.Adj y))) +
             (∑ x ∈ Zc, #(Zb.filter (G.Adj x)))) +
      51 * (2 * (∑ y ∈ Zb, #(Ub.filter (G.Adj y))) +
            (∑ y ∈ Zb, #(Zb.filter (G.Adj y)))) := by
  let J : Finset V := (Uc ∪ Zc) ∪ (Ua ∪ Za)
  let K : Finset V := Ub ∪ Zb
  have hdisj_JK : Disjoint J K := by
    refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hd_UcUb, hd_UcZb⟩,
       Finset.disjoint_union_right.mpr ⟨hd_ZcUb, hd_ZcZb⟩⟩,
      Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hd_UaUb, hd_UaZb⟩,
       Finset.disjoint_union_right.mpr ⟨hd_ZaUb, hd_ZaZb⟩⟩⟩
  have havg := avg_union_ge_scaled G hdisj_JK hr1 hrK hK2 (T := n ^ 2 + 1) (fun S hS => by
    have hb := hbound S hS
    change n ^ 2 < 50 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard at hb
    omega)
  -- Rewrite dJ via J = (Uc ∪ Ua) ∪ (Zc ∪ Za)
  have hJ_eq : J = (Uc ∪ Ua) ∪ (Zc ∪ Za) := by
    ext x; simp only [J, Finset.mem_union]; tauto
  have hd_Uca_Zca : Disjoint (Uc ∪ Ua) (Zc ∪ Za) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hd_UcZc, hd_UcZa⟩,
      Finset.disjoint_union_right.mpr ⟨hd_ZcUa.symm, hd_UaZa⟩⟩
  have hdJ_eq : ∑ u ∈ J, #(J.filter (G.Adj u)) =
      2 * (∑ x ∈ Zc ∪ Za, #((Uc ∪ Ua).filter (G.Adj x))) +
      (∑ x ∈ Zc ∪ Za, #((Zc ∪ Za).filter (G.Adj x))) := by
    rw [hJ_eq]
    exact sum_adj_union_indep G hd_Uca_Zca hUca_indep
  -- Rewrite dK via K = Ub ∪ Zb
  have hdK_eq : ∑ u ∈ K, #(K.filter (G.Adj u)) =
      2 * (∑ y ∈ Zb, #(Ub.filter (G.Adj y))) + (∑ y ∈ Zb, #(Zb.filter (G.Adj y))) :=
    sum_adj_union_indep G hd_UbZb hUb_indep
  -- Decompose eJK = ∑ w ∈ K, #(J.filter (G.Adj w))
  have hswap : ∀ A B : Finset V, ∑ w ∈ B, #(A.filter (G.Adj w)) = ∑ u ∈ A, #(B.filter (G.Adj u)) := by
    intro A B
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro w _
    simp [G.adj_comm]
  have heJK_eq : ∑ w ∈ K, #(J.filter (G.Adj w)) =
      (∑ x ∈ Uc, #(Ub.filter (G.Adj x))) + (∑ x ∈ Zc, #(Ub.filter (G.Adj x))) +
      (∑ x ∈ Ua, #(Ub.filter (G.Adj x))) + (∑ x ∈ Za, #(Ub.filter (G.Adj x))) +
      (∑ y ∈ Zb, #(Uc.filter (G.Adj y))) + (∑ x ∈ Zc, #(Zb.filter (G.Adj x))) +
      (∑ y ∈ Zb, #(Ua.filter (G.Adj y))) + (∑ x ∈ Za, #(Zb.filter (G.Adj x))) := by
    have hsplitJ : ∀ w, #(J.filter (G.Adj w)) =
        #(Uc.filter (G.Adj w)) + #(Zc.filter (G.Adj w)) +
        #(Ua.filter (G.Adj w)) + #(Za.filter (G.Adj w)) := by
      intro w
      have h1 : Disjoint (Uc ∪ Zc) (Ua ∪ Za) :=
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hd_UcUa, hd_UcZa⟩,
          Finset.disjoint_union_right.mpr ⟨hd_ZcUa, hd_ZcZa⟩⟩
      simp only [J, Finset.filter_union]
      rw [Finset.card_union_of_disjoint (h1.mono
            (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _))
            (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _))),
        Finset.card_union_of_disjoint (hd_UcZc.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        Finset.card_union_of_disjoint (hd_UaZa.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      omega
    simp_rw [hsplitJ]
    rw [Finset.sum_union hd_UbZb]
    simp_rw [Finset.sum_add_distrib]
    rw [hswap Uc Ub, hswap Zc Ub, hswap Ua Ub, hswap Za Ub, hswap Zc Zb, hswap Za Zb]
    omega
  have heUcUb : ∑ x ∈ Uc, #(Ub.filter (G.Adj x)) = 0 := by
    apply Finset.sum_eq_zero; intro x hx
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun y hy => hUcb_nadj x hx y hy
  have hle_UaUb : ∑ x ∈ Ua, #(Ub.filter (G.Adj x)) ≤ #Ua * #Ub := by
    calc _ ≤ ∑ _x ∈ Ua, #Ub := Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
      _ = #Ua * #Ub := by rw [Finset.sum_const, smul_eq_mul]
  have hle_ZaUb : ∑ x ∈ Za, #(Ub.filter (G.Adj x)) ≤ #Za * #Ub := by
    calc _ ≤ ∑ _x ∈ Za, #Ub := Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
      _ = #Za * #Ub := by rw [Finset.sum_const, smul_eq_mul]
  have hle_UaZb : ∑ y ∈ Zb, #(Ua.filter (G.Adj y)) ≤ #Ua * #Zb := by
    calc _ ≤ ∑ _y ∈ Zb, #Ua := Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
      _ = #Zb * #Ua := by rw [Finset.sum_const, smul_eq_mul]
      _ = #Ua * #Zb := mul_comm _ _
  have hle_ZaZb : ∑ x ∈ Za, #(Zb.filter (G.Adj x)) ≤ #Za * #Zb := by
    calc _ ≤ ∑ _x ∈ Za, #Zb := Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
      _ = #Za * #Zb := by rw [Finset.sum_const, smul_eq_mul]
  set DEF := (#Za * #Ub - ∑ x ∈ Za, #(Ub.filter (G.Adj x))) + (#Ua * #Zb - ∑ y ∈ Zb, #(Ua.filter (G.Adj y)))
  set ERR := (∑ x ∈ Zc, #(Ub.filter (G.Adj x))) + (∑ y ∈ Zb, #(Uc.filter (G.Adj y))) +
      (∑ x ∈ Zc, #(Zb.filter (G.Adj x)))
  set dJ := 2 * (∑ x ∈ Zc ∪ Za, #((Uc ∪ Ua).filter (G.Adj x))) +
      (∑ x ∈ Zc ∪ Za, #((Zc ∪ Za).filter (G.Adj x)))
  set dK := 2 * (∑ y ∈ Zb, #(Ub.filter (G.Adj y))) + (∑ y ∈ Zb, #(Zb.filter (G.Adj y)))
  have hcard_Wa : #(Ua ∪ Za) = #Ua + #Za := Finset.card_union_of_disjoint hd_UaZa
  have hcard_K : #K = #Ub + #Zb := Finset.card_union_of_disjoint hd_UbZb
  have heJK_bound : (∑ w ∈ K, #(J.filter (G.Adj w))) + DEF ≤ #(Ua ∪ Za) * #K + ERR := by
    have hprod : #(Ua ∪ Za) * #K = #Ua * #Ub + #Za * #Ub + #Ua * #Zb + #Za * #Zb := by
      rw [hcard_Wa, hcard_K]; ring
    omega
  rw [hdJ_eq, hdK_eq] at havg
  change 2 ≤ #K at hK2
  change 49 * #K ≤ 100 * r at hp_lo
  change 100 * r ≤ 51 * #K at hp_hi
  -- Scale by 100 and factor out 25 * #K
  have hscaled : 25 * #K * (4 * n ^ 2 + 98 * DEF) <
      25 * #K * (200 * r * #(Ua ∪ Za) + 100 * dJ + 102 * ERR + 51 * dK) := by
    have h1 : 100 * ((n ^ 2 + 1) * #K) ≤ 100 * (25 * (#K * dJ + 2 * r * (∑ w ∈ K, #(J.filter (G.Adj w))) + r * dK)) :=
      Nat.mul_le_mul_left 100 havg
    have h2 : 25 * #K * (4 * n ^ 2 + 98 * DEF) < 100 * ((n ^ 2 + 1) * #K) + 25 * (200 * r * DEF) := by
      have hKpos : 0 < #K := by omega
      have hdef_le : 25 * #K * (98 * DEF) ≤ 25 * (200 * r * DEF) := by
        have h98 : 98 * #K ≤ 200 * r := by omega
        calc 25 * #K * (98 * DEF) = 25 * (98 * #K * DEF) := by ring
          _ ≤ 25 * (200 * r * DEF) := Nat.mul_le_mul_left 25 (Nat.mul_le_mul_right DEF h98)
      have hn1 : 25 * #K * (4 * n ^ 2) < 100 * ((n ^ 2 + 1) * #K) := by
        have : 100 * ((n ^ 2 + 1) * #K) = 25 * #K * (4 * n ^ 2) + 100 * #K := by ring
        omega
      have hmul_add : 25 * #K * (4 * n ^ 2 + 98 * DEF) = 25 * #K * (4 * n ^ 2) + 25 * #K * (98 * DEF) := by ring
      omega
    have h3 : 100 * (25 * (#K * dJ + 2 * r * (∑ w ∈ K, #(J.filter (G.Adj w))) + r * dK)) + 25 * (200 * r * DEF) =
        25 * (100 * #K * dJ + 200 * r * ((∑ w ∈ K, #(J.filter (G.Adj w))) + DEF) + 100 * r * dK) := by ring
    have h4 : 200 * r * ((∑ w ∈ K, #(J.filter (G.Adj w))) + DEF) ≤
        200 * r * (#(Ua ∪ Za) * #K + ERR) := Nat.mul_le_mul_left _ heJK_bound
    have h5 : 200 * r * ERR ≤ 102 * #K * ERR := Nat.mul_le_mul_right ERR (by omega)
    have h6 : 100 * r * dK ≤ 51 * #K * dK := Nat.mul_le_mul_right dK (by omega)
    have h7 : 25 * (100 * #K * dJ + 200 * r * (#(Ua ∪ Za) * #K) + 102 * #K * ERR + 51 * #K * dK) =
        25 * #K * (200 * r * #(Ua ∪ Za) + 100 * dJ + 102 * ERR + 51 * dK) := by ring
    have h8 : 200 * r * (#(Ua ∪ Za) * #K + ERR) = 200 * r * (#(Ua ∪ Za) * #K) + 200 * r * ERR := by ring
    omega
  exact Nat.lt_of_mul_lt_mul_left hscaled

set_option maxHeartbeats 800000 in
/-- Theorem F (Norin-Yepremyan 2015 C_5-stability, elementary all-finite-n proof):
    Every triangle-free counterexample satisfies 500000 * e(G) < 99999 * n^2. -/
theorem five_hundred_thousand_mul_edges_lt {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 := by
  classical
  by_contra hge
  push Not at hge
  set n := Fintype.card V
  set m := G.edgeSet.ncard
  have hn12 : 12 ≤ n := twelve_le_card G hTF hH
  have h5d : ∀ v : V, 5 * G.degree v < 2 * n := by
    intro v
    have hv := five_mul_deg_lt_two_mul_card G hTF hH v
    have hdeq : G.degree v = (G.neighborSet v).ncard := by
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
    omega
  have h2m : 2 * m = ∑ v : V, G.degree v := by
    have h1 : m = #G.edgeFinset := by
      change G.edgeSet.ncard = #G.edgeFinset
      rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  -- Step 1: Partition V into low-degree Z (< 19n/50) and high-degree U (>= 19n/50); show 5000 * #Z <= n
  let Z : Finset V := Finset.univ.filter (fun v => 50 * G.degree v < 19 * n)
  let U : Finset V := Finset.univ.filter (fun v => 19 * n ≤ 50 * G.degree v)
  have hdisj_ZU : Disjoint Z U := by
    rw [Finset.disjoint_left]; intro v hvZ hvU
    have h1 := (Finset.mem_filter.mp hvZ).2; have h2 := (Finset.mem_filter.mp hvU).2; omega
  have hunion_ZU : Z ∪ U = Finset.univ := by
    ext v; simp only [Z, U, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega
  have hcard_ZU : #Z + #U = n := by
    rw [← Finset.card_union_of_disjoint hdisj_ZU, hunion_ZU, Finset.card_univ]
  have h5000Z : 5000 * #Z ≤ n := by
    have hdef_sum : ∑ v : V, (20 * n - 50 * G.degree v) = 20 * n ^ 2 - 100 * m := by
      have hle_each : ∀ v ∈ (Finset.univ : Finset V), 50 * G.degree v ≤ 20 * n := fun v _ => by
        have := h5d v; omega
      have h1 : (∑ v : V, (20 * n - 50 * G.degree v)) + (∑ v : V, 50 * G.degree v) = ∑ _v : V, 20 * n := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun v hv => Nat.sub_add_cancel (hle_each v hv))
      have h2 : ∑ v : V, 50 * G.degree v = 100 * m := by rw [← Finset.mul_sum, ← h2m]; ring
      have h3 : ∑ _v : V, 20 * n = 20 * n ^ 2 := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring
      omega
    have hZ_le : #Z * n ≤ ∑ v : V, (20 * n - 50 * G.degree v) := by
      calc #Z * n = ∑ _v ∈ Z, n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ v ∈ Z, (20 * n - 50 * G.degree v) := Finset.sum_le_sum (fun v hv => by
            have := (Finset.mem_filter.mp hv).2; omega)
        _ ≤ ∑ v : V, (20 * n - 50 * G.degree v) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ Z)
    have hmul : 5000 * #Z * n ≤ n * n := by
      have : 5000 * (20 * n ^ 2 - 100 * m) ≤ n * n := by
        have h1 : 100 * m ≤ 20 * n ^ 2 := by
          have h5m := five_mul_edges_lt_sq G hTF hH
          change 5 * m < n ^ 2 at h5m
          omega
        have h2 : 5000 * (20 * n ^ 2 - 100 * m) = 100000 * n ^ 2 - 500000 * m := by
          zify [h1, show 500000 * m ≤ 100000 * n ^ 2 by omega]; ring
        have h3 : n * n = n ^ 2 := by ring
        omega
      have h4 : 5000 * (#Z * n) ≤ 5000 * (20 * n ^ 2 - 100 * m) := Nat.mul_le_mul_left 5000 (by omega)
      have h5 : 5000 * #Z * n = 5000 * (#Z * n) := by ring
      omega
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  -- Step 2: Apply Häggkvist (Theorem E) to H = G.induce U -> C_5 homomorphism clsU
  let H : SimpleGraph (U : Set V) := G.induce (U : Set V)
  have hH_TF : H.CliqueFree 3 := by
    intro s hs
    apply hTF (s.map (Function.Embedding.subtype (· ∈ (U : Set V))))
    refine ⟨?_, by rw [Finset.card_map]; exact hs.2⟩
    intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coe_subtype] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    exact hs.1 hx' hy' hne
  have hH_nonbip : ¬ H.Colorable 2 := by
    rintro ⟨col⟩
    let C0 : Set V := {v | ∃ hv : v ∈ U, col ⟨v, hv⟩ = 0}
    let C1 : Set V := {v | ∃ hv : v ∈ U, col ⟨v, hv⟩ = 1}
    have hC0 : G.IsIndepSet C0 := by
      rintro x ⟨hxU, hx0⟩ y ⟨hyU, hy0⟩ _ hxy
      exact col.valid (show H.Adj ⟨x, hxU⟩ ⟨y, hyU⟩ from hxy) (hx0.trans hy0.symm)
    have hC1 : G.IsIndepSet C1 := by
      rintro x ⟨hxU, hx1⟩ y ⟨hyU, hy1⟩ _ hxy
      exact col.valid (show H.Adj ⟨x, hxU⟩ ⟨y, hyU⟩ from hxy) (hx1.trans hy1.symm)
    have h50 := five_mul_indep_lt_two_mul_card G hTF hH C0 hC0
    have h51 := five_mul_indep_lt_two_mul_card G hTF hH C1 hC1
    have hsumU : C0.ncard + C1.ncard = #U := by
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
      have hdisj : Disjoint C0.toFinset C1.toFinset := by
        rw [Finset.disjoint_left]; intro v hv0 hv1
        have ⟨h0U, h0⟩ : ∃ hv : v ∈ U, col ⟨v, hv⟩ = 0 := by simpa [C0] using hv0
        have ⟨_, h1⟩ : ∃ hv : v ∈ U, col ⟨v, hv⟩ = 1 := by simpa [C1] using hv1
        have : (0 : Fin 2) = 1 := h0.symm.trans h1
        exact absurd this (by decide)
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1; ext v
      simp only [Finset.mem_union, Set.mem_toFinset, C0, C1]
      change (∃ hv : v ∈ U, col ⟨v, hv⟩ = 0) ∨ (∃ hv : v ∈ U, col ⟨v, hv⟩ = 1) ↔ v ∈ U
      constructor
      · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
      · intro hv
        cases hcv : col ⟨v, hv⟩ with
        | mk val hlt =>
          have : val = 0 ∨ val = 1 := by omega
          rcases this with rfl | rfl
          · exact Or.inl ⟨hv, hcv⟩
          · exact Or.inr ⟨hv, hcv⟩
    omega
  have hH_8d : ∀ u : (U : Set V), 3 * Fintype.card (U : Set V) < 8 * (H.neighborSet u).ncard := by
    intro u
    have hcardU : Fintype.card (U : Set V) = #U := by simp
    have hdegU : (H.neighborSet u).ncard = #(U.filter (G.Adj u.val)) := by
      rw [Set.ncard_eq_toFinset_card']
      refine Finset.card_bij (fun w _ => w.val) ?_ ?_ ?_
      · intro w hw
        have hw' : G.Adj u.val w.val := by simpa [H] using hw
        exact Finset.mem_filter.mpr ⟨w.property, hw'⟩
      · intro w1 _ w2 _ heq; exact Subtype.ext heq
      · intro w hw
        have hw' := Finset.mem_filter.mp hw
        exact ⟨⟨w, hw'.1⟩, by simpa [H] using hw'.2, rfl⟩
    have hsub : G.neighborFinset u.val ⊆ U.filter (G.Adj u.val) ∪ Z := by
      intro w hw
      have hadj := (SimpleGraph.mem_neighborFinset G u.val w).mp hw
      by_cases hwU : w ∈ U
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwU, hadj⟩)
      · have hwZ : w ∈ Z := by
          have : w ∈ Z ∪ U := by rw [hunion_ZU]; exact Finset.mem_univ w
          exact (Finset.mem_union.mp this).resolve_right hwU
        exact Finset.mem_union_right _ hwZ
    have hdeg_le : G.degree u.val ≤ #(U.filter (G.Adj u.val)) + #Z :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have huU : 19 * n ≤ 50 * G.degree u.val := (Finset.mem_filter.mp u.property).2
    rw [hcardU, hdegU]
    omega
  obtain ⟨clsU, hclsU⟩ := haggkvist_hom_c5 H hH_TF hH_nonbip hH_8d
  let Upart : Fin 5 → Finset V := fun j => U.filter (fun v => ∃ hv : v ∈ U, clsU ⟨v, hv⟩ = j)
  have hUpart_sub : ∀ j : Fin 5, Upart j ⊆ U := fun j => Finset.filter_subset _ _
  have hUpart_disj : ∀ i j : Fin 5, i ≠ j → Disjoint (Upart i) (Upart j) := by
    intro i j hij
    rw [Finset.disjoint_left]; intro v hvi hvj
    obtain ⟨hvU, hi⟩ := (Finset.mem_filter.mp hvi).2
    obtain ⟨_, hj⟩ := (Finset.mem_filter.mp hvj).2
    exact hij (hi.symm.trans hj)
  have hUpart_biUnion : Finset.univ.biUnion Upart = U := by
    ext v; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Upart, Finset.mem_filter]
    constructor
    · rintro ⟨_, hv, _⟩; exact hv
    · intro hv; exact ⟨clsU ⟨v, hv⟩, hv, hv, rfl⟩
  have hUpart_sum : ∑ j : Fin 5, #(Upart j) = #U := by
    rw [← Finset.card_biUnion (fun i _ j _ hij => hUpart_disj i j hij), hUpart_biUnion]
  have hUpart_adj : ∀ i j : Fin 5, ∀ u ∈ Upart i, ∀ v ∈ Upart j, G.Adj u v → j = i + 1 ∨ j = i + 4 := by
    intro i j u hu v hv huv
    obtain ⟨huU, hci⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨hvU, hcj⟩ := (Finset.mem_filter.mp hv).2
    have := hclsU ⟨u, huU⟩ ⟨v, hvU⟩ huv
    rwa [hci, hcj] at this
  have hUpart_nadj : ∀ i j : Fin 5, j ≠ i + 1 → j ≠ i + 4 → ∀ u ∈ Upart i, ∀ v ∈ Upart j, ¬ G.Adj u v := by
    intro i j h1 h4 u hu v hv huv
    rcases hUpart_adj i j u hu v hv huv with rfl | rfl
    · exact h1 rfl
    · exact h4 rfl
  have hUpart_pair_indep : ∀ i : Fin 5, ∀ x ∈ Upart i ∪ Upart (i + 2), ∀ y ∈ Upart i ∪ Upart (i + 2), ¬ G.Adj x y := by
    intro i x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · exact hUpart_nadj i i (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h) x hx y hy hxy
    · exact hUpart_nadj i (i + 2) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h) x hx y hy hxy
    · exact hUpart_nadj (i + 2) i (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h) x hx y hy hxy
    · exact hUpart_nadj (i + 2) (i + 2) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h) x hx y hy hxy
  -- Step 3: #Z >= 1, hence n >= 5000
  have hZ_pos : 1 ≤ #Z := by
    by_contra hZ0
    have hZ_eq : #Z = 0 := by omega
    have hU_eq : U = Finset.univ := by
      have hZe : Z = ∅ := Finset.card_eq_zero.mp hZ_eq
      rw [hZe, Finset.empty_union] at hunion_ZU; exact hunion_ZU
    have hmemU : ∀ v : V, v ∈ U := fun v => by rw [hU_eq]; exact Finset.mem_univ v
    exact not_hom_c5_of_counterexample G hTF hH (fun v => clsU ⟨v, hmemU v⟩)
      (fun u v huv => hclsU ⟨u, hmemU u⟩ ⟨v, hmemU v⟩ huv)
  have hn5000 : 5000 ≤ n := by omega
  -- Step 4: Part-size bounds on Upart j
  have hUpair_lt : ∀ i : Fin 5, 5 * (#(Upart i) + #(Upart (i + 2))) < 2 * n := by
    intro i
    have h5 := five_mul_indep_lt_two_mul_card G hTF hH ((Upart i ∪ Upart (i + 2) : Finset V) : Set V)
      (fun x hx y hy _ hxy => hUpart_pair_indep i x hx y hy hxy)
    rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint
      (hUpart_disj i (i + 2) (by intro h; fin_cases i <;> simp at h))] at h5
    exact h5
  have hU_sum5 : ∀ i : Fin 5, #(Upart i) + #(Upart (i + 1)) + #(Upart (i + 2)) + #(Upart (i + 3)) + #(Upart (i + 4)) = #U := by
    intro i
    rw [← hUpart_sum]
    fin_cases i <;> simp [Fin.sum_univ_five] <;> omega
  have hU_lo : ∀ i : Fin 5, n < 5 * #(Upart i) + 5 * #Z := by
    intro i
    have h1 := hUpair_lt (i + 1)
    have h2 := hUpair_lt (i + 2)
    have hs := hU_sum5 i
    rw [show i + 1 + 2 = i + 3 by fin_cases i <;> rfl] at h1
    rw [show i + 2 + 2 = i + 4 by fin_cases i <;> rfl] at h2
    omega
  have hU_hi : ∀ i : Fin 5, 5 * #(Upart i) < n + 5 * #Z := by
    intro i
    have h1 := hUpair_lt i
    have h2 := hU_lo (i + 2)
    omega
  -- Step 5: Missing C_5-edges bound: 500000 * M <= n^2
  set eU := ∑ i : Fin 5, ∑ u ∈ Upart i, #((Upart (i + 1)).filter (G.Adj u))
  have heU_le_prod : eU ≤ ∑ i : Fin 5, #(Upart i) * #(Upart (i + 1)) := by
    apply Finset.sum_le_sum; intro i _
    calc ∑ u ∈ Upart i, #((Upart (i + 1)).filter (G.Adj u))
        ≤ ∑ _u ∈ Upart i, #(Upart (i + 1)) :=
          Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
      _ = #(Upart i) * #(Upart (i + 1)) := by rw [Finset.sum_const, smul_eq_mul]
  set M := (∑ i : Fin 5, #(Upart i) * #(Upart (i + 1))) - eU
  have h2eU : 2 * eU = ∑ u ∈ U, #(U.filter (G.Adj u)) := by
    have hU_adj_split : ∀ i : Fin 5, ∀ u ∈ Upart i,
        #(U.filter (G.Adj u)) = #((Upart (i + 1)).filter (G.Adj u)) + #((Upart (i + 4)).filter (G.Adj u)) := by
      intro i u hu
      have hd : Disjoint ((Upart (i + 1)).filter (G.Adj u)) ((Upart (i + 4)).filter (G.Adj u)) :=
        (hUpart_disj (i + 1) (i + 4) (by intro h; fin_cases i <;> simp at h)).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      rw [← Finset.card_union_of_disjoint hd]
      congr 1; ext v
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hvU, huv⟩
        have hvB : v ∈ Finset.univ.biUnion Upart := by rwa [hUpart_biUnion]
        obtain ⟨j, -, hvj⟩ := Finset.mem_biUnion.mp hvB
        rcases hUpart_adj i j u hu v hvj huv with rfl | rfl
        · exact Or.inl ⟨hvj, huv⟩
        · exact Or.inr ⟨hvj, huv⟩
      · rintro (⟨hv, huv⟩ | ⟨hv, huv⟩)
        · exact ⟨hUpart_sub _ hv, huv⟩
        · exact ⟨hUpart_sub _ hv, huv⟩
    have hsum1 : ∑ u ∈ U, #(U.filter (G.Adj u)) =
        ∑ i : Fin 5, ∑ u ∈ Upart i, #(U.filter (G.Adj u)) := by
      rw [← hUpart_biUnion, Finset.sum_biUnion (fun i _ j _ hij => hUpart_disj i j hij)]
    rw [hsum1]
    have hsum2 : ∑ i : Fin 5, ∑ u ∈ Upart i, #(U.filter (G.Adj u)) =
        (∑ i : Fin 5, ∑ u ∈ Upart i, #((Upart (i + 1)).filter (G.Adj u))) +
        (∑ i : Fin 5, ∑ u ∈ Upart i, #((Upart (i + 4)).filter (G.Adj u))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun u hu => hU_adj_split i u hu)
    have hsum4 : ∑ i : Fin 5, ∑ u ∈ Upart i, #((Upart (i + 4)).filter (G.Adj u)) = eU := by
      have hswap : ∀ i : Fin 5, ∑ u ∈ Upart i, #((Upart (i + 4)).filter (G.Adj u)) =
          ∑ v ∈ Upart (i + 4), #((Upart i).filter (G.Adj v)) := by
        intro i
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro v _
        apply Finset.sum_congr rfl; intro u _; simp [G.adj_comm]
      simp_rw [hswap]
      refine Fintype.sum_equiv (Equiv.addRight (4 : Fin 5)) _ _ (fun i => ?_)
      simp [show i + 4 + 1 = i by fin_cases i <;> rfl]
    rw [hsum2, hsum4]; omega
  have h50m_le : 50 * m ≤ 50 * eU + 19 * #Z * n := by
    have h2m_split : 2 * m = (∑ u ∈ U, #(U.filter (G.Adj u))) +
        2 * (∑ x ∈ Z, #(U.filter (G.Adj x))) + (∑ x ∈ Z, #(Z.filter (G.Adj x))) := by
      have h1 : 2 * m = ∑ u ∈ U ∪ Z, #((U ∪ Z).filter (G.Adj u)) := by
        rw [Finset.union_comm, hunion_ZU, h2m]
        apply Finset.sum_congr rfl; intro u _
        rw [SimpleGraph.degree]; congr 1; ext v; simp
      rw [h1, sum_adj_union G hdisj_ZU.symm]
    have hZdeg_sum : (∑ x ∈ Z, #(U.filter (G.Adj x))) + (∑ x ∈ Z, #(Z.filter (G.Adj x))) =
        ∑ x ∈ Z, G.degree x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.card_union_of_disjoint (hdisj_ZU.symm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        ← Finset.filter_union, Finset.union_comm, hunion_ZU, SimpleGraph.degree]
      congr 1; ext v; simp
    have h50Zdeg : 50 * ∑ x ∈ Z, G.degree x ≤ 19 * #Z * n := by
      rw [Finset.mul_sum]
      calc ∑ x ∈ Z, 50 * G.degree x ≤ ∑ _x ∈ Z, 19 * n :=
            Finset.sum_le_sum (fun x hx => by have := (Finset.mem_filter.mp hx).2; omega)
        _ = 19 * #Z * n := by rw [Finset.sum_const, smul_eq_mul]; ring
    omega
  have hM_bound : 500000 * M ≤ n ^ 2 := by
    have hprod50 : 50 * (eU + M) ≤ 10 * #U ^ 2 + 10 * (6 * #Z) ^ 2 := by
      have h1 : eU + M = ∑ i : Fin 5, #(Upart i) * #(Upart (i + 1)) := by omega
      rw [h1]
      exact c5_adj_sum_le (fun i => #(Upart i)) #U (6 * #Z) hUpart_sum (fun i => by
        have hlo := hU_lo i; have hhi := hU_hi i; omega)
    have hprod_z : 50 * (eU + M) + 20 * #Z * n ≤ 10 * n ^ 2 + 370 * #Z ^ 2 := by
      have h1 : 10 * #U ^ 2 + 20 * #Z * n = 10 * n ^ 2 + 10 * #Z ^ 2 := by
        have hUeq : #U = n - #Z := by omega
        zify [show #Z ≤ n by omega]; rw [hUeq]; push_cast [Nat.cast_sub (show #Z ≤ n by omega)]; ring
      have h2 : 10 * (6 * #Z) ^ 2 = 360 * #Z ^ 2 := by ring
      omega
    have h370 : 370 * #Z ^ 2 ≤ #Z * n := by
      have h1 : 370 * #Z ^ 2 ≤ 5000 * #Z ^ 2 := by nlinarith
      have h2 : 5000 * #Z ^ 2 = (5000 * #Z) * #Z := by ring
      have h3 : (5000 * #Z) * #Z ≤ n * #Z := Nat.mul_le_mul_right #Z h5000Z
      have h4 : n * #Z = #Z * n := mul_comm _ _
      omega
    have hdist : 50 * (eU + M) = 50 * eU + 50 * M := by ring
    have h19 : 19 * #Z * n = 19 * (#Z * n) := by ring
    have h20 : 20 * #Z * n = 20 * (#Z * n) := by ring
    omega
  -- Step 6: Canonical assignment cZ : V -> Fin 5 on Z
  have hprod_M : ∀ x ∈ Z, ∀ i : Fin 5,
      #((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x)) ≤ M := by
    intro x _ i
    have hmiss_i : #((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x)) +
        ∑ u ∈ Upart i, #((Upart (i + 1)).filter (G.Adj u)) ≤ #(Upart i) * #(Upart (i + 1)) := by
      have hsum_non : ∀ u ∈ Upart i, #((Upart (i + 1)).filter (G.Adj u)) +
          #((Upart (i + 1)).filter (fun v => ¬ G.Adj u v)) = #(Upart (i + 1)) :=
        fun u _ => Finset.card_filter_add_card_filter_not _
      have htot : (∑ u ∈ Upart i, #((Upart (i + 1)).filter (G.Adj u))) +
          (∑ u ∈ Upart i, #((Upart (i + 1)).filter (fun v => ¬ G.Adj u v))) = #(Upart i) * #(Upart (i + 1)) := by
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsum_non, Finset.sum_const, smul_eq_mul]
      have hge_non : #((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x)) ≤
          ∑ u ∈ Upart i, #((Upart (i + 1)).filter (fun v => ¬ G.Adj u v)) := by
        calc #((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x))
            = ∑ _u ∈ (Upart i).filter (G.Adj x), #((Upart (i + 1)).filter (G.Adj x)) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ u ∈ (Upart i).filter (G.Adj x), #((Upart (i + 1)).filter (fun v => ¬ G.Adj u v)) := by
              apply Finset.sum_le_sum; intro u hu
              apply Finset.card_le_card; intro v hv
              have hu' := Finset.mem_filter.mp hu
              have hv' := Finset.mem_filter.mp hv
              exact Finset.mem_filter.mpr ⟨hv'.1, fun huv => not_adj_of_cliqueFree_three hTF hu'.2 huv hv'.2⟩
          _ ≤ ∑ u ∈ Upart i, #((Upart (i + 1)).filter (fun v => ¬ G.Adj u v)) :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      omega
    have hM_ge_i : #(Upart i) * #(Upart (i + 1)) - ∑ u ∈ Upart i, #((Upart (i + 1)).filter (G.Adj u)) ≤ M := by
      have hsingle : ∀ j : Fin 5, ∑ u ∈ Upart j, #((Upart (j + 1)).filter (G.Adj u)) ≤ #(Upart j) * #(Upart (j + 1)) := by
        intro j
        calc _ ≤ ∑ _u ∈ Upart j, #(Upart (j + 1)) :=
              Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
          _ = #(Upart j) * #(Upart (j + 1)) := by rw [Finset.sum_const, smul_eq_mul]
      have hdiff : ∑ j : Fin 5, (#(Upart j) * #(Upart (j + 1)) -
          ∑ u ∈ Upart j, #((Upart (j + 1)).filter (G.Adj u))) = M := by
        have hadd : (∑ j : Fin 5, (#(Upart j) * #(Upart (j + 1)) -
            ∑ u ∈ Upart j, #((Upart (j + 1)).filter (G.Adj u)))) + eU =
            ∑ j : Fin 5, #(Upart j) * #(Upart (j + 1)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hsingle j))
        omega
      rw [← hdiff]
      exact Finset.single_le_sum
        (f := fun j : Fin 5 => #(Upart j) * #(Upart (j + 1)) - ∑ u ∈ Upart j, #((Upart (j + 1)).filter (G.Adj u)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hno_adj_big : ∀ x ∈ Z, ∀ i : Fin 5,
      ¬ (n < 700 * #((Upart i).filter (G.Adj x)) ∧ n < 700 * #((Upart (i + 1)).filter (G.Adj x))) := by
    intro x hx i ⟨h1, h2⟩
    have hp := hprod_M x hx i
    have hmul : n * n < (700 * #((Upart i).filter (G.Adj x))) * (700 * #((Upart (i + 1)).filter (G.Adj x))) :=
      Nat.mul_lt_mul_of_lt_of_lt h1 h2
    have h49 : (700 * #((Upart i).filter (G.Adj x))) * (700 * #((Upart (i + 1)).filter (G.Adj x))) =
        490000 * (#((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x))) := by ring
    have hle : 490000 * (#((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x))) ≤ 500000 * M := by
      have h1' : 490000 * (#((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x))) ≤
          500000 * (#((Upart i).filter (G.Adj x)) * #((Upart (i + 1)).filter (G.Adj x))) :=
        Nat.mul_le_mul_right _ (by omega)
      exact h1'.trans (Nat.mul_le_mul_left 500000 hp)
    have hsq : n * n = n ^ 2 := by ring
    omega
  have hex_cZ : ∀ x ∈ Z, ∃ c : Fin 5, ∀ j : Fin 5, j ≠ c + 4 → j ≠ c + 1 →
      700 * #((Upart j).filter (G.Adj x)) ≤ n := by
    intro x hxZ
    have hna := hno_adj_big x hxZ
    have hj5 : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by intro j; fin_cases j <;> decide
    by_cases h0 : n < 700 * #((Upart 0).filter (G.Adj x))
    · have h1 : ¬ n < 700 * #((Upart 1).filter (G.Adj x)) := fun h => hna 0 ⟨h0, h⟩
      have h4 : ¬ n < 700 * #((Upart 4).filter (G.Adj x)) := fun h => hna 4 ⟨h, by simpa using h0⟩
      by_cases h2 : n < 700 * #((Upart 2).filter (G.Adj x))
      · have h3 : ¬ n < 700 * #((Upart 3).filter (G.Adj x)) := fun h => hna 2 ⟨h2, h⟩
        refine ⟨1, fun j hj4 hj1 => ?_⟩
        rcases hj5 j with rfl | rfl | rfl | rfl | rfl <;> first | exact (hj4 rfl).elim | exact (hj1 rfl).elim | omega
      · refine ⟨4, fun j hj4 hj1 => ?_⟩
        rcases hj5 j with rfl | rfl | rfl | rfl | rfl <;> first | exact (hj4 rfl).elim | exact (hj1 rfl).elim | omega
    · by_cases h1 : n < 700 * #((Upart 1).filter (G.Adj x))
      · have h2 : ¬ n < 700 * #((Upart 2).filter (G.Adj x)) := fun h => hna 1 ⟨h1, h⟩
        by_cases h3 : n < 700 * #((Upart 3).filter (G.Adj x))
        · have h4 : ¬ n < 700 * #((Upart 4).filter (G.Adj x)) := fun h => hna 3 ⟨h3, h⟩
          refine ⟨2, fun j hj4 hj1 => ?_⟩
          rcases hj5 j with rfl | rfl | rfl | rfl | rfl <;> first | exact (hj4 rfl).elim | exact (hj1 rfl).elim | omega
        · refine ⟨0, fun j hj4 hj1 => ?_⟩
          rcases hj5 j with rfl | rfl | rfl | rfl | rfl <;> first | exact (hj4 rfl).elim | exact (hj1 rfl).elim | omega
      · by_cases h2 : n < 700 * #((Upart 2).filter (G.Adj x))
        · have h3 : ¬ n < 700 * #((Upart 3).filter (G.Adj x)) := fun h => hna 2 ⟨h2, h⟩
          refine ⟨3, fun j hj4 hj1 => ?_⟩
          rcases hj5 j with rfl | rfl | rfl | rfl | rfl <;> first | exact (hj4 rfl).elim | exact (hj1 rfl).elim | omega
        · by_cases h3 : n < 700 * #((Upart 3).filter (G.Adj x))
          · have h4 : ¬ n < 700 * #((Upart 4).filter (G.Adj x)) := fun h => hna 3 ⟨h3, h⟩
            refine ⟨4, fun j hj4 hj1 => ?_⟩
            rcases hj5 j with rfl | rfl | rfl | rfl | rfl <;> first | exact (hj4 rfl).elim | exact (hj1 rfl).elim | omega
          · refine ⟨0, fun j hj4 hj1 => ?_⟩
            rcases hj5 j with rfl | rfl | rfl | rfl | rfl <;> first | exact (hj4 rfl).elim | exact (hj1 rfl).elim | omega
  let cZ : V → Fin 5 := fun x => if hx : x ∈ Z then (hex_cZ x hx).choose else 0
  have hcZ : ∀ x (hx : x ∈ Z), ∀ j : Fin 5, j ≠ cZ x + 4 → j ≠ cZ x + 1 →
      700 * #((Upart j).filter (G.Adj x)) ≤ n := by
    intro x hx
    simpa [cZ, hx] using (hex_cZ x hx).choose_spec
  let Zpart : Fin 5 → Finset V := fun j => Z.filter (fun x => cZ x = j)
  let Wpart : Fin 5 → Finset V := fun j => Upart j ∪ Zpart j
  have hZpart_sub : ∀ j : Fin 5, Zpart j ⊆ Z := fun j => Finset.filter_subset _ _
  have hZpart_disj : ∀ i j : Fin 5, i ≠ j → Disjoint (Zpart i) (Zpart j) := by
    intro i j hij; rw [Finset.disjoint_left]; intro x hxi hxj
    exact hij ((Finset.mem_filter.mp hxi).2.symm.trans (Finset.mem_filter.mp hxj).2)
  have hZpart_sum : ∑ j : Fin 5, #(Zpart j) = #Z := by
    have hbi : Finset.univ.biUnion Zpart = Z := by
      ext x; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Zpart, Finset.mem_filter]
      exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨cZ x, hx, rfl⟩⟩
    rw [← Finset.card_biUnion (fun i _ j _ hij => hZpart_disj i j hij), hbi]
  have hdisj_UZ : ∀ i j : Fin 5, Disjoint (Upart i) (Zpart j) :=
    fun i j => hdisj_ZU.symm.mono (hUpart_sub i) (hZpart_sub j)
  have hW_card : ∀ j : Fin 5, #(Wpart j) = #(Upart j) + #(Zpart j) :=
    fun j => Finset.card_union_of_disjoint (hdisj_UZ j j)
  have hW_sum : ∑ j : Fin 5, #(Wpart j) = n := by
    simp_rw [hW_card, Finset.sum_add_distrib, hUpart_sum, hZpart_sum]; omega
  have hstray : ∀ i j : Fin 5, j ≠ i + 4 → j ≠ i + 1 →
      700 * (∑ x ∈ Zpart i, #((Upart j).filter (G.Adj x))) ≤ #(Zpart i) * n := by
    intro i j h4 h1
    rw [Finset.mul_sum]
    calc ∑ x ∈ Zpart i, 700 * #((Upart j).filter (G.Adj x))
        ≤ ∑ _x ∈ Zpart i, n := Finset.sum_le_sum (fun x hx => by
          have hx' := Finset.mem_filter.mp hx
          exact hcZ x hx'.1 j (hx'.2.symm ▸ h4) (hx'.2.symm ▸ h1))
      _ = #(Zpart i) * n := by rw [Finset.sum_const, smul_eq_mul]
  -- Step 7: Apply c5_stability_cand_bound to all 10 candidates C_i and D_i
  set k := n / 2
  let s : Fin 5 → ℕ := fun i => #(Wpart i) + #(Wpart (i + 2))
  let t : Fin 5 → ℕ := fun i => k - s i
  have hZpart_le : ∀ j : Fin 5, #(Zpart j) ≤ #Z := fun j => Finset.card_le_card (hZpart_sub j)
  have hW_bounds : ∀ i : Fin 5,
      s i ≤ k ∧ 1 ≤ t i ∧ 2 ≤ #(Wpart i) ∧
      t i ≤ #(Wpart (i + 3)) ∧ t i ≤ #(Wpart (i + 4)) ∧
      49 * #(Wpart (i + 3)) ≤ 100 * t i ∧ 100 * t i ≤ 51 * #(Wpart (i + 3)) ∧
      49 * #(Wpart (i + 4)) ≤ 100 * t i ∧ 100 * t i ≤ 51 * #(Wpart (i + 4)) := by
    intro i
    have hsi_hi : 5 * (#(Wpart i) + #(Wpart (i + 2))) < 2 * n + 5 * #Z := by
      have h1 := hUpair_lt i
      have h2 := hW_card i; have h3 := hW_card (i + 2)
      have hdisjZ : Disjoint (Zpart i) (Zpart (i + 2)) :=
        hZpart_disj i (i + 2) (by intro h; fin_cases i <;> simp at h)
      have hZ2 : #(Zpart i) + #(Zpart (i + 2)) ≤ #Z := by
        rw [← Finset.card_union_of_disjoint hdisjZ]
        exact Finset.card_le_card (Finset.union_subset (hZpart_sub i) (hZpart_sub (i + 2)))
      omega
    have hsi_lo : 2 * n < 5 * (#(Wpart i) + #(Wpart (i + 2))) + 10 * #Z := by
      have h1 := hU_lo i; have h2 := hU_lo (i + 2)
      have h3 := hW_card i; have h4 := hW_card (i + 2)
      omega
    have hw0_lo := hU_lo i; have hw0_c := hW_card i
    have hw3_lo := hU_lo (i + 3); have hw3_hi := hU_hi (i + 3); have hw3_c := hW_card (i + 3); have hw3_z := hZpart_le (i + 3)
    have hw4_lo := hU_lo (i + 4); have hw4_hi := hU_hi (i + 4); have hw4_c := hW_card (i + 4); have hw4_z := hZpart_le (i + 4)
    dsimp only [s, t]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hC_cand : ∀ i : Fin 5,
      4 * n ^ 2 +
        98 * ((#(Zpart (i + 2)) * #(Upart (i + 3)) - ∑ x ∈ Zpart (i + 2), #((Upart (i + 3)).filter (G.Adj x))) +
              (#(Upart (i + 2)) * #(Zpart (i + 3)) - ∑ y ∈ Zpart (i + 3), #((Upart (i + 2)).filter (G.Adj y)))) <
        200 * t i * #(Wpart (i + 2)) +
        100 * (2 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x))) +
               (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Zpart i ∪ Zpart (i + 2)).filter (G.Adj x)))) +
        102 * ((∑ x ∈ Zpart i, #((Upart (i + 3)).filter (G.Adj x))) +
               (∑ y ∈ Zpart (i + 3), #((Upart i).filter (G.Adj y))) +
               (∑ x ∈ Zpart i, #((Zpart (i + 3)).filter (G.Adj x)))) +
        51 * (2 * (∑ y ∈ Zpart (i + 3), #((Upart (i + 3)).filter (G.Adj y))) +
              (∑ y ∈ Zpart (i + 3), #((Zpart (i + 3)).filter (G.Adj y)))) := by
    intro i
    have hb := hW_bounds i; have hb3 := hW_bounds (i + 3)
    have hne02 : i ≠ i + 2 := by intro h; fin_cases i <;> simp at h
    have hne03 : i ≠ i + 3 := by intro h; fin_cases i <;> simp at h
    have hne23 : i + 2 ≠ i + 3 := by intro h; fin_cases i <;> simp at h
    refine c5_stability_cand_bound G
      (hdisj_UZ i i) (hUpart_disj i (i + 2) hne02) (hdisj_UZ i (i + 2))
      (hUpart_disj i (i + 3) hne03) (hdisj_UZ i (i + 3))
      (hdisj_UZ (i + 2) i).symm (hZpart_disj i (i + 2) hne02)
      (hdisj_UZ (i + 3) i).symm (hZpart_disj i (i + 3) hne03)
      (hdisj_UZ (i + 2) (i + 2)) (hUpart_disj (i + 2) (i + 3) hne23) (hdisj_UZ (i + 2) (i + 3))
      (hdisj_UZ (i + 3) (i + 2)).symm (hZpart_disj (i + 2) (i + 3) hne23) (hdisj_UZ (i + 3) (i + 3))
      (hUpart_pair_indep i)
      (fun x hx y hy => hUpart_nadj (i + 3) (i + 3)
        (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h) x hx y hy)
      (hUpart_nadj i (i + 3) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h))
      hb.2.1 hb.2.2.2.1 hb3.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 ?_
    intro S hS
    apply hH
    rw [Set.ncard_coe_finset]
    have hS' := Finset.mem_powersetCard.mp hS
    have hd1 : Disjoint (Wpart i) (Wpart (i + 2)) :=
      Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hUpart_disj i (i + 2) hne02, hdisj_UZ i (i + 2)⟩,
        Finset.disjoint_union_right.mpr ⟨(hdisj_UZ (i + 2) i).symm, hZpart_disj i (i + 2) hne02⟩⟩
    have hd2 : Disjoint (Wpart i ∪ Wpart (i + 2)) S :=
      (Finset.disjoint_union_left.mpr ⟨
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hUpart_disj i (i + 3) hne03, hdisj_UZ i (i + 3)⟩,
          Finset.disjoint_union_right.mpr ⟨(hdisj_UZ (i + 3) i).symm, hZpart_disj i (i + 3) hne03⟩⟩,
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hUpart_disj (i + 2) (i + 3) hne23, hdisj_UZ (i + 2) (i + 3)⟩,
          Finset.disjoint_union_right.mpr ⟨(hdisj_UZ (i + 3) (i + 2)).symm, hZpart_disj (i + 2) (i + 3) hne23⟩⟩⟩).mono_right hS'.1
    change 2 * #(Wpart i ∪ Wpart (i + 2) ∪ S) + 1 ≥ n
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hS'.2]
    have hsi := hb.1; dsimp only [s, t] at hsi ⊢; omega
  have hD_cand : ∀ i : Fin 5,
      4 * n ^ 2 +
        98 * ((#(Zpart i) * #(Upart (i + 4)) - ∑ x ∈ Zpart i, #((Upart (i + 4)).filter (G.Adj x))) +
              (#(Upart i) * #(Zpart (i + 4)) - ∑ y ∈ Zpart (i + 4), #((Upart i).filter (G.Adj y)))) <
        200 * t i * #(Wpart i) +
        100 * (2 * (∑ x ∈ Zpart (i + 2) ∪ Zpart i, #((Upart (i + 2) ∪ Upart i).filter (G.Adj x))) +
               (∑ x ∈ Zpart (i + 2) ∪ Zpart i, #((Zpart (i + 2) ∪ Zpart i).filter (G.Adj x)))) +
        102 * ((∑ x ∈ Zpart (i + 2), #((Upart (i + 4)).filter (G.Adj x))) +
               (∑ y ∈ Zpart (i + 4), #((Upart (i + 2)).filter (G.Adj y))) +
               (∑ x ∈ Zpart (i + 2), #((Zpart (i + 4)).filter (G.Adj x)))) +
        51 * (2 * (∑ y ∈ Zpart (i + 4), #((Upart (i + 4)).filter (G.Adj y))) +
              (∑ y ∈ Zpart (i + 4), #((Zpart (i + 4)).filter (G.Adj y)))) := by
    intro i
    have hb := hW_bounds i; have hb4 := hW_bounds (i + 4)
    have hne20 : i + 2 ≠ i := by intro h; fin_cases i <;> simp at h
    have hne24 : i + 2 ≠ i + 4 := by intro h; fin_cases i <;> simp at h
    have hne04 : i ≠ i + 4 := by intro h; fin_cases i <;> simp at h
    refine c5_stability_cand_bound G
      (hdisj_UZ (i + 2) (i + 2)) (hUpart_disj (i + 2) i hne20) (hdisj_UZ (i + 2) i)
      (hUpart_disj (i + 2) (i + 4) hne24) (hdisj_UZ (i + 2) (i + 4))
      (hdisj_UZ i (i + 2)).symm (hZpart_disj (i + 2) i hne20)
      (hdisj_UZ (i + 4) (i + 2)).symm (hZpart_disj (i + 2) (i + 4) hne24)
      (hdisj_UZ i i) (hUpart_disj i (i + 4) hne04) (hdisj_UZ i (i + 4))
      (hdisj_UZ (i + 4) i).symm (hZpart_disj i (i + 4) hne04) (hdisj_UZ (i + 4) (i + 4))
      (fun x hx y hy => hUpart_pair_indep i x (Finset.union_comm (Upart (i + 2)) (Upart i) ▸ hx)
        y (Finset.union_comm (Upart (i + 2)) (Upart i) ▸ hy))
      (fun x hx y hy => hUpart_nadj (i + 4) (i + 4)
        (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h) x hx y hy)
      (hUpart_nadj (i + 2) (i + 4) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h))
      hb.2.1 hb.2.2.2.2.1 hb4.2.2.1 hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2 ?_
    intro S hS
    apply hH
    rw [Set.ncard_coe_finset]
    have hS' := Finset.mem_powersetCard.mp hS
    have hd1 : Disjoint (Wpart (i + 2)) (Wpart i) :=
      Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hUpart_disj (i + 2) i hne20, hdisj_UZ (i + 2) i⟩,
        Finset.disjoint_union_right.mpr ⟨(hdisj_UZ i (i + 2)).symm, hZpart_disj (i + 2) i hne20⟩⟩
    have hd2 : Disjoint (Wpart (i + 2) ∪ Wpart i) S :=
      (Finset.disjoint_union_left.mpr ⟨
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hUpart_disj (i + 2) (i + 4) hne24, hdisj_UZ (i + 2) (i + 4)⟩,
          Finset.disjoint_union_right.mpr ⟨(hdisj_UZ (i + 4) (i + 2)).symm, hZpart_disj (i + 2) (i + 4) hne24⟩⟩,
        Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hUpart_disj i (i + 4) hne04, hdisj_UZ i (i + 4)⟩,
          Finset.disjoint_union_right.mpr ⟨(hdisj_UZ (i + 4) i).symm, hZpart_disj i (i + 4) hne04⟩⟩⟩).mono_right hS'.1
    change 2 * #(Wpart (i + 2) ∪ Wpart i ∪ S) + 1 ≥ n
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hS'.2]
    have hsi := hb.1; dsimp only [s, t] at hsi ⊢; omega
  -- Sum all 10 candidates over i : Fin 5
  set DEF_sum := ∑ i : Fin 5,
    (((#(Zpart (i + 2)) * #(Upart (i + 3)) - ∑ x ∈ Zpart (i + 2), #((Upart (i + 3)).filter (G.Adj x))) +
      (#(Upart (i + 2)) * #(Zpart (i + 3)) - ∑ y ∈ Zpart (i + 3), #((Upart (i + 2)).filter (G.Adj y)))) +
     ((#(Zpart i) * #(Upart (i + 4)) - ∑ x ∈ Zpart i, #((Upart (i + 4)).filter (G.Adj x))) +
      (#(Upart i) * #(Zpart (i + 4)) - ∑ y ∈ Zpart (i + 4), #((Upart i).filter (G.Adj y)))))
  set RHS_J := ∑ i : Fin 5,
    ((2 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x))) +
      (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Zpart i ∪ Zpart (i + 2)).filter (G.Adj x)))) +
     (2 * (∑ x ∈ Zpart (i + 2) ∪ Zpart i, #((Upart (i + 2) ∪ Upart i).filter (G.Adj x))) +
      (∑ x ∈ Zpart (i + 2) ∪ Zpart i, #((Zpart (i + 2) ∪ Zpart i).filter (G.Adj x)))))
  set RHS_E := ∑ i : Fin 5,
    (((∑ x ∈ Zpart i, #((Upart (i + 3)).filter (G.Adj x))) +
      (∑ y ∈ Zpart (i + 3), #((Upart i).filter (G.Adj y))) +
      (∑ x ∈ Zpart i, #((Zpart (i + 3)).filter (G.Adj x)))) +
     ((∑ x ∈ Zpart (i + 2), #((Upart (i + 4)).filter (G.Adj x))) +
      (∑ y ∈ Zpart (i + 4), #((Upart (i + 2)).filter (G.Adj y))) +
      (∑ x ∈ Zpart (i + 2), #((Zpart (i + 4)).filter (G.Adj x)))))
  set RHS_K := ∑ i : Fin 5,
    ((2 * (∑ y ∈ Zpart (i + 3), #((Upart (i + 3)).filter (G.Adj y))) +
      (∑ y ∈ Zpart (i + 3), #((Zpart (i + 3)).filter (G.Adj y)))) +
     (2 * (∑ y ∈ Zpart (i + 4), #((Upart (i + 4)).filter (G.Adj y))) +
      (∑ y ∈ Zpart (i + 4), #((Zpart (i + 4)).filter (G.Adj y)))))
  have hsum10 : 40 * n ^ 2 + 98 * DEF_sum <
      200 * (∑ i : Fin 5, s i * t i) + 100 * RHS_J + 102 * RHS_E + 51 * RHS_K := by
    have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 5))) (by simp) (fun i _ =>
      add_lt_add (hC_cand i) (hD_cand i))
    have hL : ∑ i : Fin 5,
        ((4 * n ^ 2 + 98 * ((#(Zpart (i + 2)) * #(Upart (i + 3)) -
            ∑ x ∈ Zpart (i + 2), #((Upart (i + 3)).filter (G.Adj x))) +
            (#(Upart (i + 2)) * #(Zpart (i + 3)) - ∑ y ∈ Zpart (i + 3), #((Upart (i + 2)).filter (G.Adj y))))) +
         (4 * n ^ 2 + 98 * ((#(Zpart i) * #(Upart (i + 4)) -
            ∑ x ∈ Zpart i, #((Upart (i + 4)).filter (G.Adj x))) +
            (#(Upart i) * #(Zpart (i + 4)) - ∑ y ∈ Zpart (i + 4), #((Upart i).filter (G.Adj y)))))) =
        40 * n ^ 2 + 98 * DEF_sum := by
      simp_rw [show ∀ a b : ℕ, (4 * n ^ 2 + 98 * a) + (4 * n ^ 2 + 98 * b) = 8 * n ^ 2 + 98 * (a + b) by intros; ring]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      change 5 * (8 * n ^ 2) + 98 * DEF_sum = 40 * n ^ 2 + 98 * DEF_sum
      ring
    have hR : ∑ i : Fin 5,
        ((200 * t i * #(Wpart (i + 2)) +
          100 * (2 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x))) +
                 (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Zpart i ∪ Zpart (i + 2)).filter (G.Adj x)))) +
          102 * ((∑ x ∈ Zpart i, #((Upart (i + 3)).filter (G.Adj x))) +
                 (∑ y ∈ Zpart (i + 3), #((Upart i).filter (G.Adj y))) +
                 (∑ x ∈ Zpart i, #((Zpart (i + 3)).filter (G.Adj x)))) +
          51 * (2 * (∑ y ∈ Zpart (i + 3), #((Upart (i + 3)).filter (G.Adj y))) +
                (∑ y ∈ Zpart (i + 3), #((Zpart (i + 3)).filter (G.Adj y))))) +
         (200 * t i * #(Wpart i) +
          100 * (2 * (∑ x ∈ Zpart (i + 2) ∪ Zpart i, #((Upart (i + 2) ∪ Upart i).filter (G.Adj x))) +
                 (∑ x ∈ Zpart (i + 2) ∪ Zpart i, #((Zpart (i + 2) ∪ Zpart i).filter (G.Adj x)))) +
          102 * ((∑ x ∈ Zpart (i + 2), #((Upart (i + 4)).filter (G.Adj x))) +
                 (∑ y ∈ Zpart (i + 4), #((Upart (i + 2)).filter (G.Adj y))) +
                 (∑ x ∈ Zpart (i + 2), #((Zpart (i + 4)).filter (G.Adj x)))) +
          51 * (2 * (∑ y ∈ Zpart (i + 4), #((Upart (i + 4)).filter (G.Adj y))) +
                (∑ y ∈ Zpart (i + 4), #((Zpart (i + 4)).filter (G.Adj y)))))) =
        200 * (∑ i : Fin 5, s i * t i) + 100 * RHS_J + 102 * RHS_E + 51 * RHS_K := by
      simp_rw [show ∀ i : Fin 5, ∀ a1 a2 b1 b2 c1 c2 d1 d2 : ℕ,
        (200 * t i * a1 + 100 * b1 + 102 * c1 + 51 * d1) +
        (200 * t i * a2 + 100 * b2 + 102 * c2 + 51 * d2) =
        200 * ((a2 + a1) * t i) + 100 * (b1 + b2) + 102 * (c1 + c2) + 51 * (d1 + d2) by intros; ring]
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
    rw [← hL, ← hR]; exact hlt
  -- Cancel 40 * n^2 via c5_half_sum_le!
  have hmain_le : 200 * (∑ i : Fin 5, s i * t i) ≤ 40 * n ^ 2 := by
    have h5 := c5_half_sum_le (fun i => #(Wpart i)) n k hW_sum (by omega) (fun i => (hW_bounds i).1)
    change 5 * (∑ i : Fin 5, s i * t i) ≤ n ^ 2 at h5
    have : 200 * (∑ i : Fin 5, s i * t i) = 40 * (5 * (∑ i : Fin 5, s i * t i)) := by ring
    omega
  -- Lower bound DEF sum: 2500 * DEF_sum >= 98 * #Z * n
  have hDEF_lo : 98 * #Z * n ≤ 2500 * DEF_sum := by
    have hDEF_eq : DEF_sum =
        2 * ∑ j : Fin 5, ((#(Zpart j) * #(Upart (j + 1)) - ∑ x ∈ Zpart j, #((Upart (j + 1)).filter (G.Adj x))) +
          (#(Zpart j) * #(Upart (j + 4)) - ∑ x ∈ Zpart j, #((Upart (j + 4)).filter (G.Adj x)))) := by
      simp only [DEF_sum, Finset.sum_add_distrib]
      have ha : ∑ i : Fin 5, (#(Zpart (i + 2)) * #(Upart (i + 3)) - ∑ x ∈ Zpart (i + 2), #((Upart (i + 3)).filter (G.Adj x))) =
          ∑ j : Fin 5, (#(Zpart j) * #(Upart (j + 1)) - ∑ x ∈ Zpart j, #((Upart (j + 1)).filter (G.Adj x))) :=
        Fintype.sum_equiv (Equiv.addRight (2 : Fin 5)) _ _ (fun i => by simp [show i + 2 + 1 = i + 3 by fin_cases i <;> rfl])
      have hb : ∑ i : Fin 5, (#(Upart (i + 2)) * #(Zpart (i + 3)) - ∑ y ∈ Zpart (i + 3), #((Upart (i + 2)).filter (G.Adj y))) =
          ∑ j : Fin 5, (#(Zpart j) * #(Upart (j + 4)) - ∑ x ∈ Zpart j, #((Upart (j + 4)).filter (G.Adj x))) :=
        Fintype.sum_equiv (Equiv.addRight (3 : Fin 5)) _ _ (fun i => by
          simp [show i + 3 + 4 = i + 2 by fin_cases i <;> rfl, mul_comm])
      have hd : ∑ i : Fin 5, (#(Upart i) * #(Zpart (i + 4)) - ∑ y ∈ Zpart (i + 4), #((Upart i).filter (G.Adj y))) =
          ∑ j : Fin 5, (#(Zpart j) * #(Upart (j + 1)) - ∑ x ∈ Zpart j, #((Upart (j + 1)).filter (G.Adj x))) :=
        Fintype.sum_equiv (Equiv.addRight (4 : Fin 5)) _ _ (fun i => by
          simp [show i + 4 + 1 = i by fin_cases i <;> rfl, mul_comm])
      rw [ha, hb, hd]; omega
    rw [hDEF_eq]
    have hper_j : ∀ j : Fin 5, 49 * #(Zpart j) * n ≤
        2500 * ((#(Zpart j) * #(Upart (j + 1)) - ∑ x ∈ Zpart j, #((Upart (j + 1)).filter (G.Adj x))) +
                (#(Zpart j) * #(Upart (j + 4)) - ∑ x ∈ Zpart j, #((Upart (j + 4)).filter (G.Adj x)))) := by
      intro j
      have hle1 : ∑ x ∈ Zpart j, #((Upart (j + 1)).filter (G.Adj x)) ≤ #(Zpart j) * #(Upart (j + 1)) := by
        calc _ ≤ ∑ _x ∈ Zpart j, #(Upart (j + 1)) := Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
          _ = #(Zpart j) * #(Upart (j + 1)) := by rw [Finset.sum_const, smul_eq_mul]
      have hle4 : ∑ x ∈ Zpart j, #((Upart (j + 4)).filter (G.Adj x)) ≤ #(Zpart j) * #(Upart (j + 4)) := by
        calc _ ≤ ∑ _x ∈ Zpart j, #(Upart (j + 4)) := Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))
          _ = #(Zpart j) * #(Upart (j + 4)) := by rw [Finset.sum_const, smul_eq_mul]
      have hdeg_le : (∑ x ∈ Zpart j, #((Upart (j + 1)).filter (G.Adj x))) +
          (∑ x ∈ Zpart j, #((Upart (j + 4)).filter (G.Adj x))) ≤ ∑ x ∈ Zpart j, G.degree x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum; intro x _
        have hd14 : Disjoint ((Upart (j + 1)).filter (G.Adj x)) ((Upart (j + 4)).filter (G.Adj x)) :=
          (hUpart_disj (j + 1) (j + 4) (by intro h; fin_cases j <;> simp at h)).mono
            (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        rw [← Finset.card_union_of_disjoint hd14, SimpleGraph.degree]
        apply Finset.card_le_card; intro v hv
        rw [SimpleGraph.mem_neighborFinset]
        rcases Finset.mem_union.mp hv with h1 | h4
        · exact (Finset.mem_filter.mp h1).2
        · exact (Finset.mem_filter.mp h4).2
      have h50deg : 50 * ∑ x ∈ Zpart j, G.degree x ≤ 19 * #(Zpart j) * n := by
        rw [Finset.mul_sum]
        calc _ ≤ ∑ _x ∈ Zpart j, 19 * n := Finset.sum_le_sum (fun x hx => by
              have := (Finset.mem_filter.mp (hZpart_sub j hx)).2; omega)
          _ = 19 * #(Zpart j) * n := by rw [Finset.sum_const, smul_eq_mul]; ring
      have hU1 := hU_lo (j + 1); have hU4 := hU_lo (j + 4)
      have h1000 : 1000 * #(Zpart j) * n ≤ 2500 * (#(Zpart j) * #(Upart (j + 1)) + #(Zpart j) * #(Upart (j + 4))) + 5000 * #Z * #(Zpart j) := by
        have h1 : 2 * n ≤ 5 * (#(Upart (j + 1)) + #(Upart (j + 4))) + 10 * #Z := by omega
        have h2 := Nat.mul_le_mul_left (500 * #(Zpart j)) h1
        have ha : 500 * #(Zpart j) * (2 * n) = 1000 * #(Zpart j) * n := by ring
        have hb : 500 * #(Zpart j) * (5 * (#(Upart (j + 1)) + #(Upart (j + 4))) + 10 * #Z) =
            2500 * (#(Zpart j) * #(Upart (j + 1)) + #(Zpart j) * #(Upart (j + 4))) + 5000 * #Z * #(Zpart j) := by ring
        omega
      have h5000Z_j : 5000 * #Z * #(Zpart j) ≤ #(Zpart j) * n := by
        calc 5000 * #Z * #(Zpart j) ≤ n * #(Zpart j) := Nat.mul_le_mul_right _ h5000Z
          _ = #(Zpart j) * n := mul_comm _ _
      have h19j : 19 * #(Zpart j) * n = 19 * (#(Zpart j) * n) := by ring
      have h950j : 950 * #(Zpart j) * n = 950 * (#(Zpart j) * n) := by ring
      have h1000j : 1000 * #(Zpart j) * n = 1000 * (#(Zpart j) * n) := by ring
      have h49j : 49 * #(Zpart j) * n = 49 * (#(Zpart j) * n) := by ring
      have h2500deg : 2500 * ((∑ x ∈ Zpart j, #((Upart (j + 1)).filter (G.Adj x))) +
          (∑ x ∈ Zpart j, #((Upart (j + 4)).filter (G.Adj x)))) ≤ 950 * #(Zpart j) * n := by omega
      omega
    have hsum_j := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) => hper_j j)
    rw [← Finset.sum_mul, ← Finset.mul_sum, hZpart_sum, ← Finset.mul_sum] at hsum_j
    have h98z : 98 * #Z * n = 2 * (49 * #Z * n) := by ring
    omega
  -- Upper bound the 3 RHS error sums cleanly!
  have hRHS_J : 35000 * RHS_J ≤ 828 * #Z * n := by
    have hper : ∀ i : Fin 5,
        35000 * (2 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x))) +
          (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Zpart i ∪ Zpart (i + 2)).filter (G.Adj x)))) ≤
        207 * (#(Zpart i) + #(Zpart (i + 2))) * n := by
      intro i
      have hne02 : i ≠ i + 2 := by intro h; fin_cases i <;> simp at h
      have hUZ : 700 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x))) ≤
          2 * (#(Zpart i) + #(Zpart (i + 2))) * n := by
        have hsplit : ∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x)) =
            (∑ x ∈ Zpart i, #((Upart i).filter (G.Adj x))) + (∑ x ∈ Zpart i, #((Upart (i + 2)).filter (G.Adj x))) +
            (∑ x ∈ Zpart (i + 2), #((Upart i).filter (G.Adj x))) + (∑ x ∈ Zpart (i + 2), #((Upart (i + 2)).filter (G.Adj x))) := by
          have hdU := hUpart_disj i (i + 2) hne02
          have hf : ∀ x, #((Upart i ∪ Upart (i + 2)).filter (G.Adj x)) =
              #((Upart i).filter (G.Adj x)) + #((Upart (i + 2)).filter (G.Adj x)) := fun x => by
            rw [Finset.filter_union, Finset.card_union_of_disjoint (hdU.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
          simp_rw [hf]
          rw [Finset.sum_union (hZpart_disj i (i + 2) hne02), Finset.sum_add_distrib, Finset.sum_add_distrib]
          omega
        rw [hsplit]
        have h1 := hstray i i (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
        have h2 := hstray i (i + 2) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
        have h3 := hstray (i + 2) i (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
        have h4 := hstray (i + 2) (i + 2) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
        have hlin : 2 * (#(Zpart i) + #(Zpart (i + 2))) * n =
            #(Zpart i) * n + #(Zpart i) * n + #(Zpart (i + 2)) * n + #(Zpart (i + 2)) * n := by ring
        omega
      have hZZ : ∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Zpart i ∪ Zpart (i + 2)).filter (G.Adj x)) ≤
          (#(Zpart i) + #(Zpart (i + 2))) * #Z := by
        have hsubZ : Zpart i ∪ Zpart (i + 2) ⊆ Z := Finset.union_subset (hZpart_sub i) (hZpart_sub (i + 2))
        calc _ ≤ ∑ _x ∈ Zpart i ∪ Zpart (i + 2), #Z := Finset.sum_le_sum (fun _ _ =>
              Finset.card_le_card ((Finset.filter_subset _ _).trans hsubZ))
          _ = #(Zpart i ∪ Zpart (i + 2)) * #Z := by rw [Finset.sum_const, smul_eq_mul]
          _ = (#(Zpart i) + #(Zpart (i + 2))) * #Z := by rw [Finset.card_union_of_disjoint (hZpart_disj i (i + 2) hne02)]
      have hZZ_n : 35000 * ((#(Zpart i) + #(Zpart (i + 2))) * #Z) ≤ 7 * (#(Zpart i) + #(Zpart (i + 2))) * n := by
        calc 35000 * ((#(Zpart i) + #(Zpart (i + 2))) * #Z)
            = 7 * (#(Zpart i) + #(Zpart (i + 2))) * (5000 * #Z) := by ring
          _ ≤ 7 * (#(Zpart i) + #(Zpart (i + 2))) * n := Nat.mul_le_mul_left _ h5000Z
      have h100 : 35000 * (2 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x)))) ≤
          200 * (#(Zpart i) + #(Zpart (i + 2))) * n := by
        have h1 : 35000 * (2 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x)))) =
            100 * (700 * (∑ x ∈ Zpart i ∪ Zpart (i + 2), #((Upart i ∪ Upart (i + 2)).filter (G.Adj x)))) := by ring
        have h2 : 100 * (2 * (#(Zpart i) + #(Zpart (i + 2))) * n) = 200 * (#(Zpart i) + #(Zpart (i + 2))) * n := by ring
        omega
      have h207 : 207 * (#(Zpart i) + #(Zpart (i + 2))) * n =
          200 * (#(Zpart i) + #(Zpart (i + 2))) * n + 7 * (#(Zpart i) + #(Zpart (i + 2))) * n := by ring
      omega
    have hsum : 35000 * RHS_J ≤ ∑ i : Fin 5, 414 * (#(Zpart i) + #(Zpart (i + 2))) * n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      have hp := hper i
      have hcomm : Zpart (i + 2) ∪ Zpart i = Zpart i ∪ Zpart (i + 2) := Finset.union_comm _ _
      have hcommU : Upart (i + 2) ∪ Upart i = Upart i ∪ Upart (i + 2) := Finset.union_comm _ _
      rw [hcomm, hcommU]
      have : 414 * (#(Zpart i) + #(Zpart (i + 2))) * n = 2 * (207 * (#(Zpart i) + #(Zpart (i + 2))) * n) := by ring
      omega
    have hsumZ2 : ∑ i : Fin 5, (#(Zpart i) + #(Zpart (i + 2))) = 2 * #Z := by
      rw [Finset.sum_add_distrib, hZpart_sum]
      have h2 : ∑ i : Fin 5, #(Zpart (i + 2)) = #Z := by
        rw [← hZpart_sum]; exact Fintype.sum_equiv (Equiv.addRight (2 : Fin 5)) _ _ (fun _ => rfl)
      omega
    have hfin : ∑ i : Fin 5, 414 * (#(Zpart i) + #(Zpart (i + 2))) * n = 828 * #Z * n := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsumZ2]; ring
    omega
  have hRHS_E : 35000 * RHS_E ≤ 214 * #Z * n := by
    have hper : ∀ i : Fin 5,
        35000 * (((∑ x ∈ Zpart i, #((Upart (i + 3)).filter (G.Adj x))) +
                  (∑ y ∈ Zpart (i + 3), #((Upart i).filter (G.Adj y))) +
                  (∑ x ∈ Zpart i, #((Zpart (i + 3)).filter (G.Adj x)))) +
                 ((∑ x ∈ Zpart (i + 2), #((Upart (i + 4)).filter (G.Adj x))) +
                  (∑ y ∈ Zpart (i + 4), #((Upart (i + 2)).filter (G.Adj y))) +
                  (∑ x ∈ Zpart (i + 2), #((Zpart (i + 4)).filter (G.Adj x))))) ≤
        (57 * #(Zpart i) + 50 * #(Zpart (i + 3)) + 57 * #(Zpart (i + 2)) + 50 * #(Zpart (i + 4))) * n := by
      intro i
      have h1 := hstray i (i + 3) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
      have h2 := hstray (i + 3) i (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
      have h3 := hstray (i + 2) (i + 4) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
      have h4 := hstray (i + 4) (i + 2) (by intro h; fin_cases i <;> simp at h) (by intro h; fin_cases i <;> simp at h)
      have hz1 : ∑ x ∈ Zpart i, #((Zpart (i + 3)).filter (G.Adj x)) ≤ #(Zpart i) * #Z := by
        calc _ ≤ ∑ _x ∈ Zpart i, #Z := Finset.sum_le_sum (fun _ _ =>
              Finset.card_le_card ((Finset.filter_subset _ _).trans (hZpart_sub _)))
          _ = #(Zpart i) * #Z := by rw [Finset.sum_const, smul_eq_mul]
      have hz2 : ∑ x ∈ Zpart (i + 2), #((Zpart (i + 4)).filter (G.Adj x)) ≤ #(Zpart (i + 2)) * #Z := by
        calc _ ≤ ∑ _x ∈ Zpart (i + 2), #Z := Finset.sum_le_sum (fun _ _ =>
              Finset.card_le_card ((Finset.filter_subset _ _).trans (hZpart_sub _)))
          _ = #(Zpart (i + 2)) * #Z := by rw [Finset.sum_const, smul_eq_mul]
      have hzn1 : 35000 * (#(Zpart i) * #Z) ≤ 7 * #(Zpart i) * n := by
        calc 35000 * (#(Zpart i) * #Z) = 7 * #(Zpart i) * (5000 * #Z) := by ring
          _ ≤ 7 * #(Zpart i) * n := Nat.mul_le_mul_left _ h5000Z
      have hzn2 : 35000 * (#(Zpart (i + 2)) * #Z) ≤ 7 * #(Zpart (i + 2)) * n := by
        calc 35000 * (#(Zpart (i + 2)) * #Z) = 7 * #(Zpart (i + 2)) * (5000 * #Z) := by ring
          _ ≤ 7 * #(Zpart (i + 2)) * n := Nat.mul_le_mul_left _ h5000Z
      have hlin : (57 * #(Zpart i) + 50 * #(Zpart (i + 3)) + 57 * #(Zpart (i + 2)) + 50 * #(Zpart (i + 4))) * n =
          50 * (#(Zpart i) * n) + 50 * (#(Zpart (i + 3)) * n) + 7 * #(Zpart i) * n +
          50 * (#(Zpart (i + 2)) * n) + 50 * (#(Zpart (i + 4)) * n) + 7 * #(Zpart (i + 2)) * n := by ring
      omega
    have hsum : 35000 * RHS_E ≤ ∑ i : Fin 5,
        (57 * #(Zpart i) + 50 * #(Zpart (i + 3)) + 57 * #(Zpart (i + 2)) + 50 * #(Zpart (i + 4))) * n := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hper i)
    have hshift : ∀ c : Fin 5, ∑ i : Fin 5, #(Zpart (i + c)) = #Z := fun c => by
      rw [← hZpart_sum]; exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)
    have hfin : ∑ i : Fin 5, (57 * #(Zpart i) + 50 * #(Zpart (i + 3)) + 57 * #(Zpart (i + 2)) + 50 * #(Zpart (i + 4))) * n =
        214 * #Z * n := by
      rw [← Finset.sum_mul]
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hZpart_sum, hshift 3, hshift 2, hshift 4]; ring
    omega
  have hRHS_K : 35000 * RHS_K ≤ 214 * #Z * n := by
    have hper : ∀ j : Fin 5,
        35000 * (2 * (∑ y ∈ Zpart j, #((Upart j).filter (G.Adj y))) +
          (∑ y ∈ Zpart j, #((Zpart j).filter (G.Adj y)))) ≤ 107 * #(Zpart j) * n := by
      intro j
      have h1 := hstray j j (by intro h; fin_cases j <;> simp at h) (by intro h; fin_cases j <;> simp at h)
      have hz : ∑ y ∈ Zpart j, #((Zpart j).filter (G.Adj y)) ≤ #(Zpart j) * #Z := by
        calc _ ≤ ∑ _y ∈ Zpart j, #Z := Finset.sum_le_sum (fun _ _ =>
              Finset.card_le_card ((Finset.filter_subset _ _).trans (hZpart_sub _)))
          _ = #(Zpart j) * #Z := by rw [Finset.sum_const, smul_eq_mul]
      have hzn : 35000 * (#(Zpart j) * #Z) ≤ 7 * #(Zpart j) * n := by
        calc 35000 * (#(Zpart j) * #Z) = 7 * #(Zpart j) * (5000 * #Z) := by ring
          _ ≤ 7 * #(Zpart j) * n := Nat.mul_le_mul_left _ h5000Z
      have h107 : 107 * #(Zpart j) * n = 100 * (#(Zpart j) * n) + 7 * #(Zpart j) * n := by ring
      omega
    have hsum : 35000 * RHS_K ≤ ∑ i : Fin 5, (107 * #(Zpart (i + 3)) * n + 107 * #(Zpart (i + 4)) * n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      have h3 := hper (i + 3); have h4 := hper (i + 4); omega
    have hshift : ∀ c : Fin 5, ∑ i : Fin 5, #(Zpart (i + c)) = #Z := fun c => by
      rw [← hZpart_sum]; exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)
    have hfin : ∑ i : Fin 5, (107 * #(Zpart (i + 3)) * n + 107 * #(Zpart (i + 4)) * n) = 214 * #Z * n := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum,
        hshift 3, hshift 4]; ring
    omega
  -- Final contradiction: 134456 * #Z * n <= 35000 * (98 * DEF_sum) < 115542 * #Z * n!
  have hcancel : 98 * DEF_sum < 100 * RHS_J + 102 * RHS_E + 51 * RHS_K := by omega
  have hfinal_lt : 35000 * (98 * DEF_sum) < 35000 * (100 * RHS_J + 102 * RHS_E + 51 * RHS_K) :=
    Nat.mul_lt_mul_of_pos_left hcancel (by omega)
  have hLHS : 134456 * #Z * n ≤ 35000 * (98 * DEF_sum) := by
    have : 35000 * (98 * DEF_sum) = 1372 * (2500 * DEF_sum) := by ring
    have : 134456 * #Z * n = 1372 * (98 * #Z * n) := by ring
    omega
  have hRHS : 35000 * (100 * RHS_J + 102 * RHS_E + 51 * RHS_K) ≤ 115542 * #Z * n := by
    have : 35000 * (100 * RHS_J + 102 * RHS_E + 51 * RHS_K) =
        100 * (35000 * RHS_J) + 102 * (35000 * RHS_E) + 51 * (35000 * RHS_K) := by ring
    have : 115542 * #Z * n = 100 * (828 * #Z * n) + 102 * (214 * #Z * n) + 51 * (214 * #Z * n) := by ring
    omega
  have hZn_pos : 0 < #Z * n := Nat.mul_pos (by omega) (by omega)
  have hgt : 115542 * (#Z * n) < 134456 * (#Z * n) := Nat.mul_lt_mul_of_pos_right (by omega) hZn_pos
  have h1 : 134456 * #Z * n = 134456 * (#Z * n) := by ring
  have h2 : 115542 * #Z * n = 115542 * (#Z * n) := by ring
  omega

/-- Quadratic shift inequality: shifting weight from w to u decreases the adjacency quadratic form
    whenever the weighted neighborhood sum at u is <= that at w. -/
lemma shift_quad_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℕ) {u w : V} (huw : u ≠ w) {δ : ℕ} (hδ : δ ≤ a w)
    (hs : (∑ x : V, if G.Adj u x then a x else 0) ≤ ∑ x : V, if G.Adj w x then a x else 0) :
    let a' : V → ℕ := fun x => if x = u then a u + δ else if x = w then a w - δ else a x
    (∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0) ≤
      ∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 := by
  intro a'
  have hdiff : ((∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0 : ℕ) : ℤ) -
      ((∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 : ℕ) : ℤ) =
      2 * (δ : ℤ) * (((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) -
        ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ)) -
      (if G.Adj u w then 2 * (δ : ℤ) ^ 2 else 0) := by
    let d : V → ℤ := fun x => if x = u then (δ : ℤ) else if x = w then -(δ : ℤ) else 0
    have ha'z : ∀ x : V, (a' x : ℤ) = (a x : ℤ) + d x := by
      intro x
      by_cases hxu : x = u
      · subst hxu; simp [a', d]
      · by_cases hxw : x = w
        · subst hxw; simp [a', d, hxu, Nat.cast_sub hδ]; ring
        · simp [a', d, hxu, hxw]
    have hQ : ((∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0 : ℕ) : ℤ) -
        ((∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 : ℕ) : ℤ) =
        ∑ x : V, ∑ y : V, (if G.Adj x y then (a x : ℤ) * d y + d x * (a y : ℤ) + d x * d y else 0) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro y _
      by_cases hxy : G.Adj x y
      · simp only [hxy, if_true, ha'z x, ha'z y]; ring
      · simp [hxy]
    rw [hQ]
    have hsplit : ∑ x : V, ∑ y : V, (if G.Adj x y then (a x : ℤ) * d y + d x * (a y : ℤ) + d x * d y else 0) =
        (∑ x : V, ∑ y : V, if G.Adj x y then (a x : ℤ) * d y else 0) +
        (∑ x : V, ∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0) +
        (∑ x : V, ∑ y : V, if G.Adj x y then d x * d y else 0) := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      split_ifs <;> ring
    rw [hsplit]
    have hsym : (∑ x : V, ∑ y : V, if G.Adj x y then (a x : ℤ) * d y else 0) =
        ∑ x : V, ∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      by_cases h : G.Adj y x
      · have h' : G.Adj x y := h.symm
        simp only [h, h', if_true]; ring
      · have h' : ¬ G.Adj x y := fun hxy => h hxy.symm
        simp [h, h']
    have hsum_d : ∀ f : V → ℤ, ∑ x : V, d x * f x = (δ : ℤ) * (f u - f w) := by
      intro f
      have hsub : ∀ x : V, d x * f x = (if x = u then (δ : ℤ) * f u else 0) +
          (if x = w then -(δ : ℤ) * f w else 0) := by
        intro x
        by_cases hxu : x = u
        · subst hxu; simp [d, huw]
        · by_cases hxw : x = w
          · subst hxw; simp [d, hxu]
          · simp [d, hxu, hxw]
      simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hlin : (∑ x : V, ∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0) =
        (δ : ℤ) * (((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) -
          ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ)) := by
      have hterm : ∀ x : V, (∑ y : V, if G.Adj x y then d x * (a y : ℤ) else 0) =
          d x * (∑ y : V, if G.Adj x y then (a y : ℤ) else 0) := by
        intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> ring
      simp_rw [hterm]
      rw [hsum_d]
      push_cast
      have hc : ∀ z : V, (∑ y : V, (if G.Adj z y then (a y : ℤ) else 0)) =
          ∑ y : V, ((if G.Adj z y then a y else 0 : ℕ) : ℤ) := by
        intro z; apply Finset.sum_congr rfl; intro y _; split_ifs <;> simp
      rw [hc u, hc w]
    have hquad : (∑ x : V, ∑ y : V, if G.Adj x y then d x * d y else 0) =
        -(if G.Adj u w then 2 * (δ : ℤ) ^ 2 else 0) := by
      have hterm : ∀ x : V, (∑ y : V, if G.Adj x y then d x * d y else 0) =
          d x * (∑ y : V, if G.Adj x y then d y else 0) := by
        intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> ring
      simp_rw [hterm]
      rw [hsum_d]
      have hinner : ∀ z : V, (∑ y : V, if G.Adj z y then d y else 0) =
          (if G.Adj z u then (δ : ℤ) else 0) + (if G.Adj z w then -(δ : ℤ) else 0) := by
        intro z
        have hsub : ∀ y : V, (if G.Adj z y then d y else 0) =
            (if y = u then (if G.Adj z u then (δ : ℤ) else 0) else 0) +
            (if y = w then (if G.Adj z w then -(δ : ℤ) else 0) else 0) := by
          intro y
          by_cases hyu : y = u
          · subst hyu; simp [d, huw]
          · by_cases hyw : y = w
            · subst hyw; simp [d, hyu]
            · simp [d, hyu, hyw]
        simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hinner u, hinner w]
      by_cases huw_adj : G.Adj u w
      · have hwu_adj : G.Adj w u := huw_adj.symm
        simp [huw_adj, hwu_adj]; ring
      · have hwu_adj : ¬ G.Adj w u := fun h => huw_adj h.symm
        simp [huw_adj, hwu_adj]
    rw [hsym, hlin, hquad]; ring
  have hle0 : ((∑ x : V, ∑ y : V, if G.Adj x y then a' x * a' y else 0 : ℕ) : ℤ) ≤
      ((∑ x : V, ∑ y : V, if G.Adj x y then a x * a y else 0 : ℕ) : ℤ) := by
    have hsz : ((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) ≤
        ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ) := Nat.cast_le.mpr hs
    have h1 : 2 * (δ : ℤ) * (((∑ x : V, if G.Adj u x then a x else 0 : ℕ) : ℤ) -
        ((∑ x : V, if G.Adj w x then a x else 0 : ℕ) : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h2 : (0 : ℤ) ≤ if G.Adj u w then 2 * (δ : ℤ) ^ 2 else 0 := by split_ifs <;> positivity
    linarith
  exact Nat.cast_le.mp hle0

/-- Master 2m-Blowup Theorem: the balanced (2m)-blowup of any counterexample G on n vertices
    is STILL a triangle-free counterexample on 2*m*n vertices, preserving edge density and degrees. -/
theorem blowup_counterexample {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (H : SimpleGraph (V × Fin (2 * m))),
      (∀ u i v j, H.Adj (u, i) (v, j) ↔ G.Adj u v) ∧
      H.CliqueFree 3 ∧
      (∀ U : Set (V × Fin (2 * m)), 2 * U.ncard + 1 ≥ Fintype.card (V × Fin (2 * m)) →
        50 * (H.induce U).edgeSet.ncard > Fintype.card (V × Fin (2 * m)) ^ 2) ∧
      H.edgeSet.ncard = (2 * m) ^ 2 * G.edgeSet.ncard ∧
      (∀ u i, (H.neighborSet (u, i)).ncard = 2 * m * (G.neighborSet u).ncard) := by
  classical
  let H : SimpleGraph (V × Fin (2 * m)) := G.comap Prod.fst
  have hAdj : ∀ u i v j, H.Adj (u, i) (v, j) ↔ G.Adj u v := fun _ _ _ _ => Iff.rfl
  have hH_TF : H.CliqueFree 3 := by
    intro s hs
    obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hs.2
    have h1 : H.Adj p q := hs.1 (by simp) (by simp) hpq
    have h2 : H.Adj q r := hs.1 (by simp) (by simp) hqr
    have h3 : H.Adj p r := hs.1 (by simp) (by simp) hpr
    exact not_adj_of_cliqueFree_three hTF h1 h2 h3
  have hH_deg : ∀ u i, (H.neighborSet (u, i)).ncard = 2 * m * (G.neighborSet u).ncard := by
    intro u i
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    have hprod : (H.neighborSet (u, i)).toFinset = (G.neighborSet u).toFinset ×ˢ (Finset.univ : Finset (Fin (2 * m))) := by
      ext ⟨v, j⟩
      simp [H]
    rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hH_edges : H.edgeSet.ncard = (2 * m) ^ 2 * G.edgeSet.ncard := by
    have h1 : 2 * H.edgeSet.ncard = ∑ p : V × Fin (2 * m), (H.neighborSet p).ncard := by
      have hcard : H.edgeSet.ncard = #H.edgeFinset := by rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl; intro p _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
    have h2 : 2 * G.edgeSet.ncard = ∑ u : V, (G.neighborSet u).ncard := by
      have hcard : G.edgeSet.ncard = #G.edgeFinset := by rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl; intro u _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
    have hsum : ∑ p : V × Fin (2 * m), (H.neighborSet p).ncard =
        (2 * m) ^ 2 * ∑ u : V, (G.neighborSet u).ncard := by
      rw [Fintype.sum_prod_type]
      simp_rw [hH_deg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [← h1, ← h2] at hsum
    have hmul2 : 2 * H.edgeSet.ncard = 2 * ((2 * m) ^ 2 * G.edgeSet.ncard) := by rw [hsum]; ring
    omega
  have hH_sparse : ∀ U : Set (V × Fin (2 * m)), 2 * U.ncard + 1 ≥ Fintype.card (V × Fin (2 * m)) →
      50 * (H.induce U).edgeSet.ncard > Fintype.card (V × Fin (2 * m)) ^ 2 := by
    intro U hU_card
    by_contra hle
    push Not at hle
    set n := Fintype.card V
    have hN : Fintype.card (V × Fin (2 * m)) = 2 * m * n := by
      rw [Fintype.card_prod, Fintype.card_fin, mul_comm]
    rw [hN] at hU_card hle
    have hU_ge : m * n ≤ #U.toFinset := by
      rw [Set.ncard_eq_toFinset_card'] at hU_card
      have : 2 * m * n = 2 * (m * n) := by ring
      omega
    obtain ⟨U₀, hU₀_sub, hU₀_card⟩ := Finset.exists_subset_card_eq hU_ge
    have hU₀_edges : 50 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard ≤ (2 * m * n) ^ 2 := by
      have hmono : (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard ≤ (H.induce U).edgeSet.ncard := by
        have h1 : 2 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard =
            ∑ p ∈ U₀, #(U₀.filter (H.Adj p)) := two_mul_induce_edgeSet_ncard H U₀
        have h2 : 2 * (H.induce U).edgeSet.ncard =
            ∑ p ∈ U.toFinset, #(U.toFinset.filter (H.Adj p)) := by
          have h2' := two_mul_induce_edgeSet_ncard H U.toFinset
          rwa [Set.coe_toFinset] at h2'
        have hle2 : ∑ p ∈ U₀, #(U₀.filter (H.Adj p)) ≤ ∑ p ∈ U.toFinset, #(U.toFinset.filter (H.Adj p)) :=
          (Finset.sum_le_sum (fun p _ => Finset.card_le_card (Finset.filter_subset_filter _ hU₀_sub))).trans
            (Finset.sum_le_sum_of_subset hU₀_sub)
        omega
      omega
    let a₀ : V → ℕ := fun v => #(Finset.univ.filter (fun i : Fin (2 * m) => (v, i) ∈ U₀))
    have ha₀_le : ∀ v, a₀ v ≤ 2 * m := fun v =>
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    have ha₀_sum : ∑ v : V, a₀ v = m * n := by
      rw [← hU₀_card]
      have hbij : #U₀ = ∑ v : V, #(Finset.univ.filter (fun i : Fin (2 * m) => (v, i) ∈ U₀)) := by
        have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := U₀) (t := (Finset.univ : Finset V))
          (fun _ _ => Finset.mem_univ _)
        rw [this]
        apply Finset.sum_congr rfl; intro v _
        refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
        · intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            have hp' := Finset.mem_filter.mp hp; simpa [← hp'.2] using hp'.1⟩
        · intro p1 hp1 p2 hp2 heq
          exact Prod.ext ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm) heq
        · intro i hi
          exact ⟨(v, i), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩, rfl⟩
      exact hbij.symm
    have hQ₀_eq : 2 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard =
        ∑ u : V, ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      have h1 : ∀ u : V, ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀),
          #(U₀.filter (H.Adj (u, i))) = ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0 := by
        intro u
        have hdeg : ∀ i : Fin (2 * m), #(U₀.filter (H.Adj (u, i))) =
            ∑ v : V, if G.Adj u v then a₀ v else 0 := by
          intro i
          have hfib := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
            (s := U₀.filter (H.Adj (u, i))) (t := (Finset.univ : Finset V)) (fun _ _ => Finset.mem_univ _)
          rw [hfib]
          apply Finset.sum_congr rfl; intro v _
          by_cases huv : G.Adj u v
          · rw [if_pos huv]
            refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
            · intro p hp
              have hp' := Finset.mem_filter.mp hp
              have hp1 := (Finset.mem_filter.mp hp'.1).1
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [← hp'.2] using hp1⟩
            · intro p1 hp1 p2 hp2 heq
              exact Prod.ext ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm) heq
            · intro j hj
              exact ⟨(v, j), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, huv⟩, rfl⟩, rfl⟩
          · rw [if_neg huv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp heq
            have hadj : G.Adj u p.1 := (Finset.mem_filter.mp hp).2
            rw [heq] at hadj; exact huv hadj
        calc ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀), #(U₀.filter (H.Adj (u, i)))
            = ∑ _i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀), ∑ v : V, if G.Adj u v then a₀ v else 0 :=
              Finset.sum_congr rfl (fun i _ => hdeg i)
          _ = a₀ u * ∑ v : V, if G.Adj u v then a₀ v else 0 := by rw [Finset.sum_const, smul_eq_mul]
          _ = ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0 := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; split_ifs <;> ring
      have hfibU : ∑ p ∈ U₀, #(U₀.filter (H.Adj p)) =
          ∑ u : V, ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => (u, i) ∈ U₀), #(U₀.filter (H.Adj (u, i))) := by
        have hpart := Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (s := U₀) (t := (Finset.univ : Finset V))
          (fun _ _ => Finset.mem_univ _) (fun p => #(U₀.filter (H.Adj p)))
        rw [← hpart]
        apply Finset.sum_congr rfl; intro u _
        refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
        · intro p hp
          have hp' := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [← hp'.2] using hp'.1⟩
        · intro p1 hp1 p2 hp2 heq
          exact Prod.ext ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm) heq
        · intro i hi
          exact ⟨(u, i), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩, rfl⟩
        · intro p hp
          have hp' := (Finset.mem_filter.mp hp).2
          cases p with | mk v j => dsimp at hp'; subst hp'; rfl
      rw [hfibU]
      exact Finset.sum_congr rfl (fun u _ => h1 u)
    let valid : Finset (V → Fin (2 * m + 1)) :=
      Finset.univ.filter (fun f => ∑ v : V, (f v).val = m * n)
    let f₀ : V → Fin (2 * m + 1) := fun v => ⟨a₀ v, Nat.lt_succ_of_le (ha₀_le v)⟩
    have hf₀_mem : f₀ ∈ valid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₀_sum⟩
    let Q : (V → Fin (2 * m + 1)) → ℕ :=
      fun f => ∑ x : V, ∑ y : V, if G.Adj x y then (f x).val * (f y).val else 0
    let frac : (V → Fin (2 * m + 1)) → ℕ :=
      fun f => #(Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m))
    let score : (V → Fin (2 * m + 1)) → ℕ := fun f => (n + 1) * Q f + frac f
    obtain ⟨f, hf_mem, hf_min⟩ := Finset.exists_min_image valid score ⟨f₀, hf₀_mem⟩
    have hf_sum : ∑ v : V, (f v).val = m * n := (Finset.mem_filter.mp hf_mem).2
    have hQf_le : Q f ≤ Q f₀ := by
      have hsc := hf_min f₀ hf₀_mem
      dsimp only [score] at hsc
      have hfrac_le : frac f₀ ≤ n := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [n])
      have h1 : (n + 1) * Q f ≤ (n + 1) * Q f₀ + n := by omega
      by_contra hgt
      have : Q f₀ + 1 ≤ Q f := by omega
      have : (n + 1) * (Q f₀ + 1) ≤ (n + 1) * Q f := Nat.mul_le_mul_left (n + 1) this
      have : (n + 1) * (Q f₀ + 1) = (n + 1) * Q f₀ + n + 1 := by ring
      omega
    have hfrac_le1 : frac f ≤ 1 := by
      by_contra hgt
      dsimp only [frac] at hgt
      obtain ⟨u0, hu0, w0, hw0, hne0⟩ := Finset.one_lt_card.mp (by omega : 1 < #(Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m)))
      have hu0' := (Finset.mem_filter.mp hu0).2
      have hw0' := (Finset.mem_filter.mp hw0).2
      have hpair : ∃ u w : V, u ≠ w ∧ 0 < (f u).val ∧ (f u).val < 2 * m ∧ 0 < (f w).val ∧ (f w).val < 2 * m ∧
          (∑ x : V, if G.Adj u x then (f x).val else 0) ≤ ∑ x : V, if G.Adj w x then (f x).val else 0 := by
        by_cases hle_s : (∑ x : V, if G.Adj u0 x then (f x).val else 0) ≤ ∑ x : V, if G.Adj w0 x then (f x).val else 0
        · exact ⟨u0, w0, hne0, hu0'.1, hu0'.2, hw0'.1, hw0'.2, hle_s⟩
        · exact ⟨w0, u0, hne0.symm, hw0'.1, hw0'.2, hu0'.1, hu0'.2, by omega⟩
      obtain ⟨u, w, huw, hu_lo, hu_hi, hw_lo, hw_hi, hs_le⟩ := hpair
      set δ := min (2 * m - (f u).val) (f w).val
      have hδ_pos : 1 ≤ δ := by omega
      have hδ_u : (f u).val + δ ≤ 2 * m := by omega
      have hδ_w : δ ≤ (f w).val := Nat.min_le_right _ _
      let g : V → Fin (2 * m + 1) := fun x =>
        if x = u then ⟨(f u).val + δ, by omega⟩
        else if x = w then ⟨(f w).val - δ, by omega⟩
        else f x
      have hg_val : ∀ x : V, (g x).val = if x = u then (f u).val + δ else if x = w then (f w).val - δ else (f x).val := by
        intro x; by_cases hxu : x = u
        · subst hxu; simp [g]
        · by_cases hxw : x = w
          · subst hxw; simp [g, hxu]
          · simp [g, hxu, hxw]
      have hg_mem : g ∈ valid := by
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
        have hsum_g : ∑ x : V, (g x).val = ∑ x : V, (f x).val := by
          have hsub : ∀ x : V, (g x).val + (if x = w then δ else 0) = (f x).val + (if x = u then δ else 0) := by
            intro x; rw [hg_val]
            by_cases hxu : x = u
            · subst hxu; simp [huw]
            · by_cases hxw : x = w
              · subst hxw; simp [hxu]; omega
              · simp [hxu, hxw]
          have h1 := Finset.sum_congr rfl (fun x (_ : x ∈ (Finset.univ : Finset V)) => hsub x)
          simp_rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
          omega
        omega
      have hQg_le : Q g ≤ Q f := by
        have hsh := shift_quad_le G (fun x => (f x).val) huw hδ_w hs_le
        have hEq : Q g = ∑ x : V, ∑ y : V, if G.Adj x y then
            (if x = u then (f u).val + δ else if x = w then (f w).val - δ else (f x).val) *
            (if y = u then (f u).val + δ else if y = w then (f w).val - δ else (f y).val) else 0 := by
          apply Finset.sum_congr rfl; intro x _
          apply Finset.sum_congr rfl; intro y _
          rw [hg_val x, hg_val y]
        rw [hEq]; exact hsh
      have hfrac_lt : frac g < frac f := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          have hx' := (Finset.mem_filter.mp hx).2
          rw [hg_val] at hx'
          apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
          by_cases hxu : x = u
          · subst hxu; exact ⟨hu_lo, hu_hi⟩
          · by_cases hxw : x = w
            · subst hxw; exact ⟨hw_lo, hw_hi⟩
            · simp [hxu, hxw] at hx'; exact hx'
        · intro heq
          by_cases hhit : (f u).val + δ = 2 * m
          · have hu_in : u ∈ Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_lo, hu_hi⟩
            rw [← heq] at hu_in
            have := (Finset.mem_filter.mp hu_in).2
            rw [hg_val] at this; simp [hhit] at this
          · have hw_zero : (f w).val - δ = 0 := by omega
            have hw_in : w ∈ Finset.univ.filter (fun v : V => 0 < (f v).val ∧ (f v).val < 2 * m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_lo, hw_hi⟩
            rw [← heq] at hw_in
            have := (Finset.mem_filter.mp hw_in).2
            rw [hg_val] at this; simp [huw.symm, hw_zero] at this
      have hsc_lt : score g < score f := by
        dsimp only [score]
        have : (n + 1) * Q g ≤ (n + 1) * Q f := Nat.mul_le_mul_left (n + 1) hQg_le
        omega
      have := hf_min g hg_mem
      omega
    let S : Finset V := Finset.univ.filter (fun v => (f v).val = 2 * m)
    have hS_card : 2 * #S + 1 ≥ n := by
      let F : Finset V := Finset.univ.filter (fun v => 0 < (f v).val ∧ (f v).val < 2 * m)
      have hsum_le : ∑ v : V, (f v).val ≤ 2 * m * #S + (2 * m - 1) * #F := by
        have hsplit : ∀ v : V, (f v).val ≤ (if v ∈ S then 2 * m else 0) + (if v ∈ F then 2 * m - 1 else 0) := by
          intro v
          by_cases hvS : (f v).val = 2 * m
          · have : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS⟩
            simp [this, hvS]
          · by_cases hv0 : (f v).val = 0
            · omega
            · have hvF : v ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by have := (f v).isLt; omega⟩
              simp [hvF]; have := (f v).isLt; omega
        calc ∑ v : V, (f v).val
            ≤ ∑ v : V, ((if v ∈ S then 2 * m else 0) + (if v ∈ F then 2 * m - 1 else 0)) :=
              Finset.sum_le_sum (fun v _ => hsplit v)
          _ = (∑ v : V, if v ∈ S then 2 * m else 0) + (∑ v : V, if v ∈ F then 2 * m - 1 else 0) :=
              Finset.sum_add_distrib
          _ = 2 * m * #S + (2 * m - 1) * #F := by
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
                ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
              ring
      have hF1 : #F ≤ 1 := hfrac_le1
      have hbound_n : m * n ≤ 2 * m * #S + (2 * m - 1) := by
        have : (2 * m - 1) * #F ≤ 2 * m - 1 := by
          calc (2 * m - 1) * #F ≤ (2 * m - 1) * 1 := Nat.mul_le_mul_left _ hF1
            _ = 2 * m - 1 := mul_one _
        omega
      have : m * n < m * (2 * #S + 2) := by
        have : m * (2 * #S + 2) = 2 * m * #S + 2 * m := by ring
        omega
      have : n < 2 * #S + 2 := Nat.lt_of_mul_lt_mul_left this
      omega
    have hQS : (2 * m) ^ 2 * (2 * (G.induce (S : Set V)).edgeSet.ncard) ≤ Q f := by
      rw [two_mul_induce_edgeSet_ncard]
      have h1 : (2 * m) ^ 2 * ∑ u ∈ S, #(S.filter (G.Adj u)) =
          ∑ u ∈ S, ∑ v ∈ S, if G.Adj u v then (2 * m) * (2 * m) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro u _
        rw [Finset.card_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro v _
        split_ifs <;> ring
      rw [h1]
      calc (∑ u ∈ S, ∑ v ∈ S, if G.Adj u v then (2 * m) * (2 * m) else 0)
          = (∑ u ∈ S, ∑ v ∈ S, if G.Adj u v then (f u).val * (f v).val else 0) := by
            apply Finset.sum_congr rfl; intro u hu
            apply Finset.sum_congr rfl; intro v hv
            rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2]
        _ ≤ (∑ u ∈ S, ∑ v : V, if G.Adj u v then (f u).val * (f v).val else 0) :=
            Finset.sum_le_sum (fun u _ => Finset.sum_le_sum_of_subset (Finset.subset_univ S))
        _ ≤ Q f := Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    have h50S : 50 * (G.induce (S : Set V)).edgeSet.ncard > n ^ 2 := by
      apply hH (S : Set V)
      rw [Set.ncard_coe_finset]
      exact hS_card
    have h50_bad : 25 * Q f ≤ (2 * m) ^ 2 * n ^ 2 := by
      have hQf0 : 25 * Q f₀ = 50 * (H.induce (U₀ : Set (V × Fin (2 * m)))).edgeSet.ncard := by
        change 25 * (∑ u : V, ∑ v : V, if G.Adj u v then a₀ u * a₀ v else 0) = _
        rw [← hQ₀_eq]; ring
      have hsq : (2 * m * n) ^ 2 = (2 * m) ^ 2 * n ^ 2 := by ring
      omega
    have h50_good : (2 * m) ^ 2 * n ^ 2 < 25 * ((2 * m) ^ 2 * (2 * (G.induce (S : Set V)).edgeSet.ncard)) := by
      have hpos : 0 < (2 * m) ^ 2 := by positivity
      have h1 : (2 * m) ^ 2 * n ^ 2 < (2 * m) ^ 2 * (50 * (G.induce (S : Set V)).edgeSet.ncard) :=
        Nat.mul_lt_mul_of_pos_left h50S hpos
      have h2 : (2 * m) ^ 2 * (50 * (G.induce (S : Set V)).edgeSet.ncard) =
          25 * ((2 * m) ^ 2 * (2 * (G.induce (S : Set V)).edgeSet.ncard)) := by ring
      omega
    omega
  exact ⟨H, hAdj, hH_TF, hH_sparse, hH_edges, hH_deg⟩

/-- Mantel's theorem for the directed adjacency sum of any induced subset R in a triangle-free graph. -/
lemma mantel_directed_sum {V : Type} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hTF : G.CliqueFree 3) (R : Finset V) :
    2 * (∑ u ∈ R, #(R.filter (G.Adj u))) ≤ (#R) ^ 2 := by
  let d : V → ℕ := fun u => #(R.filter (G.Adj u))
  set D := ∑ u ∈ R, d u
  have hadj_sum : ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), (d u + d v) ≤ #R * D := by
    have hpair : ∀ u ∈ R, ∀ v ∈ R.filter (G.Adj u), d u + d v ≤ #R := by
      intro u _ v hv
      have hv' := Finset.mem_filter.mp hv
      have hdisj : Disjoint (R.filter (G.Adj u)) (R.filter (G.Adj v)) := by
        rw [Finset.disjoint_left]
        intro w hwu hwv
        exact not_adj_of_cliqueFree_three hTF hv'.2 (Finset.mem_filter.mp hwv).2 (Finset.mem_filter.mp hwu).2
      calc d u + d v = #(R.filter (G.Adj u) ∪ R.filter (G.Adj v)) := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ #R := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    calc ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), (d u + d v)
        ≤ ∑ u ∈ R, ∑ _v ∈ R.filter (G.Adj u), #R :=
          Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => hpair u hu v hv))
      _ = ∑ u ∈ R, d u * #R := by
          apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_const, smul_eq_mul]
      _ = #R * D := by rw [← Finset.sum_mul, mul_comm]
  have htwice : ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), (d u + d v) = 2 * ∑ u ∈ R, (d u) ^ 2 := by
    have h1 : ∑ u ∈ R, ∑ _v ∈ R.filter (G.Adj u), d u = ∑ u ∈ R, (d u) ^ 2 := by
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.sum_const, smul_eq_mul]; ring
    have h2 : ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), d v = ∑ v ∈ R, (d v) ^ 2 := by
      calc ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), d v
          = ∑ u ∈ R, ∑ v ∈ R, if G.Adj u v then d v else 0 := by
            apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_filter]
        _ = ∑ v ∈ R, ∑ u ∈ R, if G.Adj u v then d v else 0 := Finset.sum_comm
        _ = ∑ v ∈ R, ∑ u ∈ R, if G.Adj v u then d v else 0 := by
            apply Finset.sum_congr rfl; intro v _
            apply Finset.sum_congr rfl; intro u _; simp [G.adj_comm]
        _ = ∑ v ∈ R, ∑ _u ∈ R.filter (G.Adj v), d v := by
            apply Finset.sum_congr rfl; intro v _; rw [← Finset.sum_filter]
        _ = ∑ v ∈ R, (d v) ^ 2 := by
            apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_const, smul_eq_mul]; ring
    calc ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), (d u + d v)
        = (∑ u ∈ R, ∑ _v ∈ R.filter (G.Adj u), d u) + (∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), d v) := by
          simp_rw [Finset.sum_add_distrib]
      _ = 2 * ∑ u ∈ R, (d u) ^ 2 := by rw [h1, h2]; ring
  have hcs : D ^ 2 ≤ #R * ∑ u ∈ R, (d u) ^ 2 := by
    have hnonneg : (0 : ℤ) ≤ ∑ u ∈ R, ∑ v ∈ R, ((d u : ℤ) - (d v : ℤ)) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hexp : ∑ u ∈ R, ∑ v ∈ R, ((d u : ℤ) - (d v : ℤ)) ^ 2 =
        2 * (#R : ℤ) * (∑ u ∈ R, ((d u : ℤ) ^ 2)) - 2 * ((∑ u ∈ R, (d u : ℤ)) ^ 2) := by
      have hsub : ∀ u ∈ R, ∑ v ∈ R, ((d u : ℤ) - (d v : ℤ)) ^ 2 =
          (#R : ℤ) * (d u : ℤ) ^ 2 - 2 * (d u : ℤ) * (∑ v ∈ R, (d v : ℤ)) + ∑ v ∈ R, (d v : ℤ) ^ 2 := by
        intro u _
        have hstep : ∀ v ∈ R, ((d u : ℤ) - (d v : ℤ)) ^ 2 =
            (d u : ℤ) ^ 2 - 2 * (d u : ℤ) * (d v : ℤ) + (d v : ℤ) ^ 2 := fun v _ => by ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      have hmul2 : ∑ u ∈ R, 2 * (d u : ℤ) = 2 * ∑ u ∈ R, (d u : ℤ) := (Finset.mul_sum _ _ _).symm
      rw [hmul2]; ring
    have hz : ((D : ℤ) ^ 2) ≤ (#R : ℤ) * ((∑ u ∈ R, (d u) ^ 2 : ℕ) : ℤ) := by
      have hD : (D : ℤ) = ∑ u ∈ R, (d u : ℤ) := by simp [D]
      have hS : ((∑ u ∈ R, (d u) ^ 2 : ℕ) : ℤ) = ∑ u ∈ R, (d u : ℤ) ^ 2 := by simp
      rw [hD, hS]; linarith
    exact_mod_cast hz
  by_cases hD0 : D = 0
  · rw [hD0]; omega
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    have hmul : 2 * D * D ≤ (#R) ^ 2 * D := by
      calc 2 * D * D = 2 * D ^ 2 := by ring
        _ ≤ 2 * (#R * ∑ u ∈ R, (d u) ^ 2) := Nat.mul_le_mul_left 2 hcs
        _ = #R * (2 * ∑ u ∈ R, (d u) ^ 2) := by ring
        _ ≤ #R * (#R * D) := Nat.mul_le_mul_left (#R) (by omega)
        _ = (#R) ^ 2 * D := by ring
    exact Nat.le_of_mul_le_mul_right hmul hDpos

/-- Theorem G ({C_3, C_5}-Free / Odd Girth 5 Theorem):
    Every triangle-free counterexample to Erdős #128 MUST contain a 5-cycle C_5.
    Proved completely elementarily for all finite n via the 2m-blowup theorem (m = 5),
    Mantel's theorem on R = V \ (N_1 ∪ {v} ∪ N_2), and exact SOS elimination between
    candidates N_1 ∪ S' and ({v} ∪ N_2) ∪ S. -/
theorem exists_fiveCycle {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ∃ a b c d e : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a := by
  classical
  by_contra hnoC5
  have hn12 : 12 ≤ Fintype.card V := twelve_le_card G hTF hH
  set n := Fintype.card V
  -- Blow up G by 2*5 = 10 so N = 10*n is even, >= 120, and 25 | N^2 exactly!
  obtain ⟨H, hAdj, hH_TF, hH_sparse, _, _⟩ := blowup_counterexample G hTF hH 5 (by omega)
  let W := V × Fin (2 * 5)
  have hN_eq : Fintype.card W = 10 * n := by
    simp [W, Fintype.card_prod, Fintype.card_fin, n]; ring
  set N := Fintype.card W
  set k := 5 * n
  set T := 4 * n ^ 2
  have hN2k : N = 2 * k := by omega
  have hk60 : 60 ≤ k := by omega
  have h25T : 25 * T = N ^ 2 := by
    have : N = 10 * n := hN_eq
    rw [this]; dsimp only [T]; ring
  -- H has no closed 5-walk (any closed 5-walk in H projects to a simple C_5 in G since G is triangle-free)
  have hH_no5 : ∀ p0 p1 p2 p3 p4 : W,
      H.Adj p0 p1 → H.Adj p1 p2 → H.Adj p2 p3 → H.Adj p3 p4 → H.Adj p4 p0 → False := by
    intro p0 p1 p2 p3 p4 h01 h12 h23 h34 h40
    have g01 : G.Adj p0.1 p1.1 := (hAdj p0.1 p0.2 p1.1 p1.2).mp h01
    have g12 : G.Adj p1.1 p2.1 := (hAdj p1.1 p1.2 p2.1 p2.2).mp h12
    have g23 : G.Adj p2.1 p3.1 := (hAdj p2.1 p2.2 p3.1 p3.2).mp h23
    have g34 : G.Adj p3.1 p4.1 := (hAdj p3.1 p3.2 p4.1 p4.2).mp h34
    have g40 : G.Adj p4.1 p0.1 := (hAdj p4.1 p4.2 p0.1 p0.2).mp h40
    apply hnoC5
    refine ⟨p0.1, p1.1, p2.1, p3.1, p4.1, G.ne_of_adj g01, ?_, ?_, (G.ne_of_adj g40).symm,
      G.ne_of_adj g12, ?_, ?_, G.ne_of_adj g23, ?_, G.ne_of_adj g34, g01, g12, g23, g34, g40⟩
    · intro h; rw [h] at g40; exact not_adj_of_cliqueFree_three hTF g23 g34 g40.symm
    · intro h; rw [h] at g01; exact not_adj_of_cliqueFree_three hTF g01 g12 g23.symm
    · intro h; rw [h] at g01; exact not_adj_of_cliqueFree_three hTF g34 g40 g01.symm
    · intro h; rw [h] at g12; exact not_adj_of_cliqueFree_three hTF g12 g23 g34.symm
    · intro h; rw [h] at g12; exact not_adj_of_cliqueFree_three hTF g40 g01 g12.symm
  -- Pick maximum-degree vertex v in H
  have hW_ne : (Finset.univ : Finset W).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have : N = 0 := by dsimp only [N]; rw [← Finset.card_univ, hemp, Finset.card_empty]
    omega
  obtain ⟨v, _, hv_max⟩ := Finset.exists_max_image (Finset.univ : Finset W)
    (fun w => #(Finset.univ.filter (H.Adj w))) hW_ne
  let N₁ : Finset W := Finset.univ.filter (H.Adj v)
  let N₂ : Finset W := (Finset.univ \ insert v N₁).filter (fun w => ∃ u ∈ N₁, H.Adj u w)
  let I : Finset W := insert v N₂
  let R : Finset W := Finset.univ \ (N₁ ∪ I)
  set x := #N₁
  set y := #I
  set r := #R
  have hN₁_indep : ∀ a ∈ N₁, ∀ b ∈ N₁, ¬ H.Adj a b := filter_adj_indep hH_TF Finset.univ v
  have hI_indep : ∀ a ∈ I, ∀ b ∈ I, ¬ H.Adj a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with ha_v | ha2
    · rcases Finset.mem_insert.mp hb with hb_v | hb2
      · rw [ha_v, hb_v] at hab; exact H.loopless.irrefl _ hab
      · rw [ha_v] at hab
        have hnot : b ∉ insert v N₁ := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb2).1).2
        exact hnot (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩))
    · rcases Finset.mem_insert.mp hb with hb_v | hb2
      · rw [hb_v] at hab
        have hnot : a ∉ insert v N₁ := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha2).1).2
        exact hnot (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩))
      · obtain ⟨u₁, hu₁, hadj₁⟩ := (Finset.mem_filter.mp ha2).2
        obtain ⟨u₂, hu₂, hadj₂⟩ := (Finset.mem_filter.mp hb2).2
        have hvu₁ : H.Adj v u₁ := (Finset.mem_filter.mp hu₁).2
        have hvu₂ : H.Adj v u₂ := (Finset.mem_filter.mp hu₂).2
        exact hH_no5 v u₁ a b u₂ hvu₁ hadj₁ hab hadj₂.symm hvu₂.symm
  have hdisj_N₁I : Disjoint N₁ I := by
    rw [Finset.disjoint_left]
    intro w hw1 hwI
    rcases Finset.mem_insert.mp hwI with hw_v | hw2
    · rw [hw_v] at hw1; exact H.loopless.irrefl _ (Finset.mem_filter.mp hw1).2
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw2).1).2 (Finset.mem_insert_of_mem hw1)
  have hdisj_N₁R : Disjoint N₁ R :=
    Finset.disjoint_sdiff.mono_left Finset.subset_union_left
  have hdisj_IR : Disjoint I R :=
    Finset.disjoint_sdiff.mono_left Finset.subset_union_right
  have hpart : x + y + r = N := by
    have hu : #(N₁ ∪ I) = x + y := Finset.card_union_of_disjoint hdisj_N₁I
    have hr : #R = N - #(N₁ ∪ I) := by
      dsimp only [R, N]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have hle : #(N₁ ∪ I) ≤ N := by
      dsimp only [N]; rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    omega
  -- Apply Theorem A (α < 2N/5) to N₁ and I
  have h5x : 5 * x < 2 * N := by
    have h1 := five_mul_indep_lt_two_mul_card H hH_TF hH_sparse (N₁ : Set W)
      (fun a ha b hb _ hab => hN₁_indep a ha b hb hab)
    rwa [Set.ncard_coe_finset] at h1
  have h5y : 5 * y < 2 * N := by
    have h1 := five_mul_indep_lt_two_mul_card H hH_TF hH_sparse (I : Set W)
      (fun a ha b hb _ hab => hI_indep a ha b hb hab)
    rwa [Set.ncard_coe_finset] at h1
  set t := k - x
  set s := k - y
  have hr25 : 25 ≤ r := by omega
  have ht13 : 13 ≤ t := by omega
  have hs13 : 13 ≤ s := by omega
  have ht_le_r : t ≤ r := by omega
  have hs_le_r : s ≤ r := by omega
  -- Zero cross-edges between N₁ and R
  have hN₁R_zero : ∑ w ∈ R, #(N₁.filter (H.Adj w)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu hadj
    have hw_not : w ∉ N₁ ∪ I := (Finset.mem_sdiff.mp hw).2
    have hw_not_vN₁ : w ∉ insert v N₁ := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with hw_v | hmem1
      · rw [hw_v] at hw_not; exact hw_not (Finset.mem_union_right _ (Finset.mem_insert_self v N₂))
      · exact hw_not (Finset.mem_union_left _ hmem1)
    have hw_N₂ : w ∈ N₂ :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw_not_vN₁⟩, ⟨u, hu, hadj.symm⟩⟩
    exact hw_not (Finset.mem_union_right _ (Finset.mem_insert_of_mem hw_N₂))
  -- Every k-subset of W satisfies T < 2 * e(H[S])
  have hk_gt : ∀ S : Finset W, #S = k → T < 2 * (H.induce (S : Set W)).edgeSet.ncard := by
    intro S hS
    have h50 : 50 * (H.induce (S : Set W)).edgeSet.ncard > N ^ 2 := by
      apply hH_sparse (S : Set W)
      rw [Set.ncard_coe_finset, hS]
      omega
    omega
  set D₀ := ∑ u ∈ R, #(R.filter (H.Adj u))
  set E₁ := ∑ w ∈ R, #(I.filter (H.Adj w))
  -- Candidate 1: N₁ ∪ S' for S' ∈ R.powersetCard t
  have hC1 : N ^ 2 * r * (r - 1) < 25 * t * (t - 1) * D₀ := by
    have havg := avg_indep_union_gt H hdisj_N₁R hN₁_indep (by omega : 1 ≤ t) ht_le_r (by omega : 2 ≤ r)
      (fun S' hS' => hk_gt (N₁ ∪ S') (by
        rw [Finset.card_union_of_disjoint (hdisj_N₁R.mono_right (Finset.mem_powersetCard.mp hS').1),
          (Finset.mem_powersetCard.mp hS').2]; omega))
    rw [hN₁R_zero, mul_zero, zero_add] at havg
    change T * r * (r - 1) < t * (t - 1) * D₀ at havg
    have hmul := Nat.mul_lt_mul_of_pos_left havg (by omega : 0 < 25)
    have hL : 25 * (T * r * (r - 1)) = N ^ 2 * r * (r - 1) := by rw [← h25T]; ring
    have hR : 25 * (t * (t - 1) * D₀) = 25 * t * (t - 1) * D₀ := by ring
    omega
  -- Mantel on R gives 2 * D₀ <= r^2, which forces 2 * x < k!
  have h2x_lt_k : 2 * x < k := by
    by_contra hge
    push Not at hge
    have hM : 2 * D₀ ≤ r ^ 2 := mantel_directed_sum hH_TF R
    have h2C1 : 2 * N ^ 2 * r * (r - 1) < 25 * t * (t - 1) * r ^ 2 := by
      calc 2 * N ^ 2 * r * (r - 1)
          = 2 * (N ^ 2 * r * (r - 1)) := by ring
        _ < 2 * (25 * t * (t - 1) * D₀) := Nat.mul_lt_mul_of_pos_left hC1 (by omega)
        _ = 25 * t * (t - 1) * (2 * D₀) := by ring
        _ ≤ 25 * t * (t - 1) * r ^ 2 := Nat.mul_le_mul_left _ hM
    have ht_le : 2 * t ≤ k := by omega
    have htt : 4 * (t * (t - 1)) ≤ k ^ 2 := by
      have h1 : t * (t - 1) ≤ t ^ 2 := by
        calc t * (t - 1) ≤ t * t := Nat.mul_le_mul_left t (by omega)
          _ = t ^ 2 := by ring
      have h2 : 4 * t ^ 2 ≤ k ^ 2 := by
        calc 4 * t ^ 2 = (2 * t) ^ 2 := by ring
          _ ≤ k ^ 2 := Nat.pow_le_pow_left ht_le 2
      omega
    have hbad : 32 * k ^ 2 * r * (r - 1) < 25 * k ^ 2 * r ^ 2 := by
      calc 32 * k ^ 2 * r * (r - 1)
          = 4 * (2 * N ^ 2 * r * (r - 1)) := by rw [hN2k]; ring
        _ < 4 * (25 * t * (t - 1) * r ^ 2) := Nat.mul_lt_mul_of_pos_left h2C1 (by omega)
        _ = 25 * (4 * (t * (t - 1))) * r ^ 2 := by ring
        _ ≤ 25 * k ^ 2 * r ^ 2 := by
            have := Nat.mul_le_mul_left 25 htt
            exact Nat.mul_le_mul_right (r ^ 2) this
    have hlt_r : 32 * (r - 1) < 25 * r := by
      have h1 : 32 * (r - 1) * (k ^ 2 * r) < 25 * r * (k ^ 2 * r) := by
        have hL : 32 * (r - 1) * (k ^ 2 * r) = 32 * k ^ 2 * r * (r - 1) := by ring
        have hR : 25 * r * (k ^ 2 * r) = 25 * k ^ 2 * r ^ 2 := by ring
        omega
      exact Nat.lt_of_mul_lt_mul_right h1
    omega
  -- Candidate 2: I ∪ S for S ∈ R.powersetCard s
  have hC2 : N ^ 2 * r * (r - 1) < 50 * s * (r - 1) * E₁ + 25 * s * (s - 1) * D₀ := by
    have havg := avg_indep_union_gt H hdisj_IR hI_indep (by omega : 1 ≤ s) hs_le_r (by omega : 2 ≤ r)
      (fun S hS => hk_gt (I ∪ S) (by
        rw [Finset.card_union_of_disjoint (hdisj_IR.mono_right (Finset.mem_powersetCard.mp hS).1),
          (Finset.mem_powersetCard.mp hS).2]; omega))
    change T * r * (r - 1) < 2 * s * (r - 1) * E₁ + s * (s - 1) * D₀ at havg
    have hmul := Nat.mul_lt_mul_of_pos_left havg (by omega : 0 < 25)
    have hL : 25 * (T * r * (r - 1)) = N ^ 2 * r * (r - 1) := by rw [← h25T]; ring
    have hR : 25 * (2 * s * (r - 1) * E₁ + s * (s - 1) * D₀) =
        50 * s * (r - 1) * E₁ + 25 * s * (s - 1) * D₀ := by ring
    omega
  -- Max-degree constraint on R: E₁ + D₀ <= r * x
  have hED : E₁ + D₀ ≤ r * x := by
    have hpt : ∀ w ∈ R, #(I.filter (H.Adj w)) + #(R.filter (H.Adj w)) ≤ x := by
      intro w _
      have hdisj_w : Disjoint (I.filter (H.Adj w)) (R.filter (H.Adj w)) :=
        hdisj_IR.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      calc #(I.filter (H.Adj w)) + #(R.filter (H.Adj w))
          = #(I.filter (H.Adj w) ∪ R.filter (H.Adj w)) := (Finset.card_union_of_disjoint hdisj_w).symm
        _ ≤ #(Finset.univ.filter (H.Adj w)) :=
            Finset.card_le_card (Finset.union_subset
              (Finset.filter_subset_filter _ (Finset.subset_univ _))
              (Finset.filter_subset_filter _ (Finset.subset_univ _)))
        _ ≤ x := hv_max w (Finset.mem_univ w)
    calc E₁ + D₀ = ∑ w ∈ R, (#(I.filter (H.Adj w)) + #(R.filter (H.Adj w))) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ _w ∈ R, x := Finset.sum_le_sum hpt
      _ = r * x := by rw [Finset.sum_const, smul_eq_mul]
  -- Eliminate E₁ and D₀ linearly between hC1 and hC2
  set A := 2 * (r - 1) - (s - 1)
  have hA_eq : A + (s - 1) = 2 * (r - 1) := by omega
  have hA_pos : 0 < A := by omega
  have hC2' : N ^ 2 * r * (r - 1) + 25 * s * A * D₀ < 50 * s * (r - 1) * r * x := by
    have hmulED : 50 * s * (r - 1) * E₁ + 50 * s * (r - 1) * D₀ ≤ 50 * s * (r - 1) * r * x := by
      have h1 := Nat.mul_le_mul_left (50 * s * (r - 1)) hED
      have hL : 50 * s * (r - 1) * (E₁ + D₀) = 50 * s * (r - 1) * E₁ + 50 * s * (r - 1) * D₀ := by ring
      have hR : 50 * s * (r - 1) * (r * x) = 50 * s * (r - 1) * r * x := by ring
      omega
    have hsplit : 25 * s * A * D₀ + 25 * s * (s - 1) * D₀ = 50 * s * (r - 1) * D₀ := by
      calc 25 * s * A * D₀ + 25 * s * (s - 1) * D₀
          = 25 * s * (A + (s - 1)) * D₀ := by ring
        _ = 25 * s * (2 * (r - 1)) * D₀ := by rw [hA_eq]
        _ = 50 * s * (r - 1) * D₀ := by ring
    omega
  have hcomb : (s * A + t * (t - 1)) * N ^ 2 < 50 * t * (t - 1) * s * x := by
    have h1 := Nat.mul_lt_mul_of_pos_left hC1 (Nat.mul_pos (by omega : 0 < s) hA_pos)
    have h2 := Nat.mul_lt_mul_of_pos_left hC2' (Nat.mul_pos (by omega : 0 < t) (by omega : 0 < t - 1))
    have hcancel : (s * A + t * (t - 1)) * N ^ 2 * (r * (r - 1)) <
        (50 * t * (t - 1) * s * x) * (r * (r - 1)) := by
      have hD_eq : s * A * (25 * t * (t - 1) * D₀) = t * (t - 1) * (25 * s * A * D₀) := by ring
      have hL1 : (s * A + t * (t - 1)) * N ^ 2 * (r * (r - 1)) =
          s * A * (N ^ 2 * r * (r - 1)) + t * (t - 1) * (N ^ 2 * r * (r - 1)) := by ring
      have hR1 : (50 * t * (t - 1) * s * x) * (r * (r - 1)) =
          t * (t - 1) * (50 * s * (r - 1) * r * x) := by ring
      have h2' : t * (t - 1) * (N ^ 2 * r * (r - 1)) + t * (t - 1) * (25 * s * A * D₀) <
          t * (t - 1) * (50 * s * (r - 1) * r * x) := by
        have : t * (t - 1) * (N ^ 2 * r * (r - 1) + 25 * s * A * D₀) =
            t * (t - 1) * (N ^ 2 * r * (r - 1)) + t * (t - 1) * (25 * s * A * D₀) := by ring
        omega
      omega
    exact Nat.lt_of_mul_lt_mul_right hcancel
  -- Exact SOS contradiction in ℤ via two polynomial identities!
  have hz_comb : (((s : ℤ) * (2 * r - s - 1) + t * (t - 1)) * (2 * k : ℤ) ^ 2) <
      50 * (t : ℤ) * (t - 1) * s * x := by
    have hA_z : (A : ℤ) = 2 * (r : ℤ) - s - 1 := by omega
    have ht1_z : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
    have hN_z : (N : ℤ) = 2 * (k : ℤ) := by omega
    have hcast : (((s * A + t * (t - 1)) * N ^ 2 : ℕ) : ℤ) < ((50 * t * (t - 1) * s * x : ℕ) : ℤ) :=
      Nat.cast_lt.mpr hcomb
    push_cast at hcast
    rw [hA_z, ht1_z, hN_z] at hcast
    exact hcast
  -- Identity 1: 54 * t^2 * x <= (2*k)^3
  have hid1 : 54 * (t : ℤ) ^ 2 * x ≤ (2 * (k : ℤ)) ^ 3 := by
    have hfact : (2 * (k : ℤ)) ^ 3 - 54 * (t : ℤ) ^ 2 * x =
        2 * ((k : ℤ) - 3 * x) ^ 2 * (4 * (k : ℤ) - 3 * x) := by
      have ht_z : (t : ℤ) = (k : ℤ) - x := by omega
      rw [ht_z]; ring
    have hnonneg : (0 : ℤ) ≤ 2 * ((k : ℤ) - 3 * x) ^ 2 * (4 * (k : ℤ) - 3 * x) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by omega)
    linarith only [hfact, hnonneg]
  have hrhs_bound : 27 * (50 * (t : ℤ) * (t - 1) * s * x) ≤ 25 * (s : ℤ) * (2 * (k : ℤ)) ^ 3 := by
    have h1 : 27 * (50 * (t : ℤ) * (t - 1) * s * x) ≤ 25 * (s : ℤ) * (54 * (t : ℤ) ^ 2 * x) := by
      have hfactor : 25 * (s : ℤ) * (54 * (t : ℤ) ^ 2 * x) - 27 * (50 * (t : ℤ) * (t - 1) * s * x) =
          1350 * (s : ℤ) * (x : ℤ) * (t : ℤ) := by ring
      have hnonneg : (0 : ℤ) ≤ 1350 * (s : ℤ) * (x : ℤ) * (t : ℤ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg s)) (Int.natCast_nonneg x))
          (Int.natCast_nonneg t)
      linarith only [hfactor, hnonneg]
    have h2 : 25 * (s : ℤ) * (54 * (t : ℤ) ^ 2 * x) ≤ 25 * (s : ℤ) * (2 * (k : ℤ)) ^ 3 :=
      mul_le_mul_of_nonneg_left hid1 (mul_nonneg (by norm_num) (Int.natCast_nonneg s))
    linarith only [h1, h2]
  have hlt_k : 27 * ((s : ℤ) * (2 * r - s - 1) + t * (t - 1)) < 25 * (s : ℤ) * (2 * (k : ℤ)) := by
    have h1 : 27 * ((s : ℤ) * (2 * r - s - 1) + t * (t - 1)) * (2 * (k : ℤ)) ^ 2 <
        25 * (s : ℤ) * (2 * (k : ℤ)) * (2 * (k : ℤ)) ^ 2 := by
      have hL : 27 * (((s : ℤ) * (2 * r - s - 1) + t * (t - 1)) * (2 * k : ℤ) ^ 2) =
          27 * ((s : ℤ) * (2 * r - s - 1) + t * (t - 1)) * (2 * (k : ℤ)) ^ 2 := by ring
      have hR : 25 * (s : ℤ) * (2 * (k : ℤ)) ^ 3 =
          25 * (s : ℤ) * (2 * (k : ℤ)) * (2 * (k : ℤ)) ^ 2 := by ring
      linarith only [hz_comb, hrhs_bound, hL, hR]
    have hpos : (0 : ℤ) ≤ (2 * (k : ℤ)) ^ 2 := sq_nonneg _
    exact lt_of_mul_lt_mul_right h1 hpos
  -- Identity 2: 27 * (27 * (s * (2*r - s) + t^2) - 25 * s * (2*k)) = (27*s + 2*k - 27*x)^2 + 25*k*(29*k - 54*x)
  have hid2 : 27 * (27 * ((s : ℤ) * (2 * r - s - 1) + t * (t - 1)) - 25 * (s : ℤ) * (2 * (k : ℤ))) =
      (27 * (s : ℤ) + 2 * k - 27 * x) ^ 2 + 25 * (k : ℤ) * (29 * k - 54 * x) - 729 * ((s : ℤ) + t) := by
    have ht_z : (t : ℤ) = (k : ℤ) - x := by omega
    have hs_z : (s : ℤ) = (k : ℤ) - y := by omega
    have hr_z : (r : ℤ) = 2 * (k : ℤ) - x - y := by omega
    rw [ht_z, hs_z, hr_z]; ring
  have hsq_ge : (0 : ℤ) ≤ (27 * (s : ℤ) + 2 * k - 27 * x) ^ 2 := sq_nonneg _
  have hmain_ge : 50 * (k : ℤ) ^ 2 ≤ 25 * (k : ℤ) * (29 * k - 54 * x) := by
    have h29 : 2 * (k : ℤ) ≤ 29 * k - 54 * x := by omega
    have hmul := mul_le_mul_of_nonneg_left h29 (mul_nonneg (by norm_num : (0 : ℤ) ≤ 25) (Int.natCast_nonneg k))
    have hL : 25 * (k : ℤ) * (2 * k) = 50 * (k : ℤ) ^ 2 := by ring
    linarith only [hmul, hL]
  have herr_le : 729 * ((s : ℤ) + t) ≤ 1458 * (k : ℤ) := by omega
  have hbig : 1458 * (k : ℤ) < 50 * (k : ℤ) ^ 2 := by
    have hdiff : 50 * (k : ℤ) ^ 2 - 1458 * (k : ℤ) = (k : ℤ) * (50 * k - 1458) := by ring
    have hpos : (0 : ℤ) < (k : ℤ) * (50 * k - 1458) := mul_pos (by omega) (by omega)
    linarith only [hdiff, hpos]
  linarith only [hlt_k, hid2, hsq_ge, hmain_ge, herr_le, hbig]


/-- Cauchy-Schwarz in ℤ for Fin m. -/
lemma sq_sum_le_card_mul_sum_sq_int {m : ℕ} (a : Fin m → ℤ) :
    (∑ i : Fin m, a i) ^ 2 ≤ (m : ℤ) * ∑ i : Fin m, (a i) ^ 2 := by
  have hnonneg : (0 : ℤ) ≤ ∑ i : Fin m, ∑ j : Fin m, (a i - a j) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hexp : ∑ i : Fin m, ∑ j : Fin m, (a i - a j) ^ 2 =
      2 * (m : ℤ) * (∑ i : Fin m, (a i) ^ 2) - 2 * (∑ i : Fin m, a i) ^ 2 := by
    have hsub : ∀ i : Fin m, ∑ j : Fin m, (a i - a j) ^ 2 =
        (m : ℤ) * (a i) ^ 2 - 2 * a i * (∑ j : Fin m, a j) + ∑ j : Fin m, (a j) ^ 2 := by
      intro i
      have hstep : ∀ j : Fin m, (a i - a j) ^ 2 = (a i) ^ 2 - 2 * a i * a j + (a j) ^ 2 := fun _ => by ring
      simp_rw [hstep]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [hsub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmul2 : ∑ i : Fin m, 2 * a i = 2 * ∑ i : Fin m, a i := (Finset.mul_sum _ _ _).symm
    rw [hmul2]; ring
  linarith

/-- Helper: if n > 0 divides (a - b) and |a - b| < n, then a = b. -/
lemma int_eq_of_dvd_sub {n a b : ℤ} (hn : 0 < n) (hdvd : n ∣ (a - b))
    (h1 : a - b < n) (h2 : b - a < n) : a = b := by
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q = 0 := by nlinarith only [hn, hq, h1, h2]
  rw [hq0, mul_zero] at hq; omega

/-- Helper: if n > 0 and x % n = y % n and |x - y| < n, then x = y. -/
lemma int_eq_of_emod_eq {n x y : ℤ} (hn : 0 < n) (hmod : x % n = y % n)
    (h1 : x - y < n) (h2 : y - x < n) : x = y :=
  int_eq_of_dvd_sub hn (Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod, sub_self, Int.zero_emod])) h1 h2

/-- Sorting bijection: for any key function key : V -> ℕ on a finite type V,
    there is an equivalence e : Fin (card V) ≃ V with key (e i) non-decreasing. -/
lemma exists_sorted_equiv {V : Type} [Fintype V] (key : V → ℕ) :
    ∃ e : Fin (Fintype.card V) ≃ V, ∀ i j : Fin (Fintype.card V), i ≤ j → key (e i) ≤ key (e j) := by
  classical
  let L := (Finset.univ : Finset V).toList.mergeSort (fun a b => decide (key a ≤ key b))
  have hperm : L.Perm (Finset.univ : Finset V).toList := List.mergeSort_perm _ _
  have hlen : L.length = Fintype.card V := by
    rw [hperm.length_eq, Finset.length_toList, Finset.card_univ]
  have hnodup : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
  have hpair : L.Pairwise (fun a b => key a ≤ key b) := by
    have h := List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
      (by intro a b; rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]; omega)
      (Finset.univ : Finset V).toList
    exact h.imp (fun {a b} hab => by simpa only [decide_eq_true_eq] using hab)
  let fn : Fin (Fintype.card V) → V := fun i => L[i.val]'(by omega)
  have hbij : Function.Bijective fn := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hget : L[i.val]'(by omega) = L[j.val]'(by omega) := hij
      have hidx := (List.Nodup.getElem_inj_iff hnodup).mp hget
      exact Fin.ext hidx
    · intro x
      have hxmem : x ∈ L := hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ x))
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hxmem
      exact ⟨⟨idx, by omega⟩, rfl⟩
  refine ⟨Equiv.ofBijective fn hbij, ?_⟩
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · exact (List.pairwise_iff_getElem.mp hpair) i.val j.val (by omega) (by omega) hlt

/-- Standalone corner-orbit telescoping & square-completion contradiction for Theorem H1. -/
lemma andrasfai_corner_orbit_contra
    {n k eF : ℕ} (hn2 : 2 ≤ n) (hk1 : 1 ≤ k) (h2k : 2 * k ≤ n)
    (h5e : 5 * eF < n ^ 2)
    (f : ℤ → ℤ)
    (hf_per : ∀ x : ℤ, f (x + n) = f x + n)
    (hf_gt : ∀ x : ℤ, x < f x)
    (hf_le : ∀ x : ℤ, f x ≤ x + k - 1)
    (hE_bound : 2 * (∑ i : Fin n, ((i.val : ℤ) + k - f i.val)) + (n : ℤ) ≤ 2 * (eF : ℤ))
    (hArc_gt : ∀ t : ℤ, ∀ h_t : ℤ, t < h_t →
      (∀ x : ℤ, t ≤ x → x < h_t → f x < t + k) → t + k ≤ f h_t →
      (n : ℤ) ^ 2 < 50 * ∑ j ∈ Finset.range (h_t - t).toNat, (t + k - f (t + (j : ℤ)))) :
    False := by
  have hn_pos_z : (0 : ℤ) < (n : ℤ) := by omega
  let g : ℤ → ℤ := fun x => x + k - f x
  have hg_per : ∀ x : ℤ, g (x + n) = g x := by intro x; dsimp only [g]; rw [hf_per]; ring
  have hex_h : ∀ t : ℤ, ∃ j : ℕ, t + k ≤ f (t + (j : ℤ)) := fun t => ⟨k, by have := hf_gt (t + k); omega⟩
  let h : ℤ → ℤ := fun t => t + (Nat.find (hex_h t) : ℤ)
  have hh_spec : ∀ t : ℤ, t + k ≤ f (h t) := fun t => Nat.find_spec (hex_h t)
  have hh_min : ∀ t x : ℤ, t ≤ x → x < h t → f x < t + k := by
    intro t x htx hxh
    have hlt_find : (x - t).toNat < Nat.find (hex_h t) := by dsimp only [h] at hxh; omega
    have hnot := Nat.find_min (hex_h t) hlt_find
    rw [show t + ((x - t).toNat : ℤ) = x by omega] at hnot; omega
  have hh_gt : ∀ t : ℤ, t < h t := by
    intro t
    have h0 : ¬ (t + k ≤ f (t + (0 : ℕ))) := by simp only [Nat.cast_zero, add_zero]; have := hf_le t; omega
    have hpos : 0 < Nat.find (hex_h t) := Nat.pos_of_ne_zero (fun hz => h0 (hz ▸ Nat.find_spec (hex_h t)))
    dsimp only [h]; omega
  let iter : ℕ → ℤ := fun j => Nat.iterate h j 0
  have hiter_succ : ∀ j : ℕ, iter (j + 1) = h (iter j) := fun j => Function.iterate_succ_apply' h j 0
  have hiter_mono : ∀ a b : ℕ, a < b → iter a < iter b := by
    intro a b hab
    induction b with
    | zero => omega
    | succ b ih =>
      rw [hiter_succ]
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hab) with rfl | hlt
      · exact hh_gt _
      · exact (ih hlt).trans (hh_gt _)
  let modFn : Fin (n + 1) → Fin n := fun j =>
    ⟨(iter j.val % (n : ℤ)).toNat, by
      have := Int.emod_nonneg (iter j.val) (by omega : (n : ℤ) ≠ 0)
      have := Int.emod_lt_of_pos (iter j.val) hn_pos_z; omega⟩
  have hnot_inj : ¬ Function.Injective modFn := by
    intro hinj; have hcard := Fintype.card_le_of_injective modFn hinj; simp at hcard
  rw [Function.Injective] at hnot_inj; push Not at hnot_inj
  obtain ⟨j₁, j₂, hmod_eq, hjne⟩ := hnot_inj
  have hex_ab : ∃ a b : ℕ, a < b ∧ iter a % (n : ℤ) = iter b % (n : ℤ) := by
    have heq_m : iter j₁.val % (n : ℤ) = iter j₂.val % (n : ℤ) := by
      have h1 := congrArg Fin.val hmod_eq
      have h2 := Int.emod_nonneg (iter j₁.val) (by omega : (n : ℤ) ≠ 0)
      have h3 := Int.emod_nonneg (iter j₂.val) (by omega : (n : ℤ) ≠ 0)
      dsimp only [modFn] at h1; omega
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjne) with hlt | hgt
    · exact ⟨j₁.val, j₂.val, hlt, heq_m⟩
    · exact ⟨j₂.val, j₁.val, hgt, heq_m.symm⟩
  obtain ⟨a, b, hab, hmod_ab⟩ := hex_ab
  set m := b - a
  have hm1 : 1 ≤ m := by omega
  let s : ℕ → ℤ := fun r => iter (a + r)
  have hs_succ : ∀ r : ℕ, s (r + 1) = h (s r) := fun r => by
    dsimp only [s]; rw [show a + (r + 1) = (a + r) + 1 by omega, hiter_succ]
  have hs_diff_pos : ∀ r : ℕ, 1 ≤ s (r + 1) - s r := fun r => by rw [hs_succ]; have := hh_gt (s r); omega
  have hdvd_sm : (n : ℤ) ∣ (s m - s 0) := by
    have hsm : s m = iter b := by dsimp only [s]; congr 1; omega
    have hs0 : s 0 = iter a := by simp [s]
    rw [hsm, hs0]
    exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod_ab, sub_self, Int.zero_emod])
  obtain ⟨p, hp_eq⟩ := hdvd_sm
  have hp_pos : (1 : ℤ) ≤ p := by
    have hsm_gt : s 0 < s m := by
      have h1 : s m = iter b := by dsimp only [s]; congr 1; omega
      have h2 : s 0 = iter a := by simp [s]
      rw [h1, h2]; exact hiter_mono a b hab
    nlinarith only [hp_eq, hsm_gt, hn_pos_z]
  let Δ : Fin m → ℤ := fun r => s (r.val + 1) - s r.val
  have hΔ_sum : ∑ r : Fin m, Δ r = p * (n : ℤ) := by
    have htele : ∀ l : ℕ, ∑ r ∈ Finset.range l, (s (r + 1) - s r) = s l - s 0 := by
      intro l; induction l with | zero => simp | succ l ih => rw [Finset.sum_range_succ, ih]; ring
    rw [Fin.sum_univ_eq_sum_range (fun r => s (r + 1) - s r), htele m, hp_eq]; ring
  let eA : Fin m → ℤ := fun r =>
    ∑ j ∈ Finset.range (Δ r).toNat, (s r.val + k - f (s r.val + (j : ℤ)))
  have heA_gt : ∀ r : Fin m, (n : ℤ) ^ 2 < 50 * eA r := by
    intro r
    have hΔ_eq : h (s r.val) - s r.val = Δ r := by dsimp only [Δ]; rw [hs_succ]
    have h1 := hArc_gt (s r.val) (h (s r.val)) (hh_gt _) (hh_min _) (hh_spec _)
    rwa [hΔ_eq] at h1
  have htele_eA : 2 * (∑ r : Fin m, eA r) =
      p * (2 * (∑ i : Fin n, g i.val) + (n : ℤ)) - ∑ r : Fin m, (Δ r) ^ 2 := by
    have hper_r : ∀ r : Fin m, 2 * eA r =
        2 * (∑ j ∈ Finset.range (Δ r).toNat, g (s r.val + (j : ℤ))) - (Δ r) * (Δ r - 1) := by
      intro r
      dsimp only [eA]
      have hsplit : ∀ j ∈ Finset.range (Δ r).toNat,
          s r.val + k - f (s r.val + (j : ℤ)) = g (s r.val + (j : ℤ)) - (j : ℤ) := fun _ _ => by dsimp only [g]; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, mul_sub]
      congr 1
      have hsum_j : 2 * ∑ j ∈ Finset.range (Δ r).toNat, (j : ℤ) =
          ((Δ r).toNat : ℤ) * (((Δ r).toNat : ℤ) - 1) := by
        have hnat : 2 * ∑ j ∈ Finset.range (Δ r).toNat, j = (Δ r).toNat * ((Δ r).toNat - 1) := by
          have := Finset.sum_range_id (Δ r).toNat
          have hmul := congrArg (2 * ·) this
          have hdiv : 2 * ((Δ r).toNat * ((Δ r).toNat - 1) / 2) = (Δ r).toNat * ((Δ r).toNat - 1) :=
            Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
          linarith only [hmul, hdiv]
        have hcast : ((2 * ∑ j ∈ Finset.range (Δ r).toNat, j : ℕ) : ℤ) =
            (((Δ r).toNat * ((Δ r).toNat - 1) : ℕ) : ℤ) := congrArg (Nat.cast : ℕ → ℤ) hnat
        push_cast at hcast
        have hposΔ := hs_diff_pos r.val
        have hsub1 : (((Δ r).toNat - 1 : ℕ) : ℤ) = ((Δ r).toNat : ℤ) - 1 := by dsimp only [Δ]; omega
        rw [hsub1] at hcast; exact hcast
      have hposΔ := hs_diff_pos r.val
      have htoNat : ((Δ r).toNat : ℤ) = Δ r := by dsimp only [Δ]; omega
      rw [hsum_j, htoNat]
    have hsum_r : 2 * ∑ r : Fin m, eA r =
        2 * (∑ r : Fin m, ∑ j ∈ Finset.range (Δ r).toNat, g (s r.val + (j : ℤ))) -
        ∑ r : Fin m, (Δ r) * (Δ r - 1) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun r _ => hper_r r), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hcont : ∑ r : Fin m, ∑ j ∈ Finset.range (Δ r).toNat, g (s r.val + (j : ℤ)) =
        ∑ x ∈ Finset.range (p.toNat * n), g (s 0 + (x : ℤ)) := by
      have hgen : ∀ l : ℕ, l ≤ m →
          ∑ r ∈ Finset.range l, ∑ j ∈ Finset.range (s (r + 1) - s r).toNat, g (s r + (j : ℤ)) =
          ∑ x ∈ Finset.range (s l - s 0).toNat, g (s 0 + (x : ℤ)) := by
        intro l _; induction l with
        | zero => simp
        | succ l ih =>
          rw [Finset.sum_range_succ, ih (by omega)]
          have hpos_l : 0 ≤ s l - s 0 := by
            clear ih; induction l with | zero => simp | succ l' ih' => have := hs_diff_pos l'; omega
          have hpos_step := hs_diff_pos l
          have hadd_len : (s (l + 1) - s 0).toNat = (s l - s 0).toNat + (s (l + 1) - s l).toNat := by omega
          rw [hadd_len, Finset.sum_range_add]; congr 1
          apply Finset.sum_congr rfl; intro j _; congr 1; omega
      have h1 := hgen m (le_refl m)
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∑ j ∈ Finset.range (s (r + 1) - s r).toNat, g (s r + (j : ℤ)))] at h1
      have hlen_pm : (s m - s 0).toNat = p.toNat * n := by
        rw [hp_eq]
        have heq : (n : ℤ) * p = ((p.toNat * n : ℕ) : ℤ) := by
          push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring
        rw [heq, Int.toNat_natCast]
      rw [hlen_pm] at h1; exact h1
    have hper_block : ∀ q : ℕ, ∑ x ∈ Finset.range (q * n), g (s 0 + (x : ℤ)) =
        (q : ℤ) * ∑ i : Fin n, g i.val := by
      intro q
      have h1block : ∀ y : ℤ, ∑ x ∈ Finset.range n, g (y + (x : ℤ)) = ∑ i : Fin n, g i.val := by
        intro y
        have hstep : ∀ x : ℕ, g (y + (x : ℤ)) = g ((y + (x : ℤ)) % (n : ℤ)) := by
          intro x
          have hdiv := Int.mul_ediv_add_emod (y + (x : ℤ)) (n : ℤ)
          have hg_mul : ∀ t c : ℤ, g (t + c * (n : ℤ)) = g t := by
            intro t c
            induction c using Int.induction_on with
            | zero => simp
            | succ c ih => rw [show t + (↑c + 1) * (n : ℤ) = (t + ↑c * (n : ℤ)) + n by ring, hg_per, ih]
            | pred c ih =>
              have hback : g (t + (-(↑c : ℤ) - 1) * (n : ℤ)) = g ((t + (-(↑c : ℤ) - 1) * (n : ℤ)) + n) := (hg_per _).symm
              rw [hback, show t + (-(↑c : ℤ) - 1) * (n : ℤ) + n = t + (-(↑c : ℤ)) * (n : ℤ) by ring]; exact ih
          have heq : y + (x : ℤ) = (y + (x : ℤ)) % (n : ℤ) + ((y + (x : ℤ)) / (n : ℤ)) * (n : ℤ) := by linarith
          conv_lhs => rw [heq]; exact hg_mul _ _
        rw [← Fin.sum_univ_eq_sum_range (fun x => g (y + (x : ℤ)))]
        let sh : Fin n ≃ Fin n :=
          { toFun := fun x => ⟨((y + (x.val : ℤ)) % (n : ℤ)).toNat, by
              have := Int.emod_nonneg (y + x.val) (by omega : (n : ℤ) ≠ 0)
              have := Int.emod_lt_of_pos (y + x.val) hn_pos_z; omega⟩
            invFun := fun z => ⟨(((z.val : ℤ) - y) % (n : ℤ)).toNat, by
              have := Int.emod_nonneg ((z.val : ℤ) - y) (by omega : (n : ℤ) ≠ 0)
              have := Int.emod_lt_of_pos ((z.val : ℤ) - y) hn_pos_z; omega⟩
            left_inv := fun x => Fin.ext (by
              dsimp only
              have hx := x.isLt
              have h1 := Int.emod_nonneg (y + x.val) (by omega : (n : ℤ) ≠ 0)
              have h3 : ((((y + (x.val : ℤ)) % (n : ℤ)).toNat : ℤ) - y) % (n : ℤ) = (x.val : ℤ) := by
                rw [show (((y + (x.val : ℤ)) % (n : ℤ)).toNat : ℤ) = (y + (x.val : ℤ)) % (n : ℤ) by omega,
                  Int.sub_emod, Int.emod_emod, ← Int.sub_emod, add_sub_cancel_left,
                  Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
              rw [h3, Int.toNat_natCast])
            right_inv := fun z => Fin.ext (by
              dsimp only
              have hz := z.isLt
              have h1 := Int.emod_nonneg ((z.val : ℤ) - y) (by omega : (n : ℤ) ≠ 0)
              have h3 : (y + ((((z.val : ℤ) - y) % (n : ℤ)).toNat : ℤ)) % (n : ℤ) = (z.val : ℤ) := by
                rw [show ((((z.val : ℤ) - y) % (n : ℤ)).toNat : ℤ) = ((z.val : ℤ) - y) % (n : ℤ) by omega,
                  Int.add_emod, Int.emod_emod, ← Int.add_emod, add_sub_cancel,
                  Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
              rw [h3, Int.toNat_natCast]) }
        refine Fintype.sum_equiv sh _ _ (fun x => ?_)
        rw [hstep x.val]; congr 1
        show (y + (x.val : ℤ)) % (n : ℤ) = (((y + (x.val : ℤ)) % (n : ℤ)).toNat : ℤ)
        have := Int.emod_nonneg (y + x.val) (by omega : (n : ℤ) ≠ 0); omega
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih]
        have htail : ∑ x ∈ Finset.range n, g (s 0 + ((q * n + x : ℕ) : ℤ)) = ∑ i : Fin n, g i.val := by
          have : ∀ x : ℕ, s 0 + ((q * n + x : ℕ) : ℤ) = (s 0 + (q * n : ℕ)) + (x : ℤ) := fun _ => by push_cast; ring
          simp_rw [this]; exact h1block _
        rw [htail]; push_cast; ring
    rw [hsum_r, hcont, hper_block p.toNat]
    have hp_toNat : (p.toNat : ℤ) = p := by omega
    rw [hp_toNat]
    have hΔ_expand : ∑ r : Fin m, (Δ r) * (Δ r - 1) = (∑ r : Fin m, (Δ r) ^ 2) - p * (n : ℤ) := by
      have h1 : ∀ r : Fin m, (Δ r) * (Δ r - 1) = (Δ r) ^ 2 - Δ r := fun _ => by ring
      simp_rw [h1]; rw [Finset.sum_sub_distrib, hΔ_sum]
    rw [hΔ_expand]; ring
  set S_eA : ℤ := ∑ r : Fin m, eA r
  set eFz : ℤ := (eF : ℤ)
  have h1 : 2 * S_eA ≤ 2 * p * eFz - ∑ r : Fin m, (Δ r) ^ 2 := by
    have hmul : p * (2 * (∑ i : Fin n, g i.val) + (n : ℤ)) ≤ p * (2 * eFz) :=
      mul_le_mul_of_nonneg_left hE_bound (by omega)
    dsimp only [S_eA]; linarith only [htele_eA, hmul]
  have hcs : (p * (n : ℤ)) ^ 2 ≤ (m : ℤ) * ∑ r : Fin m, (Δ r) ^ 2 := by
    rw [← hΔ_sum]; exact sq_sum_le_card_mul_sum_sq_int Δ
  have h2 : 2 * (m : ℤ) * S_eA ≤ 2 * (m : ℤ) * p * eFz - (p * (n : ℤ)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg m)
    linarith only [hmul, hcs]
  have h3 : 2 * (m : ℤ) * (n : ℤ) ^ 2 * S_eA ≤ (m : ℤ) ^ 2 * eFz ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h2 (sq_nonneg (n : ℤ))
    have hsq : (m : ℤ) ^ 2 * eFz ^ 2 - (n : ℤ) ^ 2 * (2 * (m : ℤ) * p * eFz - (p * (n : ℤ)) ^ 2) =
        (p * (n : ℤ) ^ 2 - (m : ℤ) * eFz) ^ 2 := by ring
    have hsq0 : (0 : ℤ) ≤ (p * (n : ℤ) ^ 2 - (m : ℤ) * eFz) ^ 2 := sq_nonneg _
    linarith only [hmul, hsq, hsq0]
  have h4 : 50 * (n : ℤ) ^ 2 * S_eA < (m : ℤ) * (n : ℤ) ^ 4 := by
    have h5e_z : 5 * eFz < (n : ℤ) ^ 2 := by dsimp only [eFz]; exact_mod_cast h5e
    have heF_nn : (0 : ℤ) ≤ eFz := Int.natCast_nonneg _
    have h5e_sq : (5 * eFz) ^ 2 < ((n : ℤ) ^ 2) ^ 2 := by nlinarith only [h5e_z, heF_nn]
    have hm_pos : (0 : ℤ) < (m : ℤ) := by omega
    have hmul50 : (m : ℤ) * (50 * (n : ℤ) ^ 2 * S_eA) < (m : ℤ) * ((m : ℤ) * (n : ℤ) ^ 4) := by
      have hL : (m : ℤ) * (50 * (n : ℤ) ^ 2 * S_eA) = 25 * (2 * (m : ℤ) * (n : ℤ) ^ 2 * S_eA) := by ring
      have hR : 25 * ((m : ℤ) ^ 2 * eFz ^ 2) = (m : ℤ) ^ 2 * (5 * eFz) ^ 2 := by ring
      have hm2 : (0 : ℤ) < (m : ℤ) ^ 2 := sq_pos_of_pos hm_pos
      have hlt := mul_lt_mul_of_pos_left h5e_sq hm2
      have hR2 : (m : ℤ) ^ 2 * ((n : ℤ) ^ 2) ^ 2 = (m : ℤ) * ((m : ℤ) * (n : ℤ) ^ 4) := by ring
      linarith only [h3, hL, hR, hlt, hR2]
    exact lt_of_mul_lt_mul_left hmul50 hm_pos.le
  have hsum_gt : (m : ℤ) * (n : ℤ) ^ 2 < 50 * S_eA := by
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := by rw [Finset.univ_nonempty_iff]; exact ⟨⟨0, by omega⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun r _ => heA_gt r)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hlt
    exact hlt
  have hcontra : (m : ℤ) * (n : ℤ) ^ 4 < 50 * (n : ℤ) ^ 2 * S_eA := by
    have hn2_pos : (0 : ℤ) < (n : ℤ) ^ 2 := sq_pos_of_pos hn_pos_z
    have hmul := mul_lt_mul_of_pos_left hsum_gt hn2_pos
    have hL : (n : ℤ) ^ 2 * ((m : ℤ) * (n : ℤ) ^ 2) = (m : ℤ) * (n : ℤ) ^ 4 := by ring
    have hR : (n : ℤ) ^ 2 * (50 * S_eA) = 50 * (n : ℤ) ^ 2 * S_eA := by ring
    linarith only [hmul, hL, hR]
  linarith only [h4, hcontra]

/-- Universal Andrásfai Blowup Theorem (Theorem H1 — Bedenknecht-Mota-Reiher-Schacht 2019, all finite n):
    For ALL d >= 1, no And(d)-homomorphic graph satisfies the Erdős #128 dense-half hypothesis!
    (Takes the Keevash-Sudakov Theorem A corollary `5 * e < n^2` as a parameter for modularity.) -/
theorem not_hom_andrasfai {V : Type} [Fintype V] (G : SimpleGraph V)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (h5e_rule : ∀ H : SimpleGraph V, H.CliqueFree 3 →
      (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (H.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
      5 * H.edgeSet.ncard < Fintype.card V ^ 2)
    (d : ℕ) (hd : 1 ≤ d) (φ : V → Fin (3 * d - 1))
    (hφ : ∀ u v : V, G.Adj u v →
      d ≤ ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) ∧
      ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) < 2 * d) :
    False := by
  classical
  let N := 3 * d - 1
  set n := Fintype.card V
  set k := n / 2
  have hN2 : 2 ≤ N := by omega
  -- If n <= 1, V' = ∅ contradicts hH
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h0 := hH (∅ : Set V) (by simp; omega)
    have hemp : (G.induce (∅ : Set V)).edgeSet.ncard = 0 := by
      have h1 := two_mul_induce_edgeSet_ncard G (∅ : Finset V)
      rw [Finset.coe_empty, Finset.sum_empty] at h1; omega
    omega
  have hk1 : 1 ≤ k := by omega
  -- Step 1: Pass to the complete And(d)-blowup Gfull >= G
  let adjFull : V → V → Prop := fun u v =>
    d ≤ ((φ v).val + N - (φ u).val) % N ∧ ((φ v).val + N - (φ u).val) % N < 2 * d
  have hadj_symm : ∀ u v : V, adjFull u v → adjFull v u := by
    intro u v ⟨hlo, hhi⟩
    have hu : (φ u).val < N := (φ u).isLt
    have hv : (φ v).val < N := (φ v).isLt
    dsimp only [adjFull]
    by_cases hle : (φ u).val ≤ (φ v).val
    · have h1 : ((φ v).val + N - (φ u).val) % N = (φ v).val - (φ u).val := by
        rw [show (φ v).val + N - (φ u).val = ((φ v).val - (φ u).val) + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h2 : ((φ u).val + N - (φ v).val) % N = N - ((φ v).val - (φ u).val) := by
        rw [show (φ u).val + N - (φ v).val = N - ((φ v).val - (φ u).val) by omega,
          Nat.mod_eq_of_lt (by omega)]
      omega
    · have h1 : ((φ v).val + N - (φ u).val) % N = (φ v).val + N - (φ u).val :=
        Nat.mod_eq_of_lt (by omega)
      have h2 : ((φ u).val + N - (φ v).val) % N = (φ u).val - (φ v).val := by
        rw [show (φ u).val + N - (φ v).val = ((φ u).val - (φ v).val) + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  have hadj_irrefl : ∀ u : V, ¬ adjFull u u := by
    intro u ⟨hlo, _⟩
    have hu : (φ u).val < N := (φ u).isLt
    have h0 : ((φ u).val + N - (φ u).val) % N = 0 := by
      rw [show (φ u).val + N - (φ u).val = N by omega, Nat.mod_self]
    omega
  let Gfull : SimpleGraph V :=
    { Adj := adjFull
      symm := ⟨fun _ _ h => hadj_symm _ _ h⟩
      loopless := ⟨hadj_irrefl⟩ }
  have hGGfull : ∀ u v : V, G.Adj u v → Gfull.Adj u v := by
    intro u v h; exact hφ u v h
  have hGfull_TF : Gfull.CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
    have h1 : Gfull.Adj a b := hs.1 (by simp) (by simp) hab
    have h2 : Gfull.Adj b c := hs.1 (by simp) (by simp) hbc
    have h3 : Gfull.Adj c a := hs.1 (by simp) (by simp) hac.symm
    have ha := (φ a).isLt; have hb := (φ b).isLt; have hc := (φ c).isLt
    set x := ((φ b).val + N - (φ a).val) % N
    set y := ((φ c).val + N - (φ b).val) % N
    set z := ((φ a).val + N - (φ c).val) % N
    have hmod : (x + y + z) % N = 0 := by
      have hsum : ((φ b).val + N - (φ a).val) + ((φ c).val + N - (φ b).val) +
          ((φ a).val + N - (φ c).val) = 3 * N := by omega
      have h1' : (x + y + z) % N =
          (((φ b).val + N - (φ a).val) + ((φ c).val + N - (φ b).val) +
            ((φ a).val + N - (φ c).val)) % N := by
        dsimp only [x, y, z]; simp [Nat.add_mod]
      rw [h1', hsum]; exact Nat.mul_mod_left 3 N
    have hlo : 3 * d ≤ x + y + z := by omega
    have hhi : x + y + z + 3 ≤ 6 * d := by omega
    have hdiv : N ∣ (x + y + z) := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨q, hq⟩ := hdiv
    have hN_eq : N + 1 = 3 * d := by omega
    have hq1 : 1 < q := by nlinarith only [hq, hlo, hN_eq]
    have hq2 : q < 2 := by nlinarith only [hq, hhi, hN_eq, hd]
    omega
  have hGfull_H : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ n →
      50 * (Gfull.induce V').edgeSet.ncard > n ^ 2 := by
    intro V' hV'
    have hG_gt := hH V' hV'
    have hmono : (G.induce V').edgeSet.ncard ≤ (Gfull.induce V').edgeSet.ncard := by
      have h1 := two_mul_induce_edgeSet_ncard G V'.toFinset
      have h2 := two_mul_induce_edgeSet_ncard Gfull V'.toFinset
      rw [Set.coe_toFinset] at h1 h2
      have hle : ∑ u ∈ V'.toFinset, #(V'.toFinset.filter (G.Adj u)) ≤
          ∑ u ∈ V'.toFinset, #(V'.toFinset.filter (Gfull.Adj u)) :=
        Finset.sum_le_sum (fun u _ => Finset.card_le_card (fun v hv => by
          have hv' := Finset.mem_filter.mp hv
          exact Finset.mem_filter.mpr ⟨hv'.1, hGGfull u v hv'.2⟩))
      omega
    omega
  have h5e : 5 * Gfull.edgeSet.ncard < n ^ 2 := h5e_rule Gfull hGfull_TF hGfull_H
  -- Step 2: Cyclic ordering e : Fin n ≃ V sorted by φ, lifted to ℤ
  obtain ⟨e, he_mono⟩ := exists_sorted_equiv (fun u : V => (φ u).val)
  have hn_pos_z : (0 : ℤ) < (n : ℤ) := by omega
  have hN_pos_z : (0 : ℤ) < (N : ℤ) := by omega
  let v : ℤ → V := fun x => e ⟨(x % (n : ℤ)).toNat, by
    have h1 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos x hn_pos_z
    omega⟩
  have hv_per : ∀ x : ℤ, v (x + n) = v x := by
    intro x; dsimp only [v]; congr 1; apply Fin.ext; simp [Int.add_emod_right]
  have hv_inj_mod : ∀ x y : ℤ, v x = v y ↔ x % (n : ℤ) = y % (n : ℤ) := by
    intro x y
    dsimp only [v]
    constructor
    · intro h
      have h1 := congrArg Fin.val (e.injective h)
      dsimp only at h1
      have hx0 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
      have hy0 := Int.emod_nonneg y (by omega : (n : ℤ) ≠ 0)
      omega
    · intro h; congr 1; apply Fin.ext; simp [h]
  let w : ℕ → ℕ := fun r => #(Finset.univ.filter (fun u : V => (φ u).val = r))
  let P : ℕ → ℕ := fun r => ∑ i ∈ Finset.range r, w i
  have hP0 : P 0 = 0 := by simp [P]
  have hPN : P N = n := by
    dsimp only [P, w, n]
    have hbij : ∑ i ∈ Finset.range N, #(Finset.univ.filter (fun u : V => (φ u).val = i)) =
        ∑ r : Fin N, #(Finset.univ.filter (fun u : V => φ u = r)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl; intro r _
      congr 1; ext u; simp [Fin.ext_iff]
    rw [hbij, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  have hP_mono : ∀ r₁ r₂ : ℕ, r₁ ≤ r₂ → P r₁ ≤ P r₂ := fun r₁ r₂ h =>
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hP_lt_card : ∀ r : ℕ, r ≤ N → P r = #(Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r)) := by
    intro r _
    induction r with
    | zero => simp [P]
    | succ r ih =>
      rw [show P (r + 1) = P r + w r by dsimp only [P]; rw [Finset.sum_range_succ]]
      rw [ih (by omega)]
      have hsplit : Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r + 1) =
          Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r) ∪
          Finset.univ.filter (fun i : Fin n => (φ (e i)).val = r) := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hdisj : Disjoint (Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r))
          (Finset.univ.filter (fun i : Fin n => (φ (e i)).val = r)) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        have a1 := (Finset.mem_filter.mp h1).2; have a2 := (Finset.mem_filter.mp h2).2; omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
      congr 1
      dsimp only [w]
      refine Finset.card_bij (fun u _ => e.symm u) ?_ ?_ ?_
      · intro u hu; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢; simp [hu]
      · intro u₁ _ u₂ _ h; exact e.symm.injective h
      · intro i hi; exact ⟨e i, by simpa using hi, e.symm_apply_apply i⟩
  have hP_interval : ∀ i : Fin n, P (φ (e i)).val ≤ i.val ∧ i.val < P ((φ (e i)).val + 1) := by
    intro i
    set r := (φ (e i)).val
    have hrN : r < N := (φ (e i)).isLt
    constructor
    · -- Every j < P r? No: every j with key (e j) < r must satisfy j < i!
      have hsub : Finset.univ.filter (fun j : Fin n => (φ (e j)).val < r) ⊆
          Finset.univ.filter (fun j : Fin n => j.val < i.val) := by
        intro j hj
        have hjr : (φ (e j)).val < r := (Finset.mem_filter.mp hj).2
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
        by_contra hge
        have hle : i ≤ j := Fin.le_def.mpr (by omega)
        have := he_mono i j hle; omega
      have h1 := hP_lt_card r (by omega)
      have h2 := Finset.card_le_card hsub
      have h3 : #(Finset.univ.filter (fun j : Fin n => j.val < i.val)) = i.val := by
        refine (Finset.card_bij (fun (j : Fin n) _ => j.val) ?_ ?_ ?_).trans (Finset.card_range i.val)
        · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
        · intro j₁ _ j₂ _ h; exact Fin.ext h
        · intro m hm; exact ⟨⟨m, by have := Finset.mem_range.mp hm; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hm⟩, rfl⟩
      omega
    · -- Every j <= i has key (e j) <= r < r + 1!
      have hsub : Finset.univ.filter (fun j : Fin n => j.val ≤ i.val) ⊆
          Finset.univ.filter (fun j : Fin n => (φ (e j)).val < r + 1) := by
        intro j hj
        have hle : j ≤ i := Fin.le_def.mpr (Finset.mem_filter.mp hj).2
        have := he_mono j i hle
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have h1 := hP_lt_card (r + 1) (by omega)
      have h2 := Finset.card_le_card hsub
      have h3 : #(Finset.univ.filter (fun j : Fin n => j.val ≤ i.val)) = i.val + 1 := by
        refine (Finset.card_bij (fun (j : Fin n) _ => j.val) ?_ ?_ ?_).trans (Finset.card_range (i.val + 1))
        · intro j hj; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
        · intro j₁ _ j₂ _ h; exact Fin.ext h
        · intro m hm; exact ⟨⟨m, by have := Finset.mem_range.mp hm; have := i.isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := Finset.mem_range.mp hm; dsimp only; omega⟩, rfl⟩
      omega
  let PZ : ℤ → ℤ := fun r => (r / (N : ℤ)) * (n : ℤ) + (P ((r % (N : ℤ)).toNat) : ℤ)
  have hPZ_per : ∀ r : ℤ, PZ (r + N) = PZ r + n := by
    intro r; dsimp only [PZ]
    rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self (by omega : (N : ℤ) ≠ 0), Int.add_emod_right]
    ring
  have hPZ_mono : ∀ r₁ r₂ : ℤ, r₁ ≤ r₂ → PZ r₁ ≤ PZ r₂ := by
    intro r₁ r₂ hle
    dsimp only [PZ]
    have hq_le : r₁ / (N : ℤ) ≤ r₂ / (N : ℤ) := Int.ediv_le_ediv hN_pos_z hle
    rcases eq_or_lt_of_le hq_le with hq | hq
    · rw [hq]
      have hm1 := Int.emod_nonneg r₁ (by omega : (N : ℤ) ≠ 0)
      have hm2 := Int.emod_nonneg r₂ (by omega : (N : ℤ) ≠ 0)
      have hdiv1 := Int.mul_ediv_add_emod r₁ (N : ℤ)
      have hdiv2 := Int.mul_ediv_add_emod r₂ (N : ℤ)
      rw [hq] at hdiv1
      have hm_le : (r₁ % (N : ℤ)).toNat ≤ (r₂ % (N : ℤ)).toNat := by omega
      have := hP_mono _ _ hm_le; omega
    · have hm1_lt : (r₁ % (N : ℤ)).toNat < N := by
        have := Int.emod_lt_of_pos r₁ hN_pos_z
        have := Int.emod_nonneg r₁ (by omega : (N : ℤ) ≠ 0); omega
      have hP1 : P ((r₁ % (N : ℤ)).toNat) ≤ n := by rw [← hPN]; exact hP_mono _ _ (by omega)
      have hstep : (r₁ / (N : ℤ) + 1) * (n : ℤ) ≤ (r₂ / (N : ℤ)) * (n : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by omega)
      have hP2 : (0 : ℤ) ≤ (P ((r₂ % (N : ℤ)).toNat) : ℤ) := Int.natCast_nonneg _
      linarith
  let partOf : ℤ → ℤ := fun x => (x / (n : ℤ)) * (N : ℤ) + ((φ (v x)).val : ℤ)
  have hpart_per : ∀ x : ℤ, partOf (x + n) = partOf x + N := by
    intro x; dsimp only [partOf]
    rw [hv_per, Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self (by omega : (n : ℤ) ≠ 0)]
    ring
  have hpart_mono : ∀ x y : ℤ, x ≤ y → partOf x ≤ partOf y := by
    intro x y hle
    dsimp only [partOf]
    have hq_le : x / (n : ℤ) ≤ y / (n : ℤ) := Int.ediv_le_ediv hn_pos_z hle
    rcases eq_or_lt_of_le hq_le with hq | hq
    · rw [hq]
      have hx0 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
      have hy0 := Int.emod_nonneg y (by omega : (n : ℤ) ≠ 0)
      have hdx := Int.mul_ediv_add_emod x (n : ℤ)
      have hdy := Int.mul_ediv_add_emod y (n : ℤ)
      rw [hq] at hdx
      have hlt_x := Int.emod_lt_of_pos x hn_pos_z
      have hlt_y := Int.emod_lt_of_pos y hn_pos_z
      have hfin : (⟨(x % (n : ℤ)).toNat, by omega⟩ : Fin n) ≤ ⟨(y % (n : ℤ)).toNat, by omega⟩ :=
        Fin.le_def.mpr (by dsimp only; omega)
      have hm := he_mono _ _ hfin
      dsimp only [v]
      omega
    · have hxN : (φ (v x)).val < N := (φ (v x)).isLt
      have hstep : (x / (n : ℤ) + 1) * (N : ℤ) ≤ (y / (n : ℤ)) * (N : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by omega)
      have hy0 : (0 : ℤ) ≤ ((φ (v y)).val : ℤ) := Int.natCast_nonneg _
      linarith
  have hpart_int : ∀ x : ℤ, PZ (partOf x) ≤ x ∧ x < PZ (partOf x + 1) := by
    intro x
    set q := x / (n : ℤ)
    have hdx := Int.mul_ediv_add_emod x (n : ℤ)
    have hx0 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
    have hxlt := Int.emod_lt_of_pos x hn_pos_z
    let i : Fin n := ⟨(x % (n : ℤ)).toNat, by omega⟩
    have hi_val : (i.val : ℤ) = x % (n : ℤ) := by dsimp only [i]; omega
    have hvx : v x = e i := rfl
    have ⟨hlo, hhi⟩ := hP_interval i
    set r := (φ (e i)).val
    have hrN : r < N := (φ (e i)).isLt
    have hPZ_r : PZ (partOf x) = q * (n : ℤ) + (P r : ℤ) := by
      dsimp only [PZ, partOf, q, r]
      rw [hvx]
      have hdiv : ((x / (n : ℤ)) * (N : ℤ) + ((φ (e i)).val : ℤ)) / (N : ℤ) = x / (n : ℤ) := by
        rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _), Int.mul_ediv_cancel _ (by omega : (N : ℤ) ≠ 0),
          Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by omega), add_zero]
      have hmod : ((x / (n : ℤ)) * (N : ℤ) + ((φ (e i)).val : ℤ)) % (N : ℤ) = ((φ (e i)).val : ℤ) := by
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod,
          Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
      rw [hdiv, hmod, Int.toNat_natCast]
    have hPZ_r1 : PZ (partOf x + 1) = q * (n : ℤ) + (P (r + 1) : ℤ) := by
      by_cases htop : r + 1 < N
      · have htop' : ((φ (e i)).val : ℤ) + 1 < (N : ℤ) := by dsimp only [r] at htop; omega
        have hdiv0 : (((φ (e i)).val : ℤ) + 1) / (N : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) htop'
        have hmod0 : (((φ (e i)).val : ℤ) + 1) % (N : ℤ) = ((φ (e i)).val : ℤ) + 1 := Int.emod_eq_of_lt (by omega) htop'
        dsimp only [PZ, partOf, q, r]
        rw [hvx, add_assoc]
        have hdiv : ((x / (n : ℤ)) * (N : ℤ) + (((φ (e i)).val : ℤ) + 1)) / (N : ℤ) = x / (n : ℤ) := by
          rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _), Int.mul_ediv_cancel _ (by omega : (N : ℤ) ≠ 0),
            hdiv0, add_zero]
        have hmod : ((x / (n : ℤ)) * (N : ℤ) + (((φ (e i)).val : ℤ) + 1)) % (N : ℤ) = (((φ (e i)).val : ℤ) + 1) := by
          rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod, hmod0]
        rw [hdiv, hmod, show (((φ (e i)).val : ℤ) + 1).toNat = (φ (e i)).val + 1 by omega]
      · have hr_eq : r + 1 = N := by omega
        have hr_eq_z : ((φ (e i)).val : ℤ) + 1 = (N : ℤ) := by dsimp only [r] at hr_eq; exact_mod_cast hr_eq
        have heq : partOf x + 1 = (q + 1) * (N : ℤ) := by
          dsimp only [partOf, q]; rw [hvx]; linarith
        rw [heq]
        dsimp only [PZ]
        rw [Int.mul_ediv_cancel _ (by omega : (N : ℤ) ≠ 0), Int.mul_emod_left, Int.toNat_zero,
          hP0, hr_eq, hPN]
        push_cast; ring
    rw [hPZ_r, hPZ_r1]
    have hx_eq : x = q * (n : ℤ) + (i.val : ℤ) := by dsimp only [q]; linarith
    omega
  -- Define lifted non-neighbor map f : ℤ -> ℤ
  let f : ℤ → ℤ := fun x => PZ (partOf x + d)
  have hf_mono : ∀ x y : ℤ, x ≤ y → f x ≤ f y := fun x y h => hPZ_mono _ _ (by have := hpart_mono x y h; omega)
  have hf_per : ∀ x : ℤ, f (x + n) = f x + n := by
    intro x; dsimp only [f]; rw [hpart_per, show partOf x + N + d = (partOf x + d) + N by ring, hPZ_per]
  have hf_gt : ∀ x : ℤ, x < f x := by
    intro x
    have h1 := (hpart_int x).2
    have h2 : PZ (partOf x + 1) ≤ PZ (partOf x + d) := hPZ_mono _ _ (by omega)
    exact lt_of_lt_of_le h1 h2
  -- Independent-half check: f x <= x + k - 1 for all x
  have hf_le : ∀ x : ℤ, f x ≤ x + k - 1 := by
    intro x
    by_contra hgt
    push Not at hgt
    let A : Finset V := (Finset.range k).image (fun j : ℕ => v (x + (j : ℤ)))
    have hAcard : #A = k := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      have ha' := Finset.mem_range.mp ha; have hb' := Finset.mem_range.mp hb
      have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
      omega
    have hAindep : ∀ u ∈ A, ∀ w' ∈ A, ¬ Gfull.Adj u w' := by
      intro u hu w' hw' hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw'
      have ha' := Finset.mem_range.mp ha; have hb' := Finset.mem_range.mp hb
      have hbd : ∀ j : ℕ, j < k → partOf x ≤ partOf (x + (j : ℤ)) ∧ partOf (x + (j : ℤ)) < partOf x + d := by
        intro j hj
        refine ⟨hpart_mono x (x + j) (by omega), ?_⟩
        by_contra hge
        push Not at hge
        have h1 : PZ (partOf x + d) ≤ PZ (partOf (x + j)) := hPZ_mono _ _ hge
        have h2 := (hpart_int (x + j)).1
        dsimp only [f] at hgt; omega
      have hpa := hbd a ha'; have hpb := hbd b hb'
      -- Now |partOf (x+b) - partOf (x+a)| < d, contradicting Gfull.Adj!
      have hmod_eq : ∀ y : ℤ, ((partOf y) % (N : ℤ)) = ((φ (v y)).val : ℤ) := by
        intro y; dsimp only [partOf]
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have := (φ (v y)).isLt; omega)]
      have hdiff_mod : ((((φ (v (x + b))).val + N - (φ (v (x + a))).val) % N : ℕ) : ℤ) =
          (partOf (x + b) - partOf (x + a)) % (N : ℤ) := by
        have h1 : (((φ (v (x + b))).val + N - (φ (v (x + a))).val : ℕ) : ℤ) =
            ((φ (v (x + b))).val : ℤ) - ((φ (v (x + a))).val : ℤ) + (N : ℤ) := by
          have := (φ (v (x + a))).isLt; omega
        rw [Int.natCast_emod, h1, Int.add_emod_right, ← hmod_eq (x + b), ← hmod_eq (x + a),
          ← Int.sub_emod]
      have ⟨hlo, hhi⟩ := hadj
      have hlo_z : (d : ℤ) ≤ (partOf (x + b) - partOf (x + a)) % (N : ℤ) := by
        rw [← hdiff_mod]; exact_mod_cast hlo
      have hhi_z : (partOf (x + b) - partOf (x + a)) % (N : ℤ) < (2 * d : ℤ) := by
        rw [← hdiff_mod]; exact_mod_cast hhi
      by_cases hab_le : partOf (x + a) ≤ partOf (x + b)
      · have hmod0 : (partOf (x + b) - partOf (x + a)) % (N : ℤ) = partOf (x + b) - partOf (x + a) :=
          Int.emod_eq_of_lt (by omega) (by omega)
        omega
      · have hmod0 : (partOf (x + b) - partOf (x + a)) % (N : ℤ) = partOf (x + b) - partOf (x + a) + N := by
          have := Int.add_emod_right (partOf (x + b) - partOf (x + a)) (N : ℤ)
          rw [← this, Int.emod_eq_of_lt (by omega) (by omega)]
        omega
    have h50 := hGfull_H (A : Set V) (by rw [Set.ncard_coe_finset, hAcard]; omega)
    have h0 : 2 * (Gfull.induce (A : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      apply Finset.sum_eq_zero; intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w' hw'; exact hAindep u hu w' hw'
    omega
  -- Step 3: Exact equivalence Gfull.Adj (v x) (v y) ↔ f x ≤ y for all x ≤ y ≤ x + k
  have hadj_iff : ∀ x y : ℤ, x ≤ y → y ≤ x + k → (Gfull.Adj (v x) (v y) ↔ f x ≤ y) := by
    intro x y hxy hyx
    have hrx_le : partOf x ≤ partOf y := hpart_mono x y hxy
    have hfy_le : partOf y < partOf x + 2 * d := by
      by_contra hge
      push Not at hge
      have h1 : PZ ((partOf x + 1) + N) ≤ PZ (partOf y + d) := hPZ_mono _ _ (by omega)
      rw [hPZ_per] at h1
      have h2 := (hpart_int x).2
      have h3 := hf_le y
      dsimp only [f] at h3
      omega
    have hf_iff : f x ≤ y ↔ partOf x + d ≤ partOf y := by
      constructor
      · intro hfy
        by_contra hlt
        have h1 : PZ (partOf y + 1) ≤ PZ (partOf x + d) := hPZ_mono _ _ (by omega)
        have h2 := (hpart_int y).2
        dsimp only [f] at hfy; omega
      · intro hge
        have h1 : PZ (partOf x + d) ≤ PZ (partOf y) := hPZ_mono _ _ hge
        have h2 := (hpart_int y).1
        dsimp only [f]; omega
    rw [hf_iff]
    have hmod_eq : ∀ z : ℤ, ((partOf z) % (N : ℤ)) = ((φ (v z)).val : ℤ) := by
      intro z; dsimp only [partOf]
      rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have := (φ (v z)).isLt; omega)]
    have hdiff_mod : ((((φ (v y)).val + N - (φ (v x)).val) % N : ℕ) : ℤ) = partOf y - partOf x := by
      have h1 : (((φ (v y)).val + N - (φ (v x)).val : ℕ) : ℤ) =
          ((φ (v y)).val : ℤ) - ((φ (v x)).val : ℤ) + (N : ℤ) := by
        have := (φ (v x)).isLt; omega
      rw [Int.natCast_emod, h1, Int.add_emod_right, ← hmod_eq y, ← hmod_eq x, ← Int.sub_emod,
        Int.emod_eq_of_lt (by omega) (by omega)]
    dsimp only [Gfull, adjFull]
    constructor
    · rintro ⟨hlo, _⟩
      have hlo_z : (d : ℤ) ≤ partOf y - partOf x := by rw [← hdiff_mod]; exact_mod_cast hlo
      omega
    · intro hge
      constructor
      · have : (d : ℤ) ≤ ((((φ (v y)).val + N - (φ (v x)).val) % N : ℕ) : ℤ) := by omega
        exact_mod_cast this
      · have : ((((φ (v y)).val + N - (φ (v x)).val) % N : ℕ) : ℤ) < (2 * d : ℤ) := by omega
        exact_mod_cast this
  -- Step 4: Exact edge count bound 2 * ∑_{x ∈ Fin n} (x + k - f x) + n <= 2 * e(Gfull)
  let g : ℤ → ℤ := fun x => x + k - f x
  have hg_per : ∀ x : ℤ, g (x + n) = g x := by intro x; dsimp only [g]; rw [hf_per]; ring
  have hg_pos : ∀ x : ℤ, 1 ≤ g x := fun x => by dsimp only [g]; have := hf_le x; omega
  have hE_bound : 2 * (∑ i : Fin n, g (i.val : ℤ)) + (n : ℤ) ≤ 2 * (Gfull.edgeSet.ncard : ℤ) := by
    have h2e : 2 * Gfull.edgeSet.ncard = ∑ i : Fin n, #(Finset.univ.filter (Gfull.Adj (e i))) := by
      have hcard : Gfull.edgeSet.ncard = #Gfull.edgeFinset := by
        rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      rw [← Equiv.sum_comp e (fun u => Gfull.degree u)]
      apply Finset.sum_congr rfl; intro i _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset]; congr 1; ext u; simp
    -- For each i : Fin n, partition neighbors of v(i) into Fwd, Bwd, Ant (all pairwise disjoint!)
    let Fwd : Fin n → Finset V := fun i =>
      ((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))).image
        (fun t => v (i.val + (t + 1 : ℕ)))
    let Bwd : Fin n → Finset V := fun i =>
      ((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val - (t + 1 : ℕ))))).image
        (fun t => v (i.val - (t + 1 : ℕ)))
    have hper_deg : ∀ i : Fin n,
        #(Fwd i) + #(Bwd i) + 1 ≤ #(Finset.univ.filter (Gfull.Adj (e i))) := by
      intro i
      have hvi : v i.val = e i := by
        dsimp only [v]; congr 1; apply Fin.ext; dsimp only
        rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega), Int.toNat_natCast]
      have hFsub : Fwd i ⊆ Finset.univ.filter (Gfull.Adj (e i)) := by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hvi]; exact (Finset.mem_filter.mp ht).2⟩
      have hBsub : Bwd i ⊆ Finset.univ.filter (Gfull.Adj (e i)) := by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hvi]; exact (Finset.mem_filter.mp ht).2⟩
      have hAnt_mem : v (i.val + k) ∈ Finset.univ.filter (Gfull.Adj (e i)) := by
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hvi, hadj_iff i.val (i.val + k) (by omega) (le_refl _)]
        have := hf_le i.val; omega
      have hdisj_FB : Disjoint (Fwd i) (Bwd i) := by
        rw [Finset.disjoint_left]; intro u huF huB
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp huF
        obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp huB
        have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        have hs' := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp heq.symm) (by omega) (by omega)
        omega
      have hAnt_notF : v (i.val + k) ∉ Fwd i := by
        intro hmem
        obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
        have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp heq.symm) (by omega) (by omega)
        omega
      have hAnt_notB : v (i.val + k) ∉ Bwd i := by
        intro hmem
        obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
        have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp heq.symm) (by omega) (by omega)
        omega
      have hcard_union : #(insert (v (i.val + k)) (Fwd i ∪ Bwd i)) = #(Fwd i) + #(Bwd i) + 1 := by
        rw [Finset.card_insert_of_notMem (by simp [hAnt_notF, hAnt_notB]),
          Finset.card_union_of_disjoint hdisj_FB]
      rw [← hcard_union]
      exact Finset.card_le_card (Finset.insert_subset hAnt_mem (Finset.union_subset hFsub hBsub))
    have hFwd_card : ∀ i : Fin n, (#(Fwd i) : ℤ) = g i.val := by
      intro i
      have hinj : Set.InjOn (fun t : ℕ => v (i.val + (t + 1 : ℕ)))
          ((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))) := by
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
        omega
      rw [Finset.card_image_of_injOn hinj]
      have hbij : #((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))) =
          (g i.val).toNat := by
        have hf_gt_i := hf_gt i.val
        have hf_le_i := hf_le i.val
        refine (Finset.card_bij (fun t _ => ((i.val + (t + 1 : ℕ)) - f i.val).toNat) ?_ ?_ ?_).trans
          (Finset.card_range (g i.val).toNat)
        · intro t ht
          have ht' := Finset.mem_filter.mp ht
          have htr := Finset.mem_range.mp ht'.1
          have hge := (hadj_iff i.val (i.val + (t + 1 : ℕ)) (by omega) (by omega)).mp ht'.2
          exact Finset.mem_range.mpr (by dsimp only [g]; omega)
        · intro a ha b hb heq
          have ha' := Finset.mem_filter.mp ha; have hb' := Finset.mem_filter.mp hb
          have har := Finset.mem_range.mp ha'.1; have hbr := Finset.mem_range.mp hb'.1
          have hga := (hadj_iff i.val (i.val + (a + 1 : ℕ)) (by omega) (by omega)).mp ha'.2
          have hgb := (hadj_iff i.val (i.val + (b + 1 : ℕ)) (by omega) (by omega)).mp hb'.2
          omega
        · intro m hm
          have hmr := Finset.mem_range.mp hm
          set t := (f i.val + m - i.val - 1).toNat
          refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp only [g] at hmr; omega), ?_⟩, ?_⟩
          · rw [hadj_iff i.val (i.val + (t + 1 : ℕ)) (by omega) (by dsimp only [g] at hmr; omega)]
            dsimp only [t]; omega
          · dsimp only [t]; omega
      rw [hbij]; have := hg_pos i.val; omega
    have hBwd_sum : ∑ i : Fin n, #(Bwd i) = ∑ i : Fin n, #(Fwd i) := by
      have hcardB : ∀ i : Fin n, #(Bwd i) =
          #((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val - (t + 1 : ℕ))))) := by
        intro i
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
        omega
      have hcardF : ∀ i : Fin n, #(Fwd i) =
          #((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))) := by
        intro i
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
        omega
      simp_rw [hcardB, hcardF, Finset.card_filter]
      rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
      apply Finset.sum_congr rfl; intro t _
      let shift : Fin n ≃ Fin n :=
        { toFun := fun i => ⟨(i.val + n - (t + 1) % n) % n, Nat.mod_lt _ (by omega)⟩
          invFun := fun i => ⟨(i.val + (t + 1)) % n, Nat.mod_lt _ (by omega)⟩
          left_inv := fun i => Fin.ext (by
            dsimp only
            have hi := i.isLt
            have hm := Nat.mod_lt (t + 1) (by omega : 0 < n)
            have h1 : ((i.val + n - (t + 1) % n) % n + (t + 1)) % n =
                ((i.val + n - (t + 1) % n) + (t + 1) % n) % n := by
              rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod (i.val + n - (t + 1) % n), Nat.mod_mod]
            rw [h1, Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hi])
          right_inv := fun i => Fin.ext (by
            dsimp only
            have hi := i.isLt
            have hm := Nat.mod_lt (t + 1) (by omega : 0 < n)
            have hmod : (i.val + (t + 1)) % n = (i.val + (t + 1) % n) % n := by
              rw [Nat.add_mod, Nat.add_mod i.val ((t + 1) % n), Nat.mod_mod]
            rw [hmod]
            by_cases hlt : i.val + (t + 1) % n < n
            · rw [Nat.mod_eq_of_lt hlt, show i.val + (t + 1) % n + n - (t + 1) % n = i.val + n by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt hi]
            · have hsub : (i.val + (t + 1) % n) % n = i.val + (t + 1) % n - n := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
              rw [hsub, show i.val + (t + 1) % n - n + n - (t + 1) % n = i.val by omega,
                Nat.mod_eq_of_lt hi]) }
      refine Fintype.sum_equiv shift _ _ (fun i => ?_)
      have h1 : v ((shift i).val : ℤ) = v (i.val - (t + 1 : ℕ)) := by
        rw [hv_inj_mod]
        have hi := i.isLt
        have hm := Nat.mod_lt (t + 1) (by omega : 0 < n)
        have hlt_s : (shift i).val < n := (shift i).isLt
        rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
        change (((i.val + n - (t + 1) % n) % n : ℕ) : ℤ) = _
        have hcast : (((i.val + n - (t + 1) % n) % n : ℕ) : ℤ) =
            ((i.val : ℤ) + (n : ℤ) - (((t + 1) % n : ℕ) : ℤ)) % (n : ℤ) := by
          rw [Int.natCast_emod]; congr 1; omega
        rw [hcast, show (i.val : ℤ) + (n : ℤ) - (((t + 1) % n : ℕ) : ℤ) =
            (n : ℤ) + ((i.val : ℤ) - (((t + 1) % n : ℕ) : ℤ)) by ring,
          Int.add_emod_left, Int.natCast_emod, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
      have h2 : v ((shift i).val + (t + 1 : ℕ)) = v i.val := by
        rw [hv_inj_mod]
        have h1' := (hv_inj_mod _ _).mp h1
        rw [Int.add_emod, h1', ← Int.add_emod, sub_add_cancel]
      simp only [h1, h2, Gfull.adj_comm]
    have hsum_le : ∑ i : Fin n, (#(Fwd i) + #(Bwd i) + 1) ≤ 2 * Gfull.edgeSet.ncard := by
      rw [h2e]; exact Finset.sum_le_sum (fun i _ => hper_deg i)
    simp_rw [Finset.sum_add_distrib] at hsum_le
    rw [hBwd_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum_le
    have hsum_z : (∑ i : Fin n, (#(Fwd i) : ℤ)) = ∑ i : Fin n, g i.val :=
      Finset.sum_congr rfl (fun i _ => hFwd_card i)
    have hcast : ((∑ i : Fin n, #(Fwd i) + ∑ i : Fin n, #(Fwd i) + n : ℕ) : ℤ) ≤
        ((2 * Gfull.edgeSet.ncard : ℕ) : ℤ) := Nat.cast_le.mpr hsum_le
    push_cast at hcast
    rw [hsum_z] at hcast
    linarith
  -- Step 5-6: Verify k-arc edge formula and invoke standalone corner-orbit contradiction!
  apply andrasfai_corner_orbit_contra hn2 hk1 (by omega) h5e f hf_per hf_gt hf_le hE_bound
  intro t h_t hht_gt hht_min hht_spec
  let A := (Finset.range k).image (fun j : ℕ => v (t + (j : ℤ)))
  have hinjA : Set.InjOn (fun j : ℕ => v (t + (j : ℤ))) (Finset.range k) := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha; have hb' := Finset.mem_range.mp hb
    have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
    omega
  have hAcard : #A = k := by rw [Finset.card_image_of_injOn hinjA, Finset.card_range]
  have h50 := hGfull_H (A : Set V) (by rw [Set.ncard_coe_finset, hAcard]; omega)
  have h2A := two_mul_induce_edgeSet_ncard Gfull A
  have hdouble : ∑ u ∈ A, #(A.filter (Gfull.Adj u)) =
      2 * ∑ a ∈ Finset.range k, #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) := by
    rw [Finset.sum_image (fun a ha b hb h => hinjA ha hb h)]
    have hper : ∀ a ∈ Finset.range k, #(A.filter (Gfull.Adj (v (t + a)))) =
        #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) +
        #((Finset.range k).filter (fun b => b < a ∧ Gfull.Adj (v (t + b)) (v (t + a)))) := by
      intro a _
      have hbij : #(A.filter (Gfull.Adj (v (t + (a : ℤ))))) =
          #((Finset.range k).filter (fun b : ℕ => Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ))))) := by
        symm
        refine Finset.card_bij (fun (b : ℕ) _ => v (t + (b : ℤ))) ?_ ?_ ?_
        · intro b hb; have hb' := Finset.mem_filter.mp hb
          exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hb'.1, hb'.2⟩
        · intro b₁ hb₁ b₂ hb₂ heq
          exact hinjA (Finset.mem_filter.mp hb₁).1 (Finset.mem_filter.mp hb₂).1 heq
        · intro u hu; have hu' := Finset.mem_filter.mp hu
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu'.1
          exact ⟨b, Finset.mem_filter.mpr ⟨hb, hu'.2⟩, rfl⟩
      rw [hbij]
      have hsplit : (Finset.range k).filter (fun b : ℕ => Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ)))) =
          (Finset.range k).filter (fun b : ℕ => a < b ∧ Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ)))) ∪
          (Finset.range k).filter (fun b : ℕ => b < a ∧ Gfull.Adj (v (t + (b : ℤ))) (v (t + (a : ℤ)))) := by
        ext b; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hb, hadj⟩
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          rcases lt_trichotomy a b with hlt | rfl | hgt
          · exact Or.inl ⟨hb, hlt, hadj⟩
          · exact (Gfull.loopless.irrefl _ hadj).elim
          · exact Or.inr ⟨hb, hgt, hadj.symm⟩
        · intro h; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at h
          rcases h with ⟨hb, _, hadj⟩ | ⟨hb, _, hadj⟩
          · exact ⟨hb, hadj⟩
          · exact ⟨hb, hadj.symm⟩
      have hdisj : Disjoint ((Finset.range k).filter (fun b : ℕ => a < b ∧ Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ)))))
          ((Finset.range k).filter (fun b : ℕ => b < a ∧ Gfull.Adj (v (t + (b : ℤ))) (v (t + (a : ℤ))))) := by
        rw [Finset.disjoint_left]; intro b h1 h2
        have := (Finset.mem_filter.mp h1).2.1; have := (Finset.mem_filter.mp h2).2.1; omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
    have hsym : ∑ a ∈ Finset.range k, #((Finset.range k).filter (fun b => b < a ∧ Gfull.Adj (v (t + b)) (v (t + a)))) =
        ∑ b ∈ Finset.range k, #((Finset.range k).filter (fun a => b < a ∧ Gfull.Adj (v (t + b)) (v (t + a)))) := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
    rw [hsym]; ring
  have heA : (Gfull.induce (A : Set V)).edgeSet.ncard =
      ∑ a ∈ Finset.range k, #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) := by
    omega
  have hht_le : h_t ≤ t + k := by
    by_contra hgt; push Not at hgt
    have := hht_min (t + k) (by omega) hgt
    have := hf_gt (t + k); omega
  set L := (h_t - t).toNat
  have hL_le : L ≤ k := by omega
  have hL_eq : (L : ℤ) = h_t - t := by omega
  have htail0 : ∑ a ∈ Finset.range k \ Finset.range L,
      #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) = 0 := by
    apply Finset.sum_eq_zero; intro a ha
    have ha_ge : L ≤ a := by have := (Finset.mem_sdiff.mp ha).2; simp only [Finset.mem_range] at this; omega
    have ha_lt : a < k := Finset.mem_range.mp (Finset.mem_sdiff.mp ha).1
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro b hb ⟨hab, hadj⟩
    have hb_lt := Finset.mem_range.mp hb
    have hge := (hadj_iff (t + a) (t + b) (by omega) (by omega)).mp hadj
    have hfa : t + k ≤ f (t + a) := hht_spec.trans (hf_mono h_t (t + a) (by omega))
    omega
  have houter : ∑ a ∈ Finset.range k,
      #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) =
      ∑ a ∈ Finset.range L,
        #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) := by
    have h1 := (Finset.sum_union Finset.disjoint_sdiff (s₁ := Finset.range L) (s₂ := Finset.range k \ Finset.range L)
      (f := fun a => #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))))).symm
    rw [Finset.union_sdiff_of_subset (Finset.range_mono hL_le)] at h1
    rw [← h1, htail0, add_zero]
  have heA_eq : ((Gfull.induce (A : Set V)).edgeSet.ncard : ℤ) =
      ∑ j ∈ Finset.range L, (t + k - f (t + (j : ℤ))) := by
    rw [heA, houter, Nat.cast_sum]
    apply Finset.sum_congr rfl; intro a ha
    have ha_lt : a < L := Finset.mem_range.mp ha
    have hfa_lt : f (t + a) < t + k := hht_min (t + a) (by omega) (by omega)
    have hfa_gt : t + a < f (t + a) := hf_gt (t + a)
    have hcnt : #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ))))) =
        (t + k - f (t + (a : ℤ))).toNat := by
      refine (Finset.card_bij (fun (b : ℕ) _ => ((t + (b : ℤ)) - f (t + (a : ℤ))).toNat) ?_ ?_ ?_).trans
        (Finset.card_range (t + k - f (t + (a : ℤ))).toNat)
      · intro b hb; have hb' := Finset.mem_filter.mp hb
        have hbr := Finset.mem_range.mp hb'.1
        have hge := (hadj_iff (t + a) (t + b) (by omega) (by omega)).mp hb'.2.2
        exact Finset.mem_range.mpr (by omega)
      · intro b₁ hb₁ b₂ hb₂ heq
        have h1 := Finset.mem_filter.mp hb₁; have h2 := Finset.mem_filter.mp hb₂
        have h1r := Finset.mem_range.mp h1.1; have h2r := Finset.mem_range.mp h2.1
        have hg1 := (hadj_iff (t + a) (t + b₁) (by omega) (by omega)).mp h1.2.2
        have hg2 := (hadj_iff (t + a) (t + b₂) (by omega) (by omega)).mp h2.2.2
        omega
      · intro m hm; have hmr := Finset.mem_range.mp hm
        set b := (f (t + a) + m - t).toNat
        refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩, by omega⟩
        rw [hadj_iff (t + a) (t + b) (by omega) (by omega)]; dsimp only [b]; omega
    rw [hcnt]; omega
  rw [← heA_eq]
  exact_mod_cast h50


/-- Maximal-between-color-classes triangle-free extension preserving a 3-coloring. -/
lemma exists_maximal_threeColorable_triangleFree {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (col : V → Fin 3) (hcol : ∀ u v : V, G.Adj u v → col u ≠ col v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
      (∀ u v : V, H.Adj u v → col u ≠ col v) ∧
      (∀ u v : V, col u ≠ col v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w) := by
  classical
  suffices h : ∀ m : ℕ, ∀ G : SimpleGraph V, G.CliqueFree 3 →
      (∀ u v : V, G.Adj u v → col u ≠ col v) →
      Fintype.card (Sym2 V) - #G.edgeFinset ≤ m →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
        (∀ u v : V, H.Adj u v → col u ≠ col v) ∧
        (∀ u v : V, col u ≠ col v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w) from
    h (Fintype.card (Sym2 V) - #G.edgeFinset) G hTF hcol (le_refl _)
  intro m
  induction m with
  | zero =>
    intro G hTF hcol hm
    refine ⟨G, le_refl _, hTF, hcol, ?_⟩
    intro u v hne hna
    exfalso
    have hcard : #G.edgeFinset ≤ Fintype.card (Sym2 V) := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have heq : G.edgeFinset = Finset.univ := Finset.eq_univ_of_card _ (by omega)
    exact hna (SimpleGraph.mem_edgeFinset.mp (heq ▸ Finset.mem_univ s(u, v)))
  | succ m ih =>
    intro G hTF hcol hm
    by_cases hmax : ∀ u v : V, col u ≠ col v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w
    · exact ⟨G, le_refl _, hTF, hcol, hmax⟩
    · push Not at hmax
      obtain ⟨u, v, hcol_uv, hna, hno_cn⟩ := hmax
      have huv : u ≠ v := fun h => hcol_uv (congrArg col h)
      let G' : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
      have hGG' : G ≤ G' := le_sup_left
      have hG'_adj : ∀ a b : V, G'.Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        intro a b
        simp only [G', SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        constructor
        · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩
      have hG'_col : ∀ a b : V, G'.Adj a b → col a ≠ col b := by
        intro a b hab
        rcases (hG'_adj a b).mp hab with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcol a b h
        · exact hcol_uv
        · exact hcol_uv.symm
      have hG'_TF : G'.CliqueFree 3 := by
        intro s hs
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
        have h1 : G'.Adj a b := hs.1 (by simp) (by simp) hab
        have h2 : G'.Adj b c := hs.1 (by simp) (by simp) hbc
        have h3 : G'.Adj a c := hs.1 (by simp) (by simp) hac
        rw [hG'_adj] at h1 h2 h3
        by_cases g1 : G.Adj a b
        · by_cases g2 : G.Adj b c
          · by_cases g3 : G.Adj a c
            · exact not_adj_of_cliqueFree_three hTF g1 g2 g3
            · rcases h3 with h3 | ⟨ha, hc⟩ | ⟨ha, hc⟩
              · exact g3 h3
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g1 g2.symm
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g2.symm g1
          · rcases h2 with h2 | ⟨hb, hc⟩ | ⟨hb, hc⟩
            · exact g2 h2
            · rcases h3 with g3 | ⟨ha, _⟩ | ⟨_, hcu⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g1.symm g3.symm
              · exact hab (ha.trans hb.symm)
              · exact huv (hcu.symm.trans hc)
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨ha, _⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g3.symm g1.symm
              · exact huv (hc.symm.trans hcv)
              · exact hab (ha.trans hb.symm)
        · rcases h1 with h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact g1 h1
          · rcases h2 with g2 | ⟨hbu, _⟩ | ⟨_, hcu⟩
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨hau, _⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g3 g2
              · exact hbc (hb.trans hcv.symm)
              · exact huv (ha.symm.trans hau)
            · exact huv (hb.symm.trans hbu).symm
            · exact hac (ha.trans hcu.symm)
          · rcases h2 with g2 | ⟨_, hcv⟩ | ⟨hbv, _⟩
            · rcases h3 with g3 | ⟨hau, _⟩ | ⟨_, hcu⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g2 g3
              · exact huv (hau.symm.trans ha)
              · exact hbc (hb.trans hcu.symm)
            · exact hac (ha.trans hcv.symm)
            · exact huv (hb.symm.trans hbv)
      have hstrict : #G.edgeFinset < #G'.edgeFinset := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun e he => SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hGG' (SimpleGraph.mem_edgeFinset.mp he)), ?_⟩
        intro heq
        have hmem : s(u, v) ∈ G'.edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr ((hG'_adj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        rw [← heq] at hmem; exact hna (SimpleGraph.mem_edgeFinset.mp hmem)
      have hcard_G' : #G'.edgeFinset ≤ Fintype.card (Sym2 V) := by
        rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      have hstep_m : Fintype.card (Sym2 V) - #G'.edgeFinset ≤ m := by omega
      obtain ⟨H, hG'H, hHTF, hHcol, hHmax⟩ := ih G' hG'_TF hG'_col (by convert hstep_m)
      exact ⟨H, hGG'.trans hG'H, hHTF, hHcol, hHmax⟩

/-- Helper: third color in Fin 3. -/
lemma fin3_third {a b c x : Fin 3} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c)
    (hx1 : x ≠ a) (hx2 : x ≠ b) : x = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases x <;> simp_all

/-- Pure combinatorial helper: strictly increasing functions `f : Fin a -> ℕ` bounded by `b`
    with `b = a` and `f 0 >= 1` force `f i = i + 1` (and bounded by `a - 1` force `f i = i`). -/
lemma strictMono_fin_tight {a : ℕ} (f : Fin a → ℕ)
    (hmono : ∀ i j : Fin a, i < j → f i < f j) :
    ∀ i : Fin a, i.val ≤ f i := by
  intro i
  induction hval : i.val generalizing i with
  | zero => omega
  | succ m ih =>
    have hprev := ih ⟨m, by omega⟩ rfl
    have hlt := hmono ⟨m, by omega⟩ i (Fin.lt_def.mpr (by dsimp only; omega))
    omega

lemma strictMono_fin_eq_id {a : ℕ} (f : Fin a → ℕ)
    (hmono : ∀ i j : Fin a, i < j → f i < f j)
    (hhi : ∀ i : Fin a, f i < a) :
    ∀ i : Fin a, f i = i.val := by
  have hlo : ∀ i : Fin a, i.val ≤ f i := strictMono_fin_tight f hmono
  have hup : ∀ m : ℕ, ∀ i : Fin a, a - 1 - i.val = m → f i ≤ i.val := by
    intro m; induction m with
    | zero => intro i hm; have := hhi i; omega
    | succ m ih =>
      intro i hm
      have hnext := ih ⟨i.val + 1, by omega⟩ (by dsimp only; omega)
      have hlt := hmono i ⟨i.val + 1, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
      dsimp only at hnext; omega
  intro i; have := hlo i; have := hup (a - 1 - i.val) i rfl; omega

lemma strictMono_fin_eq_succ {a : ℕ} (f : Fin a → ℕ)
    (hmono : ∀ i j : Fin a, i < j → f i < f j)
    (h0 : ∀ i : Fin a, 1 ≤ f i) (hhi : ∀ i : Fin a, f i ≤ a) :
    ∀ i : Fin a, f i = i.val + 1 := by
  have h := strictMono_fin_eq_id (fun i => f i - 1)
    (fun i j hij => by have := hmono i j hij; have := h0 i; omega)
    (fun i => by have := hhi i; have := h0 i; omega)
  intro i; have := h i; have := h0 i; omega

/-- Helper: given quotient dimensions `1 <= a <= b <= c` and strictly increasing threshold maps
    `(f, g, h)` encoding a triangle-free maximal-between-parts 3-partite quotient, construct
    an explicit homomorphism into `And(d)` for some `d >= 1`! -/
lemma cjk_quotient_ordered {a b c : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
    (hf_le : ∀ i, f i ≤ b) (hg_le : ∀ j, g j ≤ c) (hh_le : ∀ k, h k ≤ a)
    (hf_sm : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂)
    (hg_sm : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂)
    (hh_sm : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
    (hTF : ∀ (i : Fin a) (j : Fin b) (k : Fin c), ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val))
    (hmaxXY : ∀ (i : Fin a) (j : Fin b), j.val < f i → ∃ k : Fin c, g j ≤ k.val ∧ h k ≤ i.val)
    (hmaxYZ : ∀ (j : Fin b) (k : Fin c), k.val < g j → ∃ i : Fin a, f i ≤ j.val ∧ h k ≤ i.val)
    (hmaxZX : ∀ (k : Fin c) (i : Fin a), i.val < h k → ∃ j : Fin b, f i ≤ j.val ∧ g j ≤ k.val) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φX : Fin a → Fin (3 * d - 1)) (φY : Fin b → Fin (3 * d - 1))
      (φZ : Fin c → Fin (3 * d - 1)),
      (∀ i j, f i ≤ j.val →
        d ≤ ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) ∧
        ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) < 2 * d) ∧
      (∀ j k, g j ≤ k.val →
        d ≤ ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) ∧
        ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) < 2 * d) ∧
      (∀ k i, h k ≤ i.val →
        d ≤ ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) ∧
        ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) < 2 * d) := by
  have hc_le : c ≤ a + 1 := by
    have h1 := strictMono_fin_tight h hh_sm ⟨c - 1, by omega⟩
    have h2 := hh_le ⟨c - 1, by omega⟩
    dsimp only at h1; omega
  -- Case split into the 3 exact shapes: (d-1, d, d), (d, d, d), (d-1, d-1, d)
  by_cases hac : a = c
  · -- Shape (d, d, d) with d = c >= 1
    have hbd : b = c := by omega
    -- At least one of f 0, g 0, h 0 is >= 1 by triangle-freeness at (0, 0, 0)
    have hge1 : 1 ≤ f ⟨0, by omega⟩ ∨ 1 ≤ g ⟨0, by omega⟩ ∨ 1 ≤ h ⟨0, by omega⟩ := by
      have h0 := hTF ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
      dsimp only at h0; omega
    -- Helper when h 0 >= 1 in shape (d, d, d)
    have hDDD : ∀ (a' b' c' : ℕ) (h1 : a' = c') (h2 : b' = c') (hc' : 1 ≤ c')
        (f' : Fin a' → ℕ) (g' : Fin b' → ℕ) (h' : Fin c' → ℕ)
        (_ : ∀ i, f' i ≤ b') (_ : ∀ j, g' j ≤ c') (_ : ∀ k, h' k ≤ a')
        (_ : ∀ i₁ i₂, i₁ < i₂ → f' i₁ < f' i₂)
        (_ : ∀ j₁ j₂, j₁ < j₂ → g' j₁ < g' j₂)
        (_ : ∀ k₁ k₂, k₁ < k₂ → h' k₁ < h' k₂)
        (_ : ∀ i j k, ¬ (f' i ≤ j.val ∧ g' j ≤ k.val ∧ h' k ≤ i.val))
        (_ : ∀ j k, k.val < g' j → ∃ i, f' i ≤ j.val ∧ h' k ≤ i.val)
        (_ : ∀ k i, i.val < h' k → ∃ j, f' i ≤ j.val ∧ g' j ≤ k.val)
        (_ : 1 ≤ h' ⟨0, by omega⟩),
        ∃ (φX : Fin a' → Fin (3 * c' - 1)) (φY : Fin b' → Fin (3 * c' - 1))
          (φZ : Fin c' → Fin (3 * c' - 1)),
          (∀ i j, f' i ≤ j.val →
            c' ≤ ((φY j).val + (3 * c' - 1) - (φX i).val) % (3 * c' - 1) ∧
            ((φY j).val + (3 * c' - 1) - (φX i).val) % (3 * c' - 1) < 2 * c') ∧
          (∀ j k, g' j ≤ k.val →
            c' ≤ ((φZ k).val + (3 * c' - 1) - (φY j).val) % (3 * c' - 1) ∧
            ((φZ k).val + (3 * c' - 1) - (φY j).val) % (3 * c' - 1) < 2 * c') ∧
          (∀ k i, h' k ≤ i.val →
            c' ≤ ((φX i).val + (3 * c' - 1) - (φZ k).val) % (3 * c' - 1) ∧
            ((φX i).val + (3 * c' - 1) - (φZ k).val) % (3 * c' - 1) < 2 * c') := by
      intro a' b' c' h1 h2 hc' f' g' h' hf'l hg'l hh'l hf's hg's hh's hTF' hmYZ' hmZX' hh0
      have hh_all1 : ∀ k : Fin c', 1 ≤ h' k := by
        intro k; by_cases hk0 : k.val = 0
        · have : k = ⟨0, by omega⟩ := Fin.ext hk0; rw [this]; exact hh0
        · have := hh's ⟨0, by omega⟩ k (Fin.lt_def.mpr (by dsimp only; omega)); omega
      have hh_eq : ∀ k : Fin c', h' k = k.val + 1 :=
        strictMono_fin_eq_succ h' hh's hh_all1 (fun k => by have := hh'l k; omega)
      have hg_lt : ∀ j : Fin b', g' j < c' := by
        intro j; by_contra hge
        obtain ⟨i, _, hi⟩ := hmYZ' j ⟨c' - 1, by omega⟩ (by dsimp only; omega)
        have hlast := hh_eq ⟨c' - 1, by omega⟩; dsimp only at hlast; omega
      have hg_eq : ∀ j : Fin b', g' j = j.val :=
        strictMono_fin_eq_id g' hg's (fun j => by have := hg_lt j; omega)
      have hf_lt : ∀ i : Fin a', f' i < b' := by
        intro i; by_contra hge
        have hlast := hh_eq ⟨c' - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmZX' ⟨c' - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a', f' i = i.val :=
        strictMono_fin_eq_id f' hf's (fun i => by have := hf_lt i; omega)
      refine ⟨fun i => if i.val = 0 then ⟨3 * c' - 2, by omega⟩ else ⟨i.val - 1, by omega⟩,
              fun j => ⟨c' - 1 + j.val, by omega⟩,
              fun k => ⟨2 * c' - 1 + k.val, by omega⟩, ?_, ?_, ?_⟩
      · intro i j hij; rw [hf_eq] at hij
        by_cases hi0 : i.val = 0
        · simp only [hi0, ite_true]
          have hmod : (c' - 1 + j.val + (3 * c' - 1) - (3 * c' - 2)) % (3 * c' - 1) = c' + j.val := by
            rw [show c' - 1 + j.val + (3 * c' - 1) - (3 * c' - 2) = c' + j.val by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
        · simp only [hi0, ite_false]
          have hmod : (c' - 1 + j.val + (3 * c' - 1) - (i.val - 1)) % (3 * c' - 1) = c' + (j.val - i.val) := by
            rw [show c' - 1 + j.val + (3 * c' - 1) - (i.val - 1) = (c' + (j.val - i.val)) + (3 * c' - 1) by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
      · intro j k hjk; rw [hg_eq] at hjk
        have hmod : (2 * c' - 1 + k.val + (3 * c' - 1) - (c' - 1 + j.val)) % (3 * c' - 1) = c' + (k.val - j.val) := by
          rw [show 2 * c' - 1 + k.val + (3 * c' - 1) - (c' - 1 + j.val) = (c' + (k.val - j.val)) + (3 * c' - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro k i hki; rw [hh_eq] at hki
        have hi0 : i.val ≠ 0 := by omega
        simp only [hi0, ite_false]
        have hmod : (i.val - 1 + (3 * c' - 1) - (2 * c' - 1 + k.val)) % (3 * c' - 1) = c' + (i.val - 1 - k.val) := by
          rw [show i.val - 1 + (3 * c' - 1) - (2 * c' - 1 + k.val) = c' + (i.val - 1 - k.val) by omega,
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
    rcases hge1 with hf0 | hg0 | hh0
    · obtain ⟨φY, φZ, φX, h1, h2, h3⟩ := hDDD b c a (by omega) (by omega) (by omega) g h f
        hg_le hh_le hf_le hg_sm hh_sm hf_sm (fun j k i ⟨a1, a2, a3⟩ => hTF i j k ⟨a3, a1, a2⟩)
        (fun k i hlt => by obtain ⟨j, h1, h2⟩ := hmaxZX k i hlt; exact ⟨j, h2, h1⟩)
        (fun i j hlt => by obtain ⟨k, h1, h2⟩ := hmaxXY i j hlt; exact ⟨k, h1, h2⟩) hf0
      exact ⟨a, by omega, φX, φY, φZ, h3, h1, h2⟩
    · obtain ⟨φZ, φX, φY, h1, h2, h3⟩ := hDDD c a b (by omega) (by omega) (by omega) h f g
        hh_le hf_le hg_le hh_sm hf_sm hg_sm (fun k i j ⟨a1, a2, a3⟩ => hTF i j k ⟨a2, a3, a1⟩)
        (fun i j hlt => by obtain ⟨k, h1, h2⟩ := hmaxXY i j hlt; exact ⟨k, h2, h1⟩)
        (fun j k hlt => by obtain ⟨i, h1, h2⟩ := hmaxYZ j k hlt; exact ⟨i, h2, h1⟩) hg0
      exact ⟨b, by omega, φX, φY, φZ, h2, h3, h1⟩
    · obtain ⟨φX, φY, φZ, h1, h2, h3⟩ := hDDD a b c hac hbd (by omega) f g h
        hf_le hg_le hh_le hf_sm hg_sm hh_sm hTF hmaxYZ hmaxZX hh0
      exact ⟨c, by omega, φX, φY, φZ, h1, h2, h3⟩
  · -- Now a = c - 1 (so c >= 2)
    have ha_eq : a = c - 1 := by omega
    have hc2 : 2 ≤ c := by omega
    have hh_eq : ∀ k : Fin c, h k = k.val :=
      strictMono_fin_eq_id h hh_sm (fun k => by have := hh_le k; omega)
    have hg_lt : ∀ j : Fin b, g j < c := by
      intro j; by_contra hge
      obtain ⟨i, _, hi⟩ := hmaxYZ j ⟨c - 1, by omega⟩ (by dsimp only; omega)
      have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast; omega
    by_cases hbc_eq : b = c
    · -- Shape (d-1, d, d): h k = k, g j = j, f i = i + 1 -> And(c)
      have hg_eq : ∀ j : Fin b, g j = j.val :=
        strictMono_fin_eq_id g hg_sm (fun j => by have := hg_lt j; omega)
      have hf_pos : ∀ i : Fin a, 1 ≤ f i := by
        intro i; by_contra h0
        have hg0 := hg_eq ⟨0, by omega⟩; have hh0 := hh_eq ⟨0, by omega⟩
        dsimp only at hg0 hh0
        exact hTF i ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨by omega, by omega, by omega⟩
      have hf_lt : ∀ i : Fin a, f i ≤ a := by
        intro i; by_contra hgt
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmaxZX ⟨c - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a, f i = i.val + 1 := strictMono_fin_eq_succ f hf_sm hf_pos hf_lt
      refine ⟨c, by omega,
              fun i => ⟨i.val, by omega⟩,
              fun j => ⟨c - 1 + j.val, by omega⟩,
              fun k => ⟨2 * c - 1 + k.val, by omega⟩, ?_, ?_, ?_⟩
      · intro i j hij; rw [hf_eq] at hij
        have hmod : (c - 1 + j.val + (3 * c - 1) - i.val) % (3 * c - 1) = c + (j.val - (i.val + 1)) := by
          rw [show c - 1 + j.val + (3 * c - 1) - i.val = (c + (j.val - (i.val + 1))) + (3 * c - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro j k hjk; rw [hg_eq] at hjk
        have hmod : (2 * c - 1 + k.val + (3 * c - 1) - (c - 1 + j.val)) % (3 * c - 1) = c + (k.val - j.val) := by
          rw [show 2 * c - 1 + k.val + (3 * c - 1) - (c - 1 + j.val) = (c + (k.val - j.val)) + (3 * c - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro k i hki; rw [hh_eq] at hki
        have hmod : (i.val + (3 * c - 1) - (2 * c - 1 + k.val)) % (3 * c - 1) = c + (i.val - k.val) := by
          rw [show i.val + (3 * c - 1) - (2 * c - 1 + k.val) = c + (i.val - k.val) by omega,
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
    · -- Shape (d-1, d-1, d): h k = k, g j = j + 1, f i = i -> And(c - 1) via folding Z_0 and Z_{c-1}!
      have hb_eq : b = c - 1 := by omega
      have hg_pos : ∀ j : Fin b, 1 ≤ g j := by
        intro j; by_contra h0
        have hg0 : g ⟨0, by omega⟩ = 0 := by
          by_cases hj0 : j.val = 0
          · have : j = ⟨0, by omega⟩ := Fin.ext hj0; rw [← this]; omega
          · have := hg_sm ⟨0, by omega⟩ j (Fin.lt_def.mpr (by dsimp only; omega)); omega
        have hf_all1 : ∀ i : Fin a, 1 ≤ f i := by
          intro i; by_contra hfi0
          have hh0 := hh_eq ⟨0, by omega⟩; dsimp only at hh0
          exact hTF i ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨by omega, by omega, by omega⟩
        have hf_eq1 : ∀ i : Fin a, f i = i.val + 1 :=
          strictMono_fin_eq_succ f hf_sm hf_all1 (fun i => by have := hf_le i; omega)
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j', hj', _⟩ := hmaxZX ⟨c - 1, by omega⟩ ⟨a - 1, by omega⟩ (by dsimp only; omega)
        have hfa := hf_eq1 ⟨a - 1, by omega⟩; dsimp only at hfa; omega
      have hg_eq : ∀ j : Fin b, g j = j.val + 1 :=
        strictMono_fin_eq_succ g hg_sm hg_pos (fun j => by have := hg_lt j; omega)
      have hf_lt : ∀ i : Fin a, f i < b := by
        intro i; by_contra hge
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmaxZX ⟨c - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a, f i = i.val :=
        strictMono_fin_eq_id f hf_sm (fun i => by have := hf_lt i; omega)
      set d' := c - 1
      have hd'0 : d' ≠ 0 := by omega
      refine ⟨d', by omega,
              fun i => ⟨d' - 1 + i.val, by omega⟩,
              fun j => ⟨2 * d' - 1 + j.val, by omega⟩,
              fun k => if k.val = 0 then ⟨3 * d' - 2, by omega⟩
                       else if k.val = d' then ⟨d' - 1, by omega⟩
                       else ⟨k.val - 1, by omega⟩, ?_, ?_, ?_⟩
      · intro i j hij; rw [hf_eq] at hij
        have hmod : (2 * d' - 1 + j.val + (3 * d' - 1) - (d' - 1 + i.val)) % (3 * d' - 1) = d' + (j.val - i.val) := by
          rw [show 2 * d' - 1 + j.val + (3 * d' - 1) - (d' - 1 + i.val) = (d' + (j.val - i.val)) + (3 * d' - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro j k hjk; rw [hg_eq] at hjk
        have hk0 : k.val ≠ 0 := by omega
        by_cases hkd : k.val = d'
        · simp only [hkd, hd'0, ite_false, ite_true]
          have hmod : (d' - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val)) % (3 * d' - 1) = 2 * d' - 1 - j.val := by
            rw [show d' - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val) = 2 * d' - 1 - j.val by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
        · simp only [hk0, hkd, ite_false]
          have hmod : (k.val - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val)) % (3 * d' - 1) = d' + (k.val - 1 - j.val) := by
            rw [show k.val - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val) = d' + (k.val - 1 - j.val) by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
      · intro k i hki; rw [hh_eq] at hki
        have hkd : k.val ≠ d' := by omega
        by_cases hk0 : k.val = 0
        · simp only [hk0, ite_true]
          have hmod : (d' - 1 + i.val + (3 * d' - 1) - (3 * d' - 2)) % (3 * d' - 1) = d' + i.val := by
            rw [show d' - 1 + i.val + (3 * d' - 1) - (3 * d' - 2) = d' + i.val by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
        · simp only [hk0, hkd, ite_false]
          have hmod : (d' - 1 + i.val + (3 * d' - 1) - (k.val - 1)) % (3 * d' - 1) = d' + (i.val - k.val) := by
            rw [show d' - 1 + i.val + (3 * d' - 1) - (k.val - 1) = (d' + (i.val - k.val)) + (3 * d' - 1) by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega

/-- Helper: And(d) adjacency condition is symmetric in `(u, v)`. -/
lemma cjk_sym_mod {d : ℕ} (hd : 1 ≤ d) (u v : Fin (3 * d - 1))
    (h : d ≤ (v.val + (3 * d - 1) - u.val) % (3 * d - 1) ∧
      (v.val + (3 * d - 1) - u.val) % (3 * d - 1) < 2 * d) :
    d ≤ (u.val + (3 * d - 1) - v.val) % (3 * d - 1) ∧
    (u.val + (3 * d - 1) - v.val) % (3 * d - 1) < 2 * d := by
  have hu := u.isLt; have hv := v.isLt
  by_cases hle : u.val ≤ v.val
  · have e1 : (v.val + (3 * d - 1) - u.val) % (3 * d - 1) = v.val - u.val := by
      rw [show v.val + (3 * d - 1) - u.val = (v.val - u.val) + (3 * d - 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (u.val + (3 * d - 1) - v.val) % (3 * d - 1) = (3 * d - 1) - (v.val - u.val) := by
      rw [show u.val + (3 * d - 1) - v.val = (3 * d - 1) - (v.val - u.val) by omega,
        Nat.mod_eq_of_lt (by omega)]
    omega
  · have e1 : (v.val + (3 * d - 1) - u.val) % (3 * d - 1) = v.val + (3 * d - 1) - u.val :=
      Nat.mod_eq_of_lt (by omega)
    have e2 : (u.val + (3 * d - 1) - v.val) % (3 * d - 1) = u.val - v.val := by
      rw [show u.val + (3 * d - 1) - v.val = (u.val - v.val) + (3 * d - 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Helper: dual threshold function for order reversal of a strictly monotone threshold map. -/
lemma cjk_dual_threshold {m n : ℕ} (t : Fin m → ℕ)
    (hts : ∀ x₁ x₂ : Fin m, x₁ < x₂ → t x₁ < t x₂) :
    ∀ (y' : Fin n) (x' : Fin m),
      t ⟨m - 1 - x'.val, by have := x'.isLt; omega⟩ ≤ n - 1 - y'.val ↔
      m - #(Finset.univ.filter (fun u : Fin m => t ⟨m - 1 - u.val, by have := u.isLt; omega⟩ ≤ n - 1 - y'.val)) ≤ x'.val := by
  classical
  intro y' x'
  set S := Finset.univ.filter (fun u : Fin m => t ⟨m - 1 - u.val, by have := u.isLt; omega⟩ ≤ n - 1 - y'.val)
  have hSup : ∀ u₁ u₂ : Fin m, u₁ ∈ S → u₁ ≤ u₂ → u₂ ∈ S := by
    intro u₁ u₂ hu1 hle
    have h1 := (Finset.mem_filter.mp hu1).2
    apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact h1
    · have hu1l := u₁.isLt; have hu2l := u₂.isLt; have hlt' := Fin.lt_def.mp hlt
      have := hts ⟨m - 1 - u₂.val, by omega⟩ ⟨m - 1 - u₁.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
      omega
  have hS_eq : S = Finset.univ.filter (fun u : Fin m => m - #S ≤ u.val) := by
    have hcard_R : #(Finset.univ.filter (fun u : Fin m => m - #S ≤ u.val)) = #S := by
      have hSle : #S ≤ m := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      refine (Finset.card_bij (fun (u : Fin m) _ => u.val - (m - #S)) ?_ ?_ ?_).trans (Finset.card_range #S)
      · intro u hu; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hu).2; have := u.isLt; omega)
      · intro u1 hu1 u2 hu2 heq
        have := (Finset.mem_filter.mp hu1).2; have := (Finset.mem_filter.mp hu2).2; exact Fin.ext (by omega)
      · intro r hr; have hr' := Finset.mem_range.mp hr
        exact ⟨⟨m - #S + r, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
    by_cases hsub : S ⊆ Finset.univ.filter (fun u : Fin m => m - #S ≤ u.val)
    · exact Finset.eq_of_subset_of_card_le hsub (by omega)
    · exfalso; obtain ⟨u0, hu0S, hu0n⟩ := Finset.not_subset.mp hsub
      have hu0lt : u0.val < m - #S := by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu0n; omega
      have hge : Finset.univ.filter (fun u : Fin m => u0.val ≤ u.val) ⊆ S :=
        fun u hu => hSup u0 u hu0S (Fin.le_def.mpr (Finset.mem_filter.mp hu).2)
      have hcard_ge : #(Finset.univ.filter (fun u : Fin m => u0.val ≤ u.val)) = m - u0.val := by
        refine (Finset.card_bij (fun (u : Fin m) _ => u.val - u0.val) ?_ ?_ ?_).trans (Finset.card_range (m - u0.val))
        · intro u hu; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hu).2; have := u.isLt; omega)
        · intro u1 hu1 u2 hu2 heq
          have := (Finset.mem_filter.mp hu1).2; have := (Finset.mem_filter.mp hu2).2; exact Fin.ext (by omega)
        · intro r hr; have hr' := Finset.mem_range.mp hr
          exact ⟨⟨u0.val + r, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
      have := Finset.card_le_card hge; omega
  have hmem := Finset.ext_iff.mp hS_eq x'
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem

/-- Reversing all three orders handles `b ≤ a ≤ c` via `cjk_quotient_ordered`. -/
lemma cjk_quotient_rev {a b c : ℕ} (_ha : 1 ≤ a) (hb : 1 ≤ b) (_hc : 1 ≤ c)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
    (hfl : ∀ i, f i ≤ b) (hgl : ∀ j, g j ≤ c) (hhl : ∀ k, h k ≤ a)
    (hfs : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂)
    (hgs : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂)
    (hhs : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
    (hTF' : ∀ i j k, ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val))
    (hXY : ∀ i j, j.val < f i → ∃ k, g j ≤ k.val ∧ h k ≤ i.val)
    (hYZ : ∀ j k, k.val < g j → ∃ i, f i ≤ j.val ∧ h k ≤ i.val)
    (hZX : ∀ k i, i.val < h k → ∃ j, f i ≤ j.val ∧ g j ≤ k.val)
    (hba : b ≤ a) (hac : a ≤ c) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φX : Fin a → Fin (3 * d - 1)) (φY : Fin b → Fin (3 * d - 1))
      (φZ : Fin c → Fin (3 * d - 1)),
      (∀ i j, f i ≤ j.val →
        d ≤ ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) ∧
        ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) < 2 * d) ∧
      (∀ j k, g j ≤ k.val →
        d ≤ ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) ∧
        ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) < 2 * d) ∧
      (∀ k i, h k ≤ i.val →
        d ≤ ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) ∧
        ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) < 2 * d) := by
  classical
  let f' : Fin b → ℕ := fun j' => a - #(Finset.univ.filter (fun i' : Fin a => f ⟨a - 1 - i'.val, by omega⟩ ≤ b - 1 - j'.val))
  let g' : Fin a → ℕ := fun i' => c - #(Finset.univ.filter (fun k' : Fin c => h ⟨c - 1 - k'.val, by omega⟩ ≤ a - 1 - i'.val))
  let h' : Fin c → ℕ := fun k' => b - #(Finset.univ.filter (fun j' : Fin b => g ⟨b - 1 - j'.val, by omega⟩ ≤ c - 1 - k'.val))
  have hf'_iff : ∀ (j' : Fin b) (i' : Fin a), f ⟨a - 1 - i'.val, by omega⟩ ≤ b - 1 - j'.val ↔ f' j' ≤ i'.val :=
    cjk_dual_threshold f hfs
  have hg'_iff : ∀ (i' : Fin a) (k' : Fin c), h ⟨c - 1 - k'.val, by omega⟩ ≤ a - 1 - i'.val ↔ g' i' ≤ k'.val :=
    cjk_dual_threshold h hhs
  have hh'_iff : ∀ (k' : Fin c) (j' : Fin b), g ⟨b - 1 - j'.val, by omega⟩ ≤ c - 1 - k'.val ↔ h' k' ≤ j'.val :=
    cjk_dual_threshold g hgs
  have hf'_le : ∀ j', f' j' ≤ a := fun _ => Nat.sub_le _ _
  have hg'_le : ∀ i', g' i' ≤ c := fun _ => Nat.sub_le _ _
  have hh'_le : ∀ k', h' k' ≤ b := fun _ => Nat.sub_le _ _
  have hf'_sm : ∀ j1 j2 : Fin b, j1 < j2 → f' j1 < f' j2 := by
    intro j1 j2 hlt
    have hle : f' j1 ≤ f' j2 := by
      apply Nat.sub_le_sub_left; apply Finset.card_le_card; intro i' hi'
      have h1 := (Finset.mem_filter.mp hi').2; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    by_contra hnot; have heq : f' j1 = f' j2 := by omega
    have hj1 := j1.isLt; have hj2 := j2.isLt; have hlt' := Fin.lt_def.mp hlt
    have hg_lt' : g ⟨b - 1 - j2.val, by omega⟩ < g ⟨b - 1 - j1.val, by omega⟩ :=
      hgs ⟨b - 1 - j2.val, by omega⟩ ⟨b - 1 - j1.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
    have hgj2_lt : g ⟨b - 1 - j2.val, by omega⟩ < c := by have := hgl ⟨b - 1 - j1.val, by omega⟩; omega
    obtain ⟨i, hfi, hhk⟩ := hYZ ⟨b - 1 - j1.val, by omega⟩ ⟨g ⟨b - 1 - j2.val, by omega⟩, hgj2_lt⟩ hg_lt'
    let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
    have hi_inv : (⟨a - 1 - i'.val, by omega⟩ : Fin a) = i := Fin.ext (by dsimp only [i']; omega)
    have h1 : f' j1 ≤ i'.val := (hf'_iff j1 i').mp (by rw [hi_inv]; exact hfi)
    rw [heq] at h1
    have h2 : f i ≤ b - 1 - j2.val := by have := (hf'_iff j2 i').mpr h1; rwa [hi_inv] at this
    exact hTF' i ⟨b - 1 - j2.val, by omega⟩ ⟨g ⟨b - 1 - j2.val, by omega⟩, hgj2_lt⟩ ⟨h2, le_refl _, hhk⟩
  have hg'_sm : ∀ i1 i2 : Fin a, i1 < i2 → g' i1 < g' i2 := by
    intro i1 i2 hlt
    have hle : g' i1 ≤ g' i2 := by
      apply Nat.sub_le_sub_left; apply Finset.card_le_card; intro k' hk'
      have h1 := (Finset.mem_filter.mp hk').2; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    by_contra hnot; have heq : g' i1 = g' i2 := by omega
    have hi1 := i1.isLt; have hi2 := i2.isLt; have hlt' := Fin.lt_def.mp hlt
    have hf_lt' : f ⟨a - 1 - i2.val, by omega⟩ < f ⟨a - 1 - i1.val, by omega⟩ :=
      hfs ⟨a - 1 - i2.val, by omega⟩ ⟨a - 1 - i1.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
    have hfi2_lt : f ⟨a - 1 - i2.val, by omega⟩ < b := by have := hfl ⟨a - 1 - i1.val, by omega⟩; omega
    obtain ⟨k, hgk, hhk⟩ := hXY ⟨a - 1 - i1.val, by omega⟩ ⟨f ⟨a - 1 - i2.val, by omega⟩, hfi2_lt⟩ hf_lt'
    let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
    have hk_inv : (⟨c - 1 - k'.val, by omega⟩ : Fin c) = k := Fin.ext (by dsimp only [k']; omega)
    have h1 : g' i1 ≤ k'.val := (hg'_iff i1 k').mp (by rw [hk_inv]; exact hhk)
    rw [heq] at h1
    have h2 : h k ≤ a - 1 - i2.val := by have := (hg'_iff i2 k').mpr h1; rwa [hk_inv] at this
    exact hTF' ⟨a - 1 - i2.val, by omega⟩ ⟨f ⟨a - 1 - i2.val, by omega⟩, hfi2_lt⟩ k ⟨le_refl _, hgk, h2⟩
  have hh'_sm : ∀ k1 k2 : Fin c, k1 < k2 → h' k1 < h' k2 := by
    intro k1 k2 hlt
    have hle : h' k1 ≤ h' k2 := by
      apply Nat.sub_le_sub_left; apply Finset.card_le_card; intro j' hj'
      have h1 := (Finset.mem_filter.mp hj').2; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    by_contra hnot; have heq : h' k1 = h' k2 := by omega
    have hk1 := k1.isLt; have hk2 := k2.isLt; have hlt' := Fin.lt_def.mp hlt
    have hh_lt' : h ⟨c - 1 - k2.val, by omega⟩ < h ⟨c - 1 - k1.val, by omega⟩ :=
      hhs ⟨c - 1 - k2.val, by omega⟩ ⟨c - 1 - k1.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
    have hhk2_lt : h ⟨c - 1 - k2.val, by omega⟩ < a := by have := hhl ⟨c - 1 - k1.val, by omega⟩; omega
    obtain ⟨j, hfj, hgj⟩ := hZX ⟨c - 1 - k1.val, by omega⟩ ⟨h ⟨c - 1 - k2.val, by omega⟩, hhk2_lt⟩ hh_lt'
    let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
    have hj_inv : (⟨b - 1 - j'.val, by omega⟩ : Fin b) = j := Fin.ext (by dsimp only [j']; omega)
    have h1 : h' k1 ≤ j'.val := (hh'_iff k1 j').mp (by rw [hj_inv]; exact hgj)
    rw [heq] at h1
    have h2 : g j ≤ c - 1 - k2.val := by have := (hh'_iff k2 j').mpr h1; rwa [hj_inv] at this
    exact hTF' ⟨h ⟨c - 1 - k2.val, by omega⟩, hhk2_lt⟩ j ⟨c - 1 - k2.val, by omega⟩ ⟨hfj, h2, le_refl _⟩
  obtain ⟨d, hd, φY', φX', φZ', h1, h2, h3⟩ := cjk_quotient_ordered hb hba hac f' g' h'
    hf'_le hg'_le hh'_le hf'_sm hg'_sm hh'_sm
    (fun j' i' k' ⟨a1, a2, a3⟩ => hTF' ⟨a - 1 - i'.val, by omega⟩ ⟨b - 1 - j'.val, by omega⟩
      ⟨c - 1 - k'.val, by omega⟩ ⟨(hf'_iff j' i').mpr a1, (hh'_iff k' j').mpr a3, (hg'_iff i' k').mpr a2⟩)
    (fun j' i' hlt => by
      have hna : b - 1 - j'.val < f ⟨a - 1 - i'.val, by omega⟩ := by
        by_contra hle; have := (hf'_iff j' i').mp (by omega); omega
      obtain ⟨k, hgk, hhk⟩ := hXY ⟨a - 1 - i'.val, by omega⟩ ⟨b - 1 - j'.val, by omega⟩ hna
      let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
      have hk_inv : (⟨c - 1 - k'.val, by omega⟩ : Fin c) = k := Fin.ext (by dsimp only [k']; omega)
      refine ⟨k', (hg'_iff i' k').mp (by rw [hk_inv]; exact hhk),
        (hh'_iff k' j').mp (by dsimp only [k']; omega)⟩)
    (fun i' k' hlt => by
      have hna : a - 1 - i'.val < h ⟨c - 1 - k'.val, by omega⟩ := by
        by_contra hle; have := (hg'_iff i' k').mp (by omega); omega
      obtain ⟨j, hfj, hgj⟩ := hZX ⟨c - 1 - k'.val, by omega⟩ ⟨a - 1 - i'.val, by omega⟩ hna
      let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
      have hj_inv : (⟨b - 1 - j'.val, by omega⟩ : Fin b) = j := Fin.ext (by dsimp only [j']; omega)
      refine ⟨j', (hf'_iff j' i').mp (by dsimp only [j']; omega),
        (hh'_iff k' j').mp (by rw [hj_inv]; exact hgj)⟩)
    (fun k' j' hlt => by
      have hna : c - 1 - k'.val < g ⟨b - 1 - j'.val, by omega⟩ := by
        by_contra hle; have := (hh'_iff k' j').mp (by omega); omega
      obtain ⟨i, hfi, hhk⟩ := hYZ ⟨b - 1 - j'.val, by omega⟩ ⟨c - 1 - k'.val, by omega⟩ hna
      let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
      have hi_inv : (⟨a - 1 - i'.val, by omega⟩ : Fin a) = i := Fin.ext (by dsimp only [i']; omega)
      refine ⟨i', (hf'_iff j' i').mp (by rw [hi_inv]; exact hfi),
        (hg'_iff i' k').mp (by dsimp only [i']; omega)⟩)
  refine ⟨d, hd, fun i => φX' ⟨a - 1 - i.val, by omega⟩, fun j => φY' ⟨b - 1 - j.val, by omega⟩,
    fun k => φZ' ⟨c - 1 - k.val, by omega⟩, ?_, ?_, ?_⟩
  · intro i j hij
    let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
    let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
    have hi_inv : (⟨a - 1 - i'.val, by omega⟩ : Fin a) = i := Fin.ext (by dsimp only [i']; omega)
    exact cjk_sym_mod hd _ _ (h1 j' i' ((hf'_iff j' i').mp (by rw [hi_inv]; dsimp only [j']; omega)))
  · intro j k hjk
    let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
    let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
    have hj_inv : (⟨b - 1 - j'.val, by omega⟩ : Fin b) = j := Fin.ext (by dsimp only [j']; omega)
    exact cjk_sym_mod hd _ _ (h3 k' j' ((hh'_iff k' j').mp (by rw [hj_inv]; dsimp only [k']; omega)))
  · intro k i hki
    let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
    let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
    have hk_inv : (⟨c - 1 - k'.val, by omega⟩ : Fin c) = k := Fin.ext (by dsimp only [k']; omega)
    exact cjk_sym_mod hd _ _ (h2 i' k' ((hg'_iff i' k').mp (by rw [hk_inv]; dsimp only [i']; omega)))

/-- Full S_3 dispatch for any quotient dimensions `(a, b, c)`. -/
lemma cjk_quotient_S3 {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
    (hfl : ∀ i, f i ≤ b) (hgl : ∀ j, g j ≤ c) (hhl : ∀ k, h k ≤ a)
    (hfs : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂)
    (hgs : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂)
    (hhs : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
    (hTF' : ∀ i j k, ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val))
    (hXY : ∀ i j, j.val < f i → ∃ k, g j ≤ k.val ∧ h k ≤ i.val)
    (hYZ : ∀ j k, k.val < g j → ∃ i, f i ≤ j.val ∧ h k ≤ i.val)
    (hZX : ∀ k i, i.val < h k → ∃ j, f i ≤ j.val ∧ g j ≤ k.val) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φX : Fin a → Fin (3 * d - 1)) (φY : Fin b → Fin (3 * d - 1))
      (φZ : Fin c → Fin (3 * d - 1)),
      (∀ i j, f i ≤ j.val →
        d ≤ ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) ∧
        ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) < 2 * d) ∧
      (∀ j k, g j ≤ k.val →
        d ≤ ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) ∧
        ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) < 2 * d) ∧
      (∀ k i, h k ≤ i.val →
        d ≤ ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) ∧
        ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) < 2 * d) := by
  by_cases h1 : a ≤ b
  · by_cases h2 : b ≤ c
    · exact cjk_quotient_ordered ha h1 h2 f g h hfl hgl hhl hfs hgs hhs hTF' hXY hYZ hZX
    · by_cases h3 : a ≤ c
      · obtain ⟨d, hd, φZ, φX, φY, p1, p2, p3⟩ := cjk_quotient_rev hc ha hb h f g hhl hfl hgl hhs hfs hgs
          (fun k i j ⟨x1, x2, x3⟩ => hTF' i j k ⟨x2, x3, x1⟩) hZX
          (fun i j hlt => by obtain ⟨k, q1, q2⟩ := hXY i j hlt; exact ⟨k, q2, q1⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩) h3 (by omega)
        exact ⟨d, hd, φX, φY, φZ, p2, p3, p1⟩
      · obtain ⟨d, hd, φZ, φX, φY, p1, p2, p3⟩ := cjk_quotient_ordered hc (by omega) h1 h f g
          hhl hfl hgl hhs hfs hgs (fun k i j ⟨x1, x2, x3⟩ => hTF' i j k ⟨x2, x3, x1⟩) hZX
          (fun i j hlt => by obtain ⟨k, q1, q2⟩ := hXY i j hlt; exact ⟨k, q2, q1⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩)
        exact ⟨d, hd, φX, φY, φZ, p2, p3, p1⟩
  · by_cases h2 : a ≤ c
    · exact cjk_quotient_rev ha hb hc f g h hfl hgl hhl hfs hgs hhs hTF' hXY hYZ hZX (by omega) h2
    · by_cases h3 : b ≤ c
      · obtain ⟨d, hd, φY, φZ, φX, p1, p2, p3⟩ := cjk_quotient_ordered hb h3 (by omega) g h f
          hgl hhl hfl hgs hhs hfs (fun j k i ⟨x1, x2, x3⟩ => hTF' i j k ⟨x3, x1, x2⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩)
          (fun k i hlt => by obtain ⟨j, q1, q2⟩ := hZX k i hlt; exact ⟨j, q2, q1⟩) hXY
        exact ⟨d, hd, φX, φY, φZ, p3, p1, p2⟩
      · obtain ⟨d, hd, φY, φZ, φX, p1, p2, p3⟩ := cjk_quotient_rev hb hc ha g h f hgl hhl hfl hgs hhs hfs
          (fun j k i ⟨x1, x2, x3⟩ => hTF' i j k ⟨x3, x1, x2⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩)
          (fun k i hlt => by obtain ⟨j, q1, q2⟩ := hZX k i hlt; exact ⟨j, q2, q1⟩) hXY (by omega) (by omega)
        exact ⟨d, hd, φX, φY, φZ, p3, p1, p2⟩

/-- Chen-Jin-Koh (1997) Classification (elementary all-finite-n):
    Every 3-colorable triangle-free graph with 3δ(G) > n admits a homomorphism G -> And(d) for some d >= 1! -/
theorem chen_jin_koh_hom_andrasfai {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (h3col : G.Colorable 3)
    (h3d : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φ : V → Fin (3 * d - 1)),
      ∀ u v : V, G.Adj u v →
        d ≤ ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) ∧
        ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) < 2 * d := by
  classical
  obtain ⟨c3⟩ := h3col
  let col : V → Fin 3 := fun v => c3 v
  have hcol : ∀ u v : V, G.Adj u v → col u ≠ col v := fun u v h => c3.valid h
  obtain ⟨H, hGH, hHTF, hHcol, hHmax⟩ := exists_maximal_threeColorable_triangleFree G hTF col hcol
  -- Sufficient to find And(d) homomorphism for H
  suffices hH : ∃ (d : ℕ) (_ : 1 ≤ d) (φ : V → Fin (3 * d - 1)),
      ∀ u v : V, H.Adj u v →
        d ≤ ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) ∧
        ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) < 2 * d by
    obtain ⟨d, hd, φ, hφ⟩ := hH
    exact ⟨d, hd, φ, fun u v huv => hφ u v (hGH huv)⟩
  set n := Fintype.card V
  have hH3d : ∀ v : V, n < 3 * #(Finset.univ.filter (H.Adj v)) := by
    intro v
    have h1 := h3d v
    rw [Set.ncard_eq_toFinset_card'] at h1
    have hsub : (G.neighborSet v).toFinset ⊆ Finset.univ.filter (H.Adj v) := by
      intro w hw; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGH (Set.mem_toFinset.mp hw)⟩
    have := Finset.card_le_card hsub; omega
  let P : Fin 3 → Finset V := fun c => Finset.univ.filter (fun v => col v = c)
  -- If any color class is empty, H is bipartite -> And(1) = K_2!
  by_cases h0 : P 0 = ∅
  · refine ⟨1, le_refl 1, fun v => if col v = 1 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ?_⟩
    intro u v huv
    have hne := hHcol u v huv
    have hu0 : col u ≠ 0 := fun hc => Finset.notMem_empty u (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hv0 : col v ≠ 0 := fun hc => Finset.notMem_empty v (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    generalize hcu : col u = cu at hne hu0 ⊢; generalize hcv : col v = cv at hne hv0 ⊢
    fin_cases cu <;> fin_cases cv <;> simp_all
  by_cases h1 : P 1 = ∅
  · refine ⟨1, le_refl 1, fun v => if col v = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ?_⟩
    intro u v huv
    have hne := hHcol u v huv
    have hu1 : col u ≠ 1 := fun hc => Finset.notMem_empty u (h1 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hv1 : col v ≠ 1 := fun hc => Finset.notMem_empty v (h1 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    generalize hcu : col u = cu at hne hu1 ⊢; generalize hcv : col v = cv at hne hv1 ⊢
    fin_cases cu <;> fin_cases cv <;> simp_all
  by_cases h2 : P 2 = ∅
  · refine ⟨1, le_refl 1, fun v => if col v = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ?_⟩
    intro u v huv
    have hne := hHcol u v huv
    have hu2 : col u ≠ 2 := fun hc => Finset.notMem_empty u (h2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hv2 : col v ≠ 2 := fun hc => Finset.notMem_empty v (h2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    generalize hcu : col u = cu at hne hu2 ⊢; generalize hcv : col v = cv at hne hv2 ⊢
    fin_cases cu <;> fin_cases cv <;> simp_all
  have hP_ne : ∀ c : Fin 3, (P c).Nonempty := fun c => by
    fin_cases c
    · exact Finset.nonempty_iff_ne_empty.mpr h0
    · exact Finset.nonempty_iff_ne_empty.mpr h1
    · exact Finset.nonempty_iff_ne_empty.mpr h2
  -- Step 1: No induced 2K_2 between any two distinct color classes (6-line C_6 cap-2 proof!)
  have hno2K2 : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 ∈ P c1, ∀ x2 ∈ P c1, ∀ y1 ∈ P c2, ∀ y2 ∈ P c2,
      H.Adj x1 y1 → H.Adj x2 y2 → ¬ H.Adj x1 y2 → ¬ H.Adj x2 y1 → False := by
    intro c1 c2 hc12 x1 hx1 x2 hx2 y1 hy1 y2 hy2 h11 h22 h12 h21
    have hcx1 : col x1 = c1 := (Finset.mem_filter.mp hx1).2
    have hcx2 : col x2 = c1 := (Finset.mem_filter.mp hx2).2
    have hcy1 : col y1 = c2 := (Finset.mem_filter.mp hy1).2
    have hcy2 : col y2 = c2 := (Finset.mem_filter.mp hy2).2
    obtain ⟨z1, hz1x, hz1y⟩ := hHmax x1 y2 (by rw [hcx1, hcy2]; exact hc12) h12
    obtain ⟨z2, hz2x, hz2y⟩ := hHmax x2 y1 (by rw [hcx2, hcy1]; exact hc12) h21
    let c3' : Fin 3 := 0 - c1 - c2
    have hc3_ne1 : c1 ≠ c3' := by dsimp only [c3']; fin_cases c1 <;> fin_cases c2 <;> first | exact (hc12 rfl).elim | decide
    have hc3_ne2 : c2 ≠ c3' := by dsimp only [c3']; fin_cases c1 <;> fin_cases c2 <;> first | exact (hc12 rfl).elim | decide
    have hc3_eq : ∀ z : V, col z ≠ c1 → col z ≠ c2 → col z = c3' := fun z hz1 hz2 =>
      fin3_third hc12 hc3_ne1 hc3_ne2 hz1 hz2
    have hcz1 : col z1 = c3' := hc3_eq z1 (by rw [← hcx1]; exact hHcol z1 x1 hz1x.symm)
      (by rw [← hcy2]; exact hHcol z1 y2 hz1y.symm)
    have hcz2 : col z2 = c3' := hc3_eq z2 (by rw [← hcx2]; exact hHcol z2 x2 hz2x.symm)
      (by rw [← hcy1]; exact hHcol z2 y1 hz2y.symm)
    let w : Fin 6 → V := ![x1, y1, z2, x2, y2, z1]
    have hw_cap2 : ∀ u : V, #(Finset.univ.filter (fun i : Fin 6 => H.Adj u (w i))) ≤ 2 := by
      intro u
      let b : Fin 6 → ℕ := fun i => if H.Adj u (w i) then 1 else 0
      have hcard : #(Finset.univ.filter (fun i : Fin 6 => H.Adj u (w i))) =
          b 0 + b 1 + b 2 + b 3 + b 4 + b 5 := by rw [Finset.card_filter, Fin.sum_univ_six]
      rw [hcard]
      have hna : ∀ {i j : Fin 6}, H.Adj (w i) (w j) → b i + b j ≤ 1 := by
        intro i j hij; dsimp only [b]
        by_cases hi : H.Adj u (w i) <;> by_cases hj : H.Adj u (w j)
        · exact (not_adj_of_cliqueFree_three hHTF hi hij hj).elim
        all_goals simp [hi, hj]
      have h01 := hna (show H.Adj (w 0) (w 1) from h11)
      have h12' := hna (show H.Adj (w 1) (w 2) from hz2y)
      have h23 := hna (show H.Adj (w 2) (w 3) from hz2x.symm)
      have h34 := hna (show H.Adj (w 3) (w 4) from h22)
      have h45 := hna (show H.Adj (w 4) (w 5) from hz1y)
      have h50 := hna (show H.Adj (w 5) (w 0) from hz1x.symm)
      have hcol_zero : ∀ {i : Fin 6}, col u = col (w i) → b i = 0 := by
        intro i hc; dsimp only [b]; rw [if_neg (fun h => hHcol u (w i) h hc)]
      have hcu : col u = c1 ∨ col u = c2 ∨ col u = c3' := by
        by_cases h1' : col u = c1
        · exact Or.inl h1'
        · by_cases h2' : col u = c2
          · exact Or.inr (Or.inl h2')
          · exact Or.inr (Or.inr (hc3_eq u h1' h2'))
      rcases hcu with hc | hc | hc
      · have : b 0 = 0 := hcol_zero (show col u = col x1 by rw [hc, hcx1])
        have : b 3 = 0 := hcol_zero (show col u = col x2 by rw [hc, hcx2])
        omega
      · have : b 1 = 0 := hcol_zero (show col u = col y1 by rw [hc, hcy1])
        have : b 4 = 0 := hcol_zero (show col u = col y2 by rw [hc, hcy2])
        omega
      · have : b 2 = 0 := hcol_zero (show col u = col z2 by rw [hc, hcz2])
        have : b 5 = 0 := hcol_zero (show col u = col z1 by rw [hc, hcz1])
        omega
    have hsum_le : ∑ i : Fin 6, #(Finset.univ.filter (H.Adj (w i))) ≤ 2 * n := by
      have hswap : ∑ i : Fin 6, #(Finset.univ.filter (H.Adj (w i))) =
          ∑ u : V, #(Finset.univ.filter (fun i : Fin 6 => H.Adj u (w i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro u _
        apply Finset.sum_congr rfl; intro i _; simp [H.adj_comm]
      rw [hswap]
      calc _ ≤ ∑ _u : V, 2 := Finset.sum_le_sum (fun u _ => hw_cap2 u)
        _ = 2 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_gt : 6 * n < 3 * ∑ i : Fin 6, #(Finset.univ.filter (H.Adj (w i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 6))) (by simp)
        (fun i _ => hH3d (w i))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
      omega
    omega
  -- Step 2: Total inclusion ordering + opposite monotonicity of neighborhoods on each color class
  have hnbhd_total : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x1) ⊆ (P c2).filter (H.Adj x2) ∨
      (P c2).filter (H.Adj x2) ⊆ (P c2).filter (H.Adj x1) := by
    intro c1 c2 hc12 x1 hx1 x2 hx2
    by_contra hnot; push Not at hnot
    obtain ⟨h1, h2⟩ := hnot
    obtain ⟨y1, hy1, hy1n⟩ := Finset.not_subset.mp h1
    obtain ⟨y2, hy2, hy2n⟩ := Finset.not_subset.mp h2
    have hy1' := Finset.mem_filter.mp hy1; have hy2' := Finset.mem_filter.mp hy2
    exact hno2K2 c1 c2 hc12 x1 hx1 x2 hx2 y1 hy1'.1 y2 hy2'.1 hy1'.2 hy2'.2
      (fun h => hy2n (Finset.mem_filter.mpr ⟨hy2'.1, h⟩))
      (fun h => hy1n (Finset.mem_filter.mpr ⟨hy1'.1, h⟩))
  have hnbhd_eq_iff : ∀ c1 c2 c3' : Fin 3, c1 ≠ c2 → c1 ≠ c3' → c2 ≠ c3' →
      ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x1) = (P c2).filter (H.Adj x2) →
      (P c3').filter (H.Adj x1) = (P c3').filter (H.Adj x2) := by
    intro c1 c2 c3' h12 h13 h23 x1 hx1 x2 hx2 heq
    have hsub : ∀ u ∈ P c1, ∀ v ∈ P c1, (P c2).filter (H.Adj u) = (P c2).filter (H.Adj v) →
        (P c3').filter (H.Adj u) ⊆ (P c3').filter (H.Adj v) := by
      intro u hu v hv huv z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr; refine ⟨hz'.1, ?_⟩
      by_contra hna
      have hcv : col v = c1 := (Finset.mem_filter.mp hv).2
      have hcz : col z = c3' := (Finset.mem_filter.mp hz'.1).2
      obtain ⟨y, hyv, hyz⟩ := hHmax v z (by rw [hcv, hcz]; exact h13) hna
      have hcy : col y = c2 :=
        fin3_third h13 h12 h23.symm (by rw [← hcv]; exact (hHcol v y hyv).symm)
          (by rw [← hcz]; exact (hHcol z y hyz).symm)
      have hy_in : y ∈ (P c2).filter (H.Adj v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcy⟩, hyv⟩
      rw [← huv] at hy_in
      exact not_adj_of_cliqueFree_three hHTF (Finset.mem_filter.mp hy_in).2 hyz.symm hz'.2
    exact Finset.Subset.antisymm (hsub x1 hx1 x2 hx2 heq) (hsub x2 hx2 x1 hx1 heq.symm)
  have hnbhd_opp : ∀ c1 c2 c3' : Fin 3, c1 ≠ c2 → c1 ≠ c3' → c2 ≠ c3' →
      ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x2) ⊂ (P c2).filter (H.Adj x1) →
      (P c3').filter (H.Adj x1) ⊂ (P c3').filter (H.Adj x2) := by
    intro c1 c2 c3' h12 h13 h23 x1 hx1 x2 hx2 hssub
    have hsub3 : (P c3').filter (H.Adj x1) ⊆ (P c3').filter (H.Adj x2) := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr; refine ⟨hz'.1, ?_⟩
      by_contra hna
      obtain ⟨y, hy1, hy2⟩ := Finset.exists_of_ssubset hssub
      have hy1' := Finset.mem_filter.mp hy1
      have hna_y : ¬ H.Adj x2 y := fun h => hy2 (Finset.mem_filter.mpr ⟨hy1'.1, h⟩)
      have hcx2 : col x2 = c1 := (Finset.mem_filter.mp hx2).2
      have hcy : col y = c2 := (Finset.mem_filter.mp hy1'.1).2
      obtain ⟨z', hz'x2, hz'y⟩ := hHmax x2 y (by rw [hcx2, hcy]; exact h12) hna_y
      have hcz' : col z' = c3' :=
        fin3_third h12 h13 h23 (by rw [← hcx2]; exact (hHcol x2 z' hz'x2).symm)
          (by rw [← hcy]; exact (hHcol y z' hz'y).symm)
      have hna_z' : ¬ H.Adj x1 z' := fun h => not_adj_of_cliqueFree_three hHTF hy1'.2 hz'y h
      exact hno2K2 c1 c3' h13 x1 hx1 x2 hx2 z hz'.1 z' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcz'⟩)
        hz'.2 hz'x2 hna_z' hna
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub3, fun heq => ?_⟩
    exact (Finset.ssubset_iff_subset_ne.mp hssub).2 (hnbhd_eq_iff c1 c3' c2 h13 h12 h23.symm x1 hx1 x2 hx2 heq).symm
  -- Step 3: Build decreasing-degree representatives for each color class c -> next color (c + 1)
  let degNext : Fin 3 → V → ℕ := fun c x => #((P (c + 1)).filter (H.Adj x))
  let degSet : Fin 3 → Finset ℕ := fun c => (P c).image (degNext c)
  let sz : Fin 3 → ℕ := fun c => #(degSet c)
  have hsz_pos : ∀ c : Fin 3, 1 ≤ sz c := fun c =>
    Finset.card_pos.mpr ((hP_ne c).image _)
  -- Decreasing enumeration of degSet c via orderIsoOfFin
  let degVal : (c : Fin 3) → Fin (sz c) → ℕ := fun c i =>
    (Finset.orderIsoOfFin (degSet c) rfl ⟨sz c - 1 - i.val, by change sz c - 1 - i.val < sz c; have := i.isLt; omega⟩).val
  have hdegVal_mem : ∀ (c : Fin 3) (i : Fin (sz c)), degVal c i ∈ degSet c := fun c i =>
    (Finset.orderIsoOfFin (degSet c) rfl ⟨sz c - 1 - i.val, by change sz c - 1 - i.val < sz c; have := i.isLt; omega⟩).property
  have hdegVal_strict : ∀ (c : Fin 3) (i j : Fin (sz c)), i < j → degVal c j < degVal c i := by
    intro c i j hij
    have hi := i.isLt; have hj := j.isLt; have hlt' := Fin.lt_def.mp hij
    have hlt : (⟨sz c - 1 - j.val, by omega⟩ : Fin (sz c)) < ⟨sz c - 1 - i.val, by omega⟩ :=
      Fin.lt_def.mpr (by dsimp only; omega)
    exact (Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).strictMono hlt
  have hex_rep : ∀ (c : Fin 3) (i : Fin (sz c)), ∃ x ∈ P c, degNext c x = degVal c i :=
    fun c i => Finset.mem_image.mp (hdegVal_mem c i)
  let rep : (c : Fin 3) → Fin (sz c) → V := fun c i => (hex_rep c i).choose
  have hrep_mem : ∀ (c : Fin 3) (i : Fin (sz c)), rep c i ∈ P c := fun c i => (hex_rep c i).choose_spec.1
  have hrep_deg : ∀ (c : Fin 3) (i : Fin (sz c)), degNext c (rep c i) = degVal c i :=
    fun c i => (hex_rep c i).choose_spec.2
  -- Every x ∈ P c is a full twin of rep c (idx c x)
  have hex_idx : ∀ (c : Fin 3) (x : V), x ∈ P c → ∃ i : Fin (sz c), degNext c x = degVal c i := by
    intro c x hx
    have hmem : degNext c x ∈ degSet c := Finset.mem_image_of_mem _ hx
    let j : Fin (sz c) := (Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).symm ⟨degNext c x, hmem⟩
    have hj := j.isLt
    refine ⟨⟨sz c - 1 - j.val, by omega⟩, ?_⟩
    dsimp only [degVal]
    have hsub : (⟨sz c - 1 - (sz c - 1 - j.val), by omega⟩ : Fin (sz c)) = j := Fin.ext (by dsimp only; omega)
    rw [hsub]
    exact (congrArg Subtype.val ((Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).apply_symm_apply ⟨degNext c x, hmem⟩)).symm
  let idx : (c : Fin 3) → (x : V) → x ∈ P c → Fin (sz c) := fun c x hx => (hex_idx c x hx).choose
  have hidx_deg : ∀ (c : Fin 3) (x : V) (hx : x ∈ P c), degNext c x = degNext c (rep c (idx c x hx)) := by
    intro c x hx; rw [hrep_deg]; exact (hex_idx c x hx).choose_spec
  have hsame_deg_twin : ∀ (c : Fin 3) (x1 x2 : V), x1 ∈ P c → x2 ∈ P c →
      degNext c x1 = degNext c x2 → ∀ w : V, H.Adj x1 w ↔ H.Adj x2 w := by
    intro c x1 x2 hx1 hx2 hdeq w
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hne2 : c ≠ c + 2 := by fin_cases c <;> decide
    have hne12 : c + 1 ≠ c + 2 := by fin_cases c <;> decide
    have hN1 : (P (c + 1)).filter (H.Adj x1) = (P (c + 1)).filter (H.Adj x2) := by
      rcases hnbhd_total c (c + 1) hne1 x1 hx1 x2 hx2 with hsub | hsub
      · exact Finset.eq_of_subset_of_card_le hsub (by dsimp only [degNext] at hdeq; omega)
      · exact (Finset.eq_of_subset_of_card_le hsub (by dsimp only [degNext] at hdeq; omega)).symm
    have hN2 : (P (c + 2)).filter (H.Adj x1) = (P (c + 2)).filter (H.Adj x2) :=
      hnbhd_eq_iff c (c + 1) (c + 2) hne1 hne2 hne12 x1 hx1 x2 hx2 hN1
    have hcw : col w = c ∨ col w = c + 1 ∨ col w = c + 2 := by
      generalize col w = cw; fin_cases c <;> fin_cases cw <;> simp
    rcases hcw with hc | hc | hc
    · have h1 : ¬ H.Adj x1 w := fun h => hHcol x1 w h ((Finset.mem_filter.mp hx1).2.trans hc.symm)
      have h2 : ¬ H.Adj x2 w := fun h => hHcol x2 w h ((Finset.mem_filter.mp hx2).2.trans hc.symm)
      exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
    · have hwP : w ∈ P (c + 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hiff := Finset.ext_iff.mp hN1 w
      simp only [Finset.mem_filter, hwP, true_and] at hiff; exact hiff
    · have hwP : w ∈ P (c + 2) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hiff := Finset.ext_iff.mp hN2 w
      simp only [Finset.mem_filter, hwP, true_and] at hiff; exact hiff
  -- Monotonicity of adjacency on representatives!
  have hrep_adj_mono : ∀ (c : Fin 3) (i₁ i₂ : Fin (sz c)), i₁ < i₂ →
      ∀ (j : Fin (sz (c + 1))), H.Adj (rep c i₂) (rep (c + 1) j) → H.Adj (rep c i₁) (rep (c + 1) j) := by
    intro c i₁ i₂ hlt j hadj
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hdlt : degNext c (rep c i₂) < degNext c (rep c i₁) := by
      rw [hrep_deg, hrep_deg]; exact hdegVal_strict c i₁ i₂ hlt
    have hsub : (P (c + 1)).filter (H.Adj (rep c i₂)) ⊆ (P (c + 1)).filter (H.Adj (rep c i₁)) := by
      rcases hnbhd_total c (c + 1) hne1 (rep c i₁) (hrep_mem c i₁) (rep c i₂) (hrep_mem c i₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; omega
      · exact h
    exact (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hrep_mem (c + 1) j, hadj⟩))).2
  have hrep_adj_mono_right : ∀ (c : Fin 3) (j₁ j₂ : Fin (sz (c + 1))), j₁ < j₂ →
      ∀ (i : Fin (sz c)), H.Adj (rep c i) (rep (c + 1) j₁) → H.Adj (rep c i) (rep (c + 1) j₂) := by
    intro c j₁ j₂ hlt i hadj
    have hne1 : c + 1 ≠ c + 2 := by fin_cases c <;> decide
    have hne2 : c + 1 ≠ c := by fin_cases c <;> decide
    have hne3 : c + 2 ≠ c := by fin_cases c <;> decide
    have hdlt : degNext (c + 1) (rep (c + 1) j₂) < degNext (c + 1) (rep (c + 1) j₁) := by
      rw [hrep_deg, hrep_deg]; exact hdegVal_strict (c + 1) j₁ j₂ hlt
    have hssub : (P (c + 2)).filter (H.Adj (rep (c + 1) j₂)) ⊂ (P (c + 2)).filter (H.Adj (rep (c + 1) j₁)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, fun heq => by have := congrArg Finset.card heq; dsimp only [degNext] at hdlt; rw [show c + 1 + 1 = c + 2 by fin_cases c <;> decide] at hdlt; omega⟩
      rcases hnbhd_total (c + 1) (c + 2) hne1 (rep (c + 1) j₁) (hrep_mem _ j₁) (rep (c + 1) j₂) (hrep_mem _ j₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; rw [show c + 1 + 1 = c + 2 by fin_cases c <;> decide] at hdlt; omega
      · exact h
    have hopp := hnbhd_opp (c + 1) (c + 2) c hne1 hne2 hne3 (rep (c + 1) j₁) (hrep_mem _ j₁)
      (rep (c + 1) j₂) (hrep_mem _ j₂) hssub
    exact (Finset.mem_filter.mp (hopp.1 (Finset.mem_filter.mpr ⟨hrep_mem c i, hadj.symm⟩))).2.symm
  -- Threshold function thr c i := sz (c + 1) - #{j | rep c i ~ rep (c + 1) j}
  let thr : (c : Fin 3) → Fin (sz c) → ℕ := fun c i =>
    sz (c + 1) - #(Finset.univ.filter (fun j : Fin (sz (c + 1)) => H.Adj (rep c i) (rep (c + 1) j)))
  have hthr_iff : ∀ (c : Fin 3) (i : Fin (sz c)) (j : Fin (sz (c + 1))),
      H.Adj (rep c i) (rep (c + 1) j) ↔ thr c i ≤ j.val := by
    intro c i j
    set S := Finset.univ.filter (fun j' : Fin (sz (c + 1)) => H.Adj (rep c i) (rep (c + 1) j'))
    have hS_up : ∀ j₁ j₂ : Fin (sz (c + 1)), j₁ ∈ S → j₁ ≤ j₂ → j₂ ∈ S := by
      intro j₁ j₂ hj1 hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hj1
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrep_adj_mono_right c j₁ j₂ hlt i (Finset.mem_filter.mp hj1).2⟩
    have hS_eq : S = Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val) := by
      have hcard_R : #(Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val)) = #S := by
        have hS_le : #S ≤ sz (c + 1) := by
          calc #S ≤ #(Finset.univ : Finset (Fin (sz (c + 1)))) := Finset.card_le_card (Finset.filter_subset _ _)
            _ = sz (c + 1) := by simp
        refine (Finset.card_bij (fun (j' : Fin (sz (c + 1))) _ => j'.val - (sz (c + 1) - #S)) ?_ ?_ ?_).trans (Finset.card_range #S)
        · intro j' hj'; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj').2; omega)
        · intro j₁ hj₁ j₂ hj₂ heq
          have := (Finset.mem_filter.mp hj₁).2; have := (Finset.mem_filter.mp hj₂).2; exact Fin.ext (by omega)
        · intro m hm; have hm' := Finset.mem_range.mp hm
          exact ⟨⟨sz (c + 1) - #S + m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
      by_cases hsub : S ⊆ Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val)
      · exact Finset.eq_of_subset_of_card_le hsub (by omega)
      · exfalso
        obtain ⟨j₀, hj₀S, hj₀not⟩ := Finset.not_subset.mp hsub
        have hj₀_lt : j₀.val < sz (c + 1) - #S := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀not; omega
        have hge : Finset.univ.filter (fun j' : Fin (sz (c + 1)) => j₀.val ≤ j'.val) ⊆ S :=
          fun j' hj' => hS_up j₀ j' hj₀S (Fin.le_def.mpr (Finset.mem_filter.mp hj').2)
        have hcard_ge : #(Finset.univ.filter (fun j' : Fin (sz (c + 1)) => j₀.val ≤ j'.val)) = sz (c + 1) - j₀.val := by
          refine (Finset.card_bij (fun (j' : Fin (sz (c + 1))) _ => j'.val - j₀.val) ?_ ?_ ?_).trans (Finset.card_range (sz (c + 1) - j₀.val))
          · intro j' hj'; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj').2; omega)
          · intro j₁ hj₁ j₂ hj₂ heq; have := (Finset.mem_filter.mp hj₁).2; have := (Finset.mem_filter.mp hj₂).2; exact Fin.ext (by omega)
          · intro m hm; have hm' := Finset.mem_range.mp hm
            exact ⟨⟨j₀.val + m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
        have := Finset.card_le_card hge; omega
    have hmem := Finset.ext_iff.mp hS_eq j
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem
  have hthr_le : ∀ (c : Fin 3) (i : Fin (sz c)), thr c i ≤ sz (c + 1) := fun _ _ => Nat.sub_le _ _
  have hthr_sm : ∀ (c : Fin 3) (i₁ i₂ : Fin (sz c)), i₁ < i₂ → thr c i₁ < thr c i₂ := by
    intro c i₁ i₂ hlt
    have hdlt : degNext c (rep c i₂) < degNext c (rep c i₁) := by
      rw [hrep_deg, hrep_deg]; exact hdegVal_strict c i₁ i₂ hlt
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hssub : (P (c + 1)).filter (H.Adj (rep c i₂)) ⊂ (P (c + 1)).filter (H.Adj (rep c i₁)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, fun heq => by have := congrArg Finset.card heq; dsimp only [degNext] at hdlt; omega⟩
      rcases hnbhd_total c (c + 1) hne1 (rep c i₁) (hrep_mem c i₁) (rep c i₂) (hrep_mem c i₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; omega
      · exact h
    obtain ⟨y, hy1, hy2⟩ := Finset.exists_of_ssubset hssub
    have hy1' := Finset.mem_filter.mp hy1
    let j := idx (c + 1) y hy1'.1
    have htwin := hsame_deg_twin (c + 1) y (rep (c + 1) j) hy1'.1 (hrep_mem _ j) (hidx_deg _ y hy1'.1)
    have hadj1 : H.Adj (rep c i₁) (rep (c + 1) j) := ((htwin (rep c i₁)).mp hy1'.2.symm).symm
    have hna2 : ¬ H.Adj (rep c i₂) (rep (c + 1) j) := fun h =>
      hy2 (Finset.mem_filter.mpr ⟨hy1'.1, ((htwin (rep c i₂)).mpr h.symm).symm⟩)
    rw [hthr_iff] at hadj1 hna2; omega
  -- Helper: lift any valid quotient homomorphism (φ0, φ1, φ2) to H : SimpleGraph V!
  have hlift : ∀ (d : ℕ) (hd : 1 ≤ d)
      (φ0 : Fin (sz 0) → Fin (3 * d - 1)) (φ1 : Fin (sz 1) → Fin (3 * d - 1))
      (φ2 : Fin (sz 2) → Fin (3 * d - 1)),
      (∀ i j, thr 0 i ≤ j.val →
        d ≤ ((φ1 j).val + (3 * d - 1) - (φ0 i).val) % (3 * d - 1) ∧
        ((φ1 j).val + (3 * d - 1) - (φ0 i).val) % (3 * d - 1) < 2 * d) →
      (∀ j k, thr 1 j ≤ k.val →
        d ≤ ((φ2 k).val + (3 * d - 1) - (φ1 j).val) % (3 * d - 1) ∧
        ((φ2 k).val + (3 * d - 1) - (φ1 j).val) % (3 * d - 1) < 2 * d) →
      (∀ k i, thr 2 k ≤ i.val →
        d ≤ ((φ0 i).val + (3 * d - 1) - (φ2 k).val) % (3 * d - 1) ∧
        ((φ0 i).val + (3 * d - 1) - (φ2 k).val) % (3 * d - 1) < 2 * d) →
      ∃ (d' : ℕ) (_ : 1 ≤ d') (φ : V → Fin (3 * d' - 1)),
        ∀ u v : V, H.Adj u v →
          d' ≤ ((φ v).val + (3 * d' - 1) - (φ u).val) % (3 * d' - 1) ∧
          ((φ v).val + (3 * d' - 1) - (φ u).val) % (3 * d' - 1) < 2 * d' := by
    intro d hd φ0 φ1 φ2 h01 h12 h20
    have hsym_mod : ∀ a b : Fin (3 * d - 1),
        (d ≤ (b.val + (3 * d - 1) - a.val) % (3 * d - 1) ∧ (b.val + (3 * d - 1) - a.val) % (3 * d - 1) < 2 * d) →
        (d ≤ (a.val + (3 * d - 1) - b.val) % (3 * d - 1) ∧ (a.val + (3 * d - 1) - b.val) % (3 * d - 1) < 2 * d) := by
      intro a b ⟨hlo, hhi⟩
      have ha := a.isLt; have hb := b.isLt
      by_cases hle : a.val ≤ b.val
      · have h1 : (b.val + (3 * d - 1) - a.val) % (3 * d - 1) = b.val - a.val := by
          rw [show b.val + (3 * d - 1) - a.val = (b.val - a.val) + (3 * d - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (a.val + (3 * d - 1) - b.val) % (3 * d - 1) = (3 * d - 1) - (b.val - a.val) := by
          rw [show a.val + (3 * d - 1) - b.val = (3 * d - 1) - (b.val - a.val) by omega, Nat.mod_eq_of_lt (by omega)]
        omega
      · have h1 : (b.val + (3 * d - 1) - a.val) % (3 * d - 1) = b.val + (3 * d - 1) - a.val := Nat.mod_eq_of_lt (by omega)
        have h2 : (a.val + (3 * d - 1) - b.val) % (3 * d - 1) = a.val - b.val := by
          rw [show a.val + (3 * d - 1) - b.val = (a.val - b.val) + (3 * d - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    let φ : V → Fin (3 * d - 1) := fun v =>
      if h0 : v ∈ P 0 then φ0 (idx 0 v h0)
      else if h1 : v ∈ P 1 then φ1 (idx 1 v h1)
      else if h2 : v ∈ P 2 then φ2 (idx 2 v h2)
      else ⟨0, by omega⟩
    refine ⟨d, hd, φ, ?_⟩
    intro u v huv
    have hmem_col : ∀ w : V, w ∈ P (col w) := fun w => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hnot_mem : ∀ w : V, ∀ c : Fin 3, col w ≠ c → w ∉ P c := fun w c hne hmem => hne (Finset.mem_filter.mp hmem).2
    have hrep_adj : ∀ c1 c2 : Fin 3, ∀ hu : u ∈ P c1, ∀ hv : v ∈ P c2,
        H.Adj (rep c1 (idx c1 u hu)) (rep c2 (idx c2 v hv)) := by
      intro c1 c2 hu hv
      have h1 := (hsame_deg_twin c1 u (rep c1 (idx c1 u hu)) hu (hrep_mem c1 _) (hidx_deg c1 u hu) v).mp huv
      exact (hsame_deg_twin c2 v (rep c2 (idx c2 v hv)) hv (hrep_mem c2 _) (hidx_deg c2 v hv) _).mp h1.symm |>.symm
    have hne := hHcol u v huv
    have hcu : col u = 0 ∨ col u = 1 ∨ col u = 2 := by generalize col u = cu; fin_cases cu <;> simp
    have hcv : col v = 0 ∨ col v = 1 ∨ col v = 2 := by generalize col v = cv; fin_cases cv <;> simp
    rcases hcu with hu | hu | hu <;> rcases hcv with hv | hv | hv
    · exact (hne (hu.trans hv.symm)).elim
    · have hu0 : u ∈ P 0 := hu ▸ hmem_col u; have hv1 : v ∈ P 1 := hv ▸ hmem_col v
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      simp only [φ, hu0, hv0, hv1, dite_true, dite_false]
      exact h01 _ _ ((hthr_iff 0 _ _).mp (hrep_adj 0 1 hu0 hv1))
    · have hu0 : u ∈ P 0 := hu ▸ hmem_col u; have hv2 : v ∈ P 2 := hv ▸ hmem_col v
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      have hv1 : v ∉ P 1 := hnot_mem v 1 (by rw [hv]; decide)
      simp only [φ, hu0, hv0, hv1, hv2, dite_true, dite_false]
      exact hsym_mod _ _ (h20 _ _ ((hthr_iff 2 _ _).mp (hrep_adj 0 2 hu0 hv2).symm))
    · have hu1 : u ∈ P 1 := hu ▸ hmem_col u; have hv0 : v ∈ P 0 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      simp only [φ, hu0, hu1, hv0, dite_true, dite_false]
      exact hsym_mod _ _ (h01 _ _ ((hthr_iff 0 _ _).mp (hrep_adj 1 0 hu1 hv0).symm))
    · exact (hne (hu.trans hv.symm)).elim
    · have hu1 : u ∈ P 1 := hu ▸ hmem_col u; have hv2 : v ∈ P 2 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      have hv1 : v ∉ P 1 := hnot_mem v 1 (by rw [hv]; decide)
      simp only [φ, hu0, hu1, hv0, hv1, hv2, dite_true, dite_false]
      exact h12 _ _ ((hthr_iff 1 _ _).mp (hrep_adj 1 2 hu1 hv2))
    · have hu2 : u ∈ P 2 := hu ▸ hmem_col u; have hv0 : v ∈ P 0 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      have hu1 : u ∉ P 1 := hnot_mem u 1 (by rw [hu]; decide)
      simp only [φ, hu0, hu1, hu2, hv0, dite_true, dite_false]
      exact h20 _ _ ((hthr_iff 2 _ _).mp (hrep_adj 2 0 hu2 hv0))
    · have hu2 : u ∈ P 2 := hu ▸ hmem_col u; have hv1 : v ∈ P 1 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      have hu1 : u ∉ P 1 := hnot_mem u 1 (by rw [hu]; decide)
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      simp only [φ, hu0, hu1, hu2, hv0, hv1, dite_true, dite_false]
      exact hsym_mod _ _ (h12 _ _ ((hthr_iff 1 _ _).mp (hrep_adj 2 1 hu2 hv1).symm))
    · exact (hne (hu.trans hv.symm)).elim
  -- Step 4: Verify quotient axioms and apply S_3 symmetry to invoke cjk_quotient_ordered!
  have hQ_TF : ∀ (i : Fin (sz 0)) (j : Fin (sz 1)) (k : Fin (sz 2)),
      ¬ (thr 0 i ≤ j.val ∧ thr 1 j ≤ k.val ∧ thr 2 k ≤ i.val) := by
    intro i j k ⟨h1, h2, h3⟩
    exact not_adj_of_cliqueFree_three hHTF ((hthr_iff 0 i j).mpr h1) ((hthr_iff 1 j k).mpr h2)
      ((hthr_iff 2 k i).mpr h3).symm
  have hQ_max01 : ∀ (i : Fin (sz 0)) (j : Fin (sz 1)),
      j.val < thr 0 i → ∃ k : Fin (sz 2), thr 1 j ≤ k.val ∧ thr 2 k ≤ i.val := by
    intro i j hlt
    have hna : ¬ H.Adj (rep 0 i) (rep 1 j) := by rw [hthr_iff 0 i j]; omega
    have hne : col (rep 0 i) ≠ col (rep 1 j) := by
      rw [(Finset.mem_filter.mp (hrep_mem 0 i)).2, (Finset.mem_filter.mp (hrep_mem 1 j)).2]; decide
    obtain ⟨w, hwi, hwj⟩ := hHmax _ _ hne hna
    have hcw : col w = 2 := fin3_third (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
      (by decide : (1 : Fin 3) ≠ 2)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 0 i)).2]; exact (hHcol _ w hwi).symm)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 1 j)).2]; exact (hHcol _ w hwj).symm)
    have hwP : w ∈ P 2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw⟩
    let k := idx 2 w hwP
    have htwin := hsame_deg_twin 2 w (rep 2 k) hwP (hrep_mem 2 k) (hidx_deg 2 w hwP)
    exact ⟨k, (hthr_iff 1 j k).mp ((htwin _).mp hwj.symm).symm, (hthr_iff 2 k i).mp ((htwin _).mp hwi.symm)⟩
  have hQ_max12 : ∀ (j : Fin (sz 1)) (k : Fin (sz 2)),
      k.val < thr 1 j → ∃ i : Fin (sz 0), thr 0 i ≤ j.val ∧ thr 2 k ≤ i.val := by
    intro j k hlt
    have hna : ¬ H.Adj (rep 1 j) (rep 2 k) := by rw [hthr_iff 1 j k]; omega
    have hne : col (rep 1 j) ≠ col (rep 2 k) := by
      rw [(Finset.mem_filter.mp (hrep_mem 1 j)).2, (Finset.mem_filter.mp (hrep_mem 2 k)).2]; decide
    obtain ⟨w, hwj, hwk⟩ := hHmax _ _ hne hna
    have hcw : col w = 0 := fin3_third (by decide : (1 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 0)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 1 j)).2]; exact (hHcol _ w hwj).symm)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 2 k)).2]; exact (hHcol _ w hwk).symm)
    have hwP : w ∈ P 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw⟩
    let i := idx 0 w hwP
    have htwin := hsame_deg_twin 0 w (rep 0 i) hwP (hrep_mem 0 i) (hidx_deg 0 w hwP)
    exact ⟨i, (hthr_iff 0 i j).mp ((htwin _).mp hwj.symm), (hthr_iff 2 k i).mp ((htwin _).mp hwk.symm).symm⟩
  have hQ_max20 : ∀ (k : Fin (sz 2)) (i : Fin (sz 0)),
      i.val < thr 2 k → ∃ j : Fin (sz 1), thr 0 i ≤ j.val ∧ thr 1 j ≤ k.val := by
    intro k i hlt
    have hna : ¬ H.Adj (rep 2 k) (rep 0 i) := by rw [hthr_iff 2 k i]; omega
    have hne : col (rep 2 k) ≠ col (rep 0 i) := by
      rw [(Finset.mem_filter.mp (hrep_mem 2 k)).2, (Finset.mem_filter.mp (hrep_mem 0 i)).2]; decide
    obtain ⟨w, hwk, hwi⟩ := hHmax _ _ hne hna
    have hcw : col w = 1 := fin3_third (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 1)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 2 k)).2]; exact (hHcol _ w hwk).symm)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 0 i)).2]; exact (hHcol _ w hwi).symm)
    have hwP : w ∈ P 1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw⟩
    let j := idx 1 w hwP
    have htwin := hsame_deg_twin 1 w (rep 1 j) hwP (hrep_mem 1 j) (hidx_deg 1 w hwP)
    exact ⟨j, (hthr_iff 0 i j).mp ((htwin _).mp hwi.symm).symm, (hthr_iff 1 j k).mp ((htwin _).mp hwk.symm)⟩
  obtain ⟨d, hd, φ0, φ1, φ2, h01, h12, h20⟩ := cjk_quotient_S3 (hsz_pos 0) (hsz_pos 1) (hsz_pos 2)
    (thr 0) (thr 1) (thr 2) (hthr_le 0) (hthr_le 1) (hthr_le 2)
    (hthr_sm 0) (hthr_sm 1) (hthr_sm 2) hQ_TF hQ_max01 hQ_max12 hQ_max20
  exact hlift d hd φ0 φ1 φ2 h01 h12 h20


/-- Theorem G: Every counterexample with 3 * δ(G) > n is non-3-colorable (χ(G) >= 4). -/
theorem not_colorable_three_of_gt_third {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (h3d : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) :
    ¬ G.Colorable 3 := fun h3col => by
  obtain ⟨d, hd, φ, hφ⟩ := chen_jin_koh_hom_andrasfai G hTF h3col h3d
  exact not_hom_andrasfai G hH (fun H hHTF hHH => five_mul_edges_lt_sq H hHTF hHH) d hd φ hφ

/-- Finite helper: inside a 4-window {i, i+1, i+2, i+3} of And(3), the only edges connect i and i+3. -/
lemma v8_window_edge (i a b : Fin 8)
    (ha : a = i ∨ a = i + 1 ∨ a = i + 2 ∨ a = i + 3)
    (hb : b = i ∨ b = i + 1 ∨ b = i + 2 ∨ b = i + 3)
    (hab : b = a + 3 ∨ b = a + 4 ∨ b = a + 5) :
    (a = i ∧ b = i + 3) ∨ (a = i + 3 ∧ b = i) := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all

/-- Finite helper: every non-edge (c1, c2) of Möbius V_8 omits a full neighborhood N_{V_8}(r). -/
lemma v8_nonedge_omits_nbhd (c1 c2 : Fin 8)
    (hnot : ¬ (c2 = c1 + 1 ∨ c2 = c1 + 4 ∨ c2 = c1 + 7)) :
    ∃ r : Fin 8, ∀ j : Fin 8, (j = r + 1 ∨ j = r + 4 ∨ j = r + 7) →
      ¬ (j = c1 + 1 ∨ j = c1 + 4 ∨ j = c1 + 7) ∧
      ¬ (j = c2 + 1 ∨ j = c2 + 4 ∨ j = c2 + 7) := by
  fin_cases c1 <;> fin_cases c2
  all_goals first
    | (exfalso; apply hnot; decide)
    | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩ | exact ⟨3, by decide⟩
    | exact ⟨4, by decide⟩ | exact ⟨5, by decide⟩ | exact ⟨6, by decide⟩ | exact ⟨7, by decide⟩

/-- Finite helper: every independent set of Möbius V_8 is contained in some neighborhood N_{V_8}(c). -/
lemma v8_indep_subset_nbhd (J : Finset (Fin 8))
    (hJ_indep : ∀ i ∈ J, ∀ j ∈ J, ¬ (j = i + 1 ∨ j = i + 4 ∨ j = i + 7)) :
    ∃ c : Fin 8, ∀ j ∈ J, j = c + 1 ∨ j = c + 4 ∨ j = c + 7 := by
  by_contra hall
  push Not at hall
  let b : Fin 8 → ℕ := fun i => if i ∈ J then 1 else 0
  have hna : ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) → b i + b j ≤ 1 := by
    intro i j hij; dsimp only [b]
    by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
    · exact (hJ_indep i hi j hj hij).elim
    all_goals simp [hi, hj]
  have hnot_cov : ∀ c : Fin 8, b c + b (c + 2) + b (c + 3) + b (c + 5) + b (c + 6) ≥ 1 := by
    intro c
    obtain ⟨j, hjJ, hjnot⟩ := hall c
    have hj_in : j = c ∨ j = c + 2 ∨ j = c + 3 ∨ j = c + 5 ∨ j = c + 6 := by
      fin_cases c <;> fin_cases j <;> simp at hjnot ⊢
    have hbj : b j = 1 := by dsimp only [b]; simp [hjJ]
    rcases hj_in with rfl | rfl | rfl | rfl | rfl <;> omega
  have hc0 : b 0 + b 2 + b 3 + b 5 + b 6 ≥ 1 := hnot_cov 0
  have hc1 : b 1 + b 3 + b 4 + b 6 + b 7 ≥ 1 := hnot_cov 1
  have hc2 : b 2 + b 4 + b 5 + b 7 + b 0 ≥ 1 := hnot_cov 2
  have hc3 : b 3 + b 5 + b 6 + b 0 + b 1 ≥ 1 := hnot_cov 3
  have hc4 : b 4 + b 6 + b 7 + b 1 + b 2 ≥ 1 := hnot_cov 4
  have hc5 : b 5 + b 7 + b 0 + b 2 + b 3 ≥ 1 := hnot_cov 5
  have hc6 : b 6 + b 0 + b 1 + b 3 + b 4 ≥ 1 := hnot_cov 6
  have hc7 : b 7 + b 1 + b 2 + b 4 + b 5 ≥ 1 := hnot_cov 7
  have := hna 0 1 (by decide); have := hna 1 2 (by decide); have := hna 2 3 (by decide)
  have := hna 3 4 (by decide); have := hna 4 5 (by decide); have := hna 5 6 (by decide)
  have := hna 6 7 (by decide); have := hna 7 0 (by decide)
  have := hna 0 4 (by decide); have := hna 1 5 (by decide)
  have := hna 2 6 (by decide); have := hna 3 7 (by decide)
  have hle1 : ∀ i : Fin 8, b i ≤ 1 := fun i => by dsimp only [b]; split_ifs <;> omega
  have := hle1 0; have := hle1 1; have := hle1 2; have := hle1 3
  have := hle1 4; have := hle1 5; have := hle1 6; have := hle1 7
  omega


/-- Step 1: Every triangle-free graph on a finite vertex set extends to a maximal
    triangle-free supergraph (in which every non-adjacent distinct pair has a common neighbor). -/
lemma exists_maximal_triangleFree {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
      ∀ u v : V, u ≠ v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w := by
  classical
  suffices h : ∀ m : ℕ, ∀ G : SimpleGraph V, G.CliqueFree 3 →
      Fintype.card (Sym2 V) - #G.edgeFinset ≤ m →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
        ∀ u v : V, u ≠ v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w from
    h (Fintype.card (Sym2 V) - #G.edgeFinset) G hTF (le_refl _)
  intro m
  induction m with
  | zero =>
    intro G hTF hm
    refine ⟨G, le_refl _, hTF, ?_⟩
    intro u v huv hna
    exfalso
    have hcard : #G.edgeFinset ≤ Fintype.card (Sym2 V) := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have heq : G.edgeFinset = Finset.univ := Finset.eq_univ_of_card _ (by omega)
    have hmem : s(u, v) ∈ G.edgeFinset := by rw [heq]; exact Finset.mem_univ _
    exact hna (SimpleGraph.mem_edgeFinset.mp hmem)
  | succ m ih =>
    intro G hTF hm
    by_cases hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w
    · exact ⟨G, le_refl _, hTF, hmax⟩
    · push Not at hmax
      obtain ⟨u, v, huv, hna, hno_cn⟩ := hmax
      let G' : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
      have hGG' : G ≤ G' := le_sup_left
      have hG'_adj : ∀ a b : V, G'.Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        intro a b
        simp only [G', SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        constructor
        · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩
      have hG'_TF : G'.CliqueFree 3 := by
        intro s hs
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
        have h1 : G'.Adj a b := hs.1 (by simp) (by simp) hab
        have h2 : G'.Adj b c := hs.1 (by simp) (by simp) hbc
        have h3 : G'.Adj a c := hs.1 (by simp) (by simp) hac
        rw [hG'_adj] at h1 h2 h3
        by_cases g1 : G.Adj a b
        · by_cases g2 : G.Adj b c
          · by_cases g3 : G.Adj a c
            · exact not_adj_of_cliqueFree_three hTF g1 g2 g3
            · rcases h3 with h3 | ⟨ha, hc⟩ | ⟨ha, hc⟩
              · exact g3 h3
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g1 g2.symm
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g2.symm g1
          · rcases h2 with h2 | ⟨hb, hc⟩ | ⟨hb, hc⟩
            · exact g2 h2
            · rcases h3 with g3 | ⟨ha, _⟩ | ⟨_, hcu⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g1.symm g3.symm
              · exact hab (ha.trans hb.symm)
              · exact huv (hcu.symm.trans hc)
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨ha, _⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g3.symm g1.symm
              · exact huv (hc.symm.trans hcv)
              · exact hab (ha.trans hb.symm)
        · rcases h1 with h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact g1 h1
          · rcases h2 with g2 | ⟨hbu, _⟩ | ⟨_, hcu⟩
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨hau, _⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g3 g2
              · exact hbc (hb.trans hcv.symm)
              · exact huv (ha.symm.trans hau)
            · exact huv (hb.symm.trans hbu).symm
            · exact hac (ha.trans hcu.symm)
          · rcases h2 with g2 | ⟨_, hcv⟩ | ⟨hbv, _⟩
            · rcases h3 with g3 | ⟨hau, _⟩ | ⟨_, hcu⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g2 g3
              · exact huv (hau.symm.trans ha)
              · exact hbc (hb.trans hcu.symm)
            · exact hac (ha.trans hcv.symm)
            · exact huv (hb.symm.trans hbv)
      have hstrict : #G.edgeFinset < #G'.edgeFinset := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro e he
          exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hGG' (SimpleGraph.mem_edgeFinset.mp he))
        · intro heq
          have hmem : s(u, v) ∈ G'.edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr ((hG'_adj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
          rw [← heq] at hmem
          exact hna (SimpleGraph.mem_edgeFinset.mp hmem)
      have hcard_G' : #G'.edgeFinset ≤ Fintype.card (Sym2 V) := by
        rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      have hstep_m : Fintype.card (Sym2 V) - #G'.edgeFinset ≤ m := by omega
      obtain ⟨H, hG'H, hHTF, hHmax⟩ := ih G' hG'_TF (by convert hstep_m)
      exact ⟨H, hGG'.trans hG'H, hHTF, hHmax⟩

/-- Step 2: If a triangle-free graph with 11δ > 4n contains V_8 - (2, 6), then G maps to V_8
    (in consecutive And(3) labeling: φ v = φ u + 3 ∨ φ v = φ u + 4 ∨ φ v = φ u + 5). -/
lemma hom_v8_of_contains_v8_minus_e {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (h11d : ∀ x : V, 4 * Fintype.card V < 11 * (G.neighborSet x).ncard)
    (v : Fin 8 → V)
    (hv_adj : ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j)) :
    ∃ φ : V → Fin 8, ∀ x y : V, G.Adj x y →
      φ y = φ x + 3 ∨ φ y = φ x + 4 ∨ φ y = φ x + 5 := by
  classical
  set n := Fintype.card V
  have hdeg : ∀ x : V, 4 * n < 11 * #(Finset.univ.filter (G.Adj x)) := by
    intro x
    have h1 := h11d x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = Finset.univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  -- Convenient named edge facts in V_8 - (2, 6)
  have e01 : G.Adj (v 0) (v 1) := hv_adj 0 1 (by decide) (by decide) (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv_adj 1 2 (by decide) (by decide) (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv_adj 2 3 (by decide) (by decide) (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv_adj 3 4 (by decide) (by decide) (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv_adj 4 5 (by decide) (by decide) (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv_adj 5 6 (by decide) (by decide) (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv_adj 6 7 (by decide) (by decide) (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv_adj 7 0 (by decide) (by decide) (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv_adj 0 4 (by decide) (by decide) (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv_adj 1 5 (by decide) (by decide) (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv_adj 3 7 (by decide) (by decide) (by decide)
  -- Every vertex w hits at most 3 vertices of S = range v
  have hcap3 : ∀ w : V, #(Finset.univ.filter (fun i : Fin 8 => G.Adj w (v i))) ≤ 3 := by
    intro w
    let f : Fin 8 → ℕ := fun i => if G.Adj w (v i) then 1 else 0
    have hcard : #(Finset.univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
        f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
      rw [Finset.card_filter, Fin.sum_univ_eight]
    rw [hcard]
    have hna : ∀ {i j : Fin 8}, G.Adj (v i) (v j) → f i + f j ≤ 1 := by
      intro i j hij
      dsimp only [f]
      by_cases hi : G.Adj w (v i) <;> by_cases hj : G.Adj w (v j)
      · exact (not_adj_of_cliqueFree_three hTF hi hij hj).elim
      · simp [hi, hj]
      · simp [hi, hj]
      · simp [hi, hj]
    have h01 := hna e01; have h12 := hna e12; have h23 := hna e23; have h34 := hna e34
    have h45 := hna e45; have h56 := hna e56; have h67 := hna e67; have h70 := hna e70
    have h04 := hna e04; have h15 := hna e15; have h37 := hna e37
    have hle1 : ∀ i : Fin 8, f i ≤ 1 := fun i => by dsimp only [f]; split_ifs <;> omega
    have := hle1 0; have := hle1 1; have := hle1 2; have := hle1 3
    have := hle1 4; have := hle1 5; have := hle1 6; have := hle1 7
    omega
  -- Substep 2a (H_9-free): no vertex z is adjacent to {v 0, v 2, v 6} or {v 4, v 2, v 6}
  have hno026 : ∀ z : V, ¬ (G.Adj z (v 0) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
    rintro z ⟨hz0, hz2, hz6⟩
    let c : Fin 8 → ℕ := fun i =>
      if i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 then 3 else 2
    have hw_cap : ∀ w : V,
        (∑ i : Fin 8, if G.Adj w (v i) then c i else 0) + (if G.Adj w z then 2 else 0) ≤ 8 := by
      intro w
      let f : Fin 8 → ℕ := fun i => if G.Adj w (v i) then 1 else 0
      let fz : ℕ := if G.Adj w z then 1 else 0
      have hterm : ∀ i : Fin 8, (if G.Adj w (v i) then c i else 0) = c i * f i := by
        intro i; dsimp only [f]; split_ifs <;> simp
      have hrew : (∑ i : Fin 8, if G.Adj w (v i) then c i else 0) =
          2 * f 0 + 2 * f 1 + 3 * f 2 + 3 * f 3 + 2 * f 4 + 3 * f 5 + 3 * f 6 + 2 * f 7 := by
        simp_rw [hterm]; rw [Fin.sum_univ_eight]
        have hc0 : c 0 = 2 := by decide
        have hc1 : c 1 = 2 := by decide
        have hc2 : c 2 = 3 := by decide
        have hc3 : c 3 = 3 := by decide
        have hc4 : c 4 = 2 := by decide
        have hc5 : c 5 = 3 := by decide
        have hc6 : c 6 = 3 := by decide
        have hc7 : c 7 = 2 := by decide
        rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
      rw [hrew]
      have hfz_eq : (if G.Adj w z then 2 else 0) = 2 * fz := by dsimp only [fz]; split_ifs <;> omega
      rw [hfz_eq]
      have hna : ∀ {i j : Fin 8}, G.Adj (v i) (v j) → f i + f j ≤ 1 := by
        intro i j hij; dsimp only [f]
        by_cases hi : G.Adj w (v i) <;> by_cases hj : G.Adj w (v j)
        · exact (not_adj_of_cliqueFree_three hTF hi hij hj).elim
        · simp [hi, hj]
        · simp [hi, hj]
        · simp [hi, hj]
      have hnaz : ∀ {i : Fin 8}, G.Adj z (v i) → fz + f i ≤ 1 := by
        intro i hi; dsimp only [fz, f]
        by_cases h1 : G.Adj w z <;> by_cases h2 : G.Adj w (v i)
        · exact (not_adj_of_cliqueFree_three hTF h1 hi h2).elim
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      have := hna e01; have := hna e12; have := hna e23; have := hna e34
      have := hna e45; have := hna e56; have := hna e67; have := hna e70
      have := hna e04; have := hna e15; have := hna e37
      have := hnaz hz0; have := hnaz hz2; have := hnaz hz6
      have hle1 : ∀ i : Fin 8, f i ≤ 1 := fun i => by dsimp only [f]; split_ifs <;> omega
      have : fz ≤ 1 := by dsimp only [fz]; split_ifs <;> omega
      have := hle1 0; have := hle1 1; have := hle1 2; have := hle1 3
      have := hle1 4; have := hle1 5; have := hle1 6; have := hle1 7
      omega
    have hsum_le : ∑ w : V, ((∑ i : Fin 8, if G.Adj w (v i) then c i else 0) + (if G.Adj w z then 2 else 0)) ≤ 8 * n := by
      calc _ ≤ ∑ _w : V, 8 := Finset.sum_le_sum (fun w _ => hw_cap w)
        _ = 8 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((∑ i : Fin 8, if G.Adj w (v i) then c i else 0) + (if G.Adj w z then 2 else 0)) =
        (∑ i : Fin 8, c i * #(Finset.univ.filter (G.Adj (v i)))) + 2 * #(Finset.univ.filter (G.Adj z)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      · apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
    have hsum_gt : 88 * n < 11 * ((∑ i : Fin 8, c i * #(Finset.univ.filter (G.Adj (v i)))) +
        2 * #(Finset.univ.filter (G.Adj z))) := by
      have hc_sum : ∑ i : Fin 8, c i = 20 := by rw [Fin.sum_univ_eight]; decide
      have h1 : 80 * n < 11 * ∑ i : Fin 8, c i * #(Finset.univ.filter (G.Adj (v i))) := by
        rw [Finset.mul_sum]
        have hlt : ∑ i : Fin 8, c i * (4 * n) < ∑ i : Fin 8, 11 * (c i * #(Finset.univ.filter (G.Adj (v i)))) := by
          apply Finset.sum_lt_sum_of_nonempty (by simp)
          intro i _
          have hcpos : 0 < c i := by dsimp only [c]; split_ifs <;> omega
          have hdi := hdeg (v i)
          have := Nat.mul_lt_mul_of_pos_left hdi hcpos
          have : 11 * (c i * #(Finset.univ.filter (G.Adj (v i)))) = c i * (11 * #(Finset.univ.filter (G.Adj (v i)))) := by ring
          omega
        rw [← Finset.sum_mul, hc_sum] at hlt
        omega
      have h2 := hdeg z
      omega
    omega
  have hno426 : ∀ z : V, ¬ (G.Adj z (v 4) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
    rintro z ⟨hz4, hz2, hz6⟩
    let c : Fin 8 → ℕ := fun i =>
      if i = 1 ∨ i = 2 ∨ i = 6 ∨ i = 7 then 3 else 2
    have hw_cap : ∀ w : V,
        (∑ i : Fin 8, if G.Adj w (v i) then c i else 0) + (if G.Adj w z then 2 else 0) ≤ 8 := by
      intro w
      let f : Fin 8 → ℕ := fun i => if G.Adj w (v i) then 1 else 0
      let fz : ℕ := if G.Adj w z then 1 else 0
      have hterm : ∀ i : Fin 8, (if G.Adj w (v i) then c i else 0) = c i * f i := by
        intro i; dsimp only [f]; split_ifs <;> simp
      have hrew : (∑ i : Fin 8, if G.Adj w (v i) then c i else 0) =
          2 * f 0 + 3 * f 1 + 3 * f 2 + 2 * f 3 + 2 * f 4 + 2 * f 5 + 3 * f 6 + 3 * f 7 := by
        simp_rw [hterm]; rw [Fin.sum_univ_eight]
        have hc0 : c 0 = 2 := by decide
        have hc1 : c 1 = 3 := by decide
        have hc2 : c 2 = 3 := by decide
        have hc3 : c 3 = 2 := by decide
        have hc4 : c 4 = 2 := by decide
        have hc5 : c 5 = 2 := by decide
        have hc6 : c 6 = 3 := by decide
        have hc7 : c 7 = 3 := by decide
        rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
      rw [hrew]
      have hfz_eq : (if G.Adj w z then 2 else 0) = 2 * fz := by dsimp only [fz]; split_ifs <;> omega
      rw [hfz_eq]
      have hna : ∀ {i j : Fin 8}, G.Adj (v i) (v j) → f i + f j ≤ 1 := by
        intro i j hij; dsimp only [f]
        by_cases hi : G.Adj w (v i) <;> by_cases hj : G.Adj w (v j)
        · exact (not_adj_of_cliqueFree_three hTF hi hij hj).elim
        · simp [hi, hj]
        · simp [hi, hj]
        · simp [hi, hj]
      have hnaz : ∀ {i : Fin 8}, G.Adj z (v i) → fz + f i ≤ 1 := by
        intro i hi; dsimp only [fz, f]
        by_cases h1 : G.Adj w z <;> by_cases h2 : G.Adj w (v i)
        · exact (not_adj_of_cliqueFree_three hTF h1 hi h2).elim
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      have := hna e01; have := hna e12; have := hna e23; have := hna e34
      have := hna e45; have := hna e56; have := hna e67; have := hna e70
      have := hna e04; have := hna e15; have := hna e37
      have := hnaz hz4; have := hnaz hz2; have := hnaz hz6
      have hle1 : ∀ i : Fin 8, f i ≤ 1 := fun i => by dsimp only [f]; split_ifs <;> omega
      have : fz ≤ 1 := by dsimp only [fz]; split_ifs <;> omega
      have := hle1 0; have := hle1 1; have := hle1 2; have := hle1 3
      have := hle1 4; have := hle1 5; have := hle1 6; have := hle1 7
      omega
    have hsum_le : ∑ w : V, ((∑ i : Fin 8, if G.Adj w (v i) then c i else 0) + (if G.Adj w z then 2 else 0)) ≤ 8 * n := by
      calc _ ≤ ∑ _w : V, 8 := Finset.sum_le_sum (fun w _ => hw_cap w)
        _ = 8 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((∑ i : Fin 8, if G.Adj w (v i) then c i else 0) + (if G.Adj w z then 2 else 0)) =
        (∑ i : Fin 8, c i * #(Finset.univ.filter (G.Adj (v i)))) + 2 * #(Finset.univ.filter (G.Adj z)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      · apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
    have hsum_gt : 88 * n < 11 * ((∑ i : Fin 8, c i * #(Finset.univ.filter (G.Adj (v i)))) +
        2 * #(Finset.univ.filter (G.Adj z))) := by
      have hc_sum : ∑ i : Fin 8, c i = 20 := by rw [Fin.sum_univ_eight]; decide
      have h1 : 80 * n < 11 * ∑ i : Fin 8, c i * #(Finset.univ.filter (G.Adj (v i))) := by
        rw [Finset.mul_sum]
        have hlt : ∑ i : Fin 8, c i * (4 * n) < ∑ i : Fin 8, 11 * (c i * #(Finset.univ.filter (G.Adj (v i)))) := by
          apply Finset.sum_lt_sum_of_nonempty (by simp)
          intro i _
          have hcpos : 0 < c i := by dsimp only [c]; split_ifs <;> omega
          have hdi := hdeg (v i)
          have := Nat.mul_lt_mul_of_pos_left hdi hcpos
          have : 11 * (c i * #(Finset.univ.filter (G.Adj (v i)))) = c i * (11 * #(Finset.univ.filter (G.Adj (v i)))) := by ring
          omega
        rw [← Finset.sum_mul, hc_sum] at hlt
        omega
      have h2 := hdeg z
      omega
    omega
  -- Substep 2b: Partition V = U_0 ⊔ ... ⊔ U_7 ⊔ B
  let U : Fin 8 → Finset V := fun j =>
    Finset.univ.filter (fun w => G.Adj w (v (j + 1)) ∧ G.Adj w (v (j + 4)) ∧ G.Adj w (v (j + 7)))
  have hU_exact : ∀ j : Fin 8, ∀ w ∈ U j, ∀ i : Fin 8,
      G.Adj w (v i) ↔ (i = j + 1 ∨ i = j + 4 ∨ i = j + 7) := by
    intro j w hw i
    have ⟨h1, h4, h7⟩ := (Finset.mem_filter.mp hw).2
    constructor
    · intro hi
      by_contra hnot
      have hge4 : 4 ≤ #(Finset.univ.filter (fun k : Fin 8 => G.Adj w (v k))) := by
        have hsub : ({j + 1, j + 4, j + 7, i} : Finset (Fin 8)) ⊆
            Finset.univ.filter (fun k : Fin 8 => G.Adj w (v k)) := by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
          rcases hk with rfl | rfl | rfl | rfl <;> assumption
        have hcard4 : #({j + 1, j + 4, j + 7, i} : Finset (Fin 8)) = 4 := by
          have h14 : j + 1 ≠ j + 4 := by fin_cases j <;> decide
          have h17 : j + 1 ≠ j + 7 := by fin_cases j <;> decide
          have h47 : j + 4 ≠ j + 7 := by fin_cases j <;> decide
          have hi1 : i ≠ j + 1 := fun h => hnot (Or.inl h)
          have hi4 : i ≠ j + 4 := fun h => hnot (Or.inr (Or.inl h))
          have hi7 : i ≠ j + 7 := fun h => hnot (Or.inr (Or.inr h))
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hi7.symm]
          · simp [h47, hi4.symm]
          · simp [h14, h17, hi1.symm]
        have := Finset.card_le_card hsub; omega
      have := hcap3 w; omega
    · rintro (rfl | rfl | rfl) <;> assumption
  have hU_disj : ∀ j₁ j₂ : Fin 8, j₁ ≠ j₂ → Disjoint (U j₁) (U j₂) := by
    intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have h1 := hU_exact j₁ w hw1 (j₂ + 1)
    have h4 := hU_exact j₁ w hw1 (j₂ + 4)
    have h7 := hU_exact j₁ w hw1 (j₂ + 7)
    have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hw2).2
    have b1 := h1.mp a1; have b4 := h4.mp a4; have b7 := h7.mp a7
    fin_cases j₁ <;> fin_cases j₂ <;> simp at hne b1 b4 b7
  let B : Finset V := Finset.univ.filter (fun w => ∀ j : Fin 8, w ∉ U j)
  have hB_cap2 : ∀ w ∈ B, #(Finset.univ.filter (fun i : Fin 8 => G.Adj w (v i))) ≤ 2 := by
    intro w hwB
    have hnotU : ∀ j : Fin 8, ¬ (G.Adj w (v (j + 1)) ∧ G.Adj w (v (j + 4)) ∧ G.Adj w (v (j + 7))) :=
      fun j h => (Finset.mem_filter.mp hwB).2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    let f : Fin 8 → ℕ := fun i => if G.Adj w (v i) then 1 else 0
    have hcard : #(Finset.univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
        f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
      rw [Finset.card_filter, Fin.sum_univ_eight]
    rw [hcard]
    have hna : ∀ {i j : Fin 8}, G.Adj (v i) (v j) → f i + f j ≤ 1 := by
      intro i j hij; dsimp only [f]
      by_cases hi : G.Adj w (v i) <;> by_cases hj : G.Adj w (v j)
      · exact (not_adj_of_cliqueFree_three hTF hi hij hj).elim
      · simp [hi, hj]
      · simp [hi, hj]
      · simp [hi, hj]
    have hnot3 : ∀ a b c : Fin 8, ¬ (G.Adj w (v a) ∧ G.Adj w (v b) ∧ G.Adj w (v c)) → f a + f b + f c ≤ 2 := by
      intro a b c h; dsimp only [f]
      by_cases ha : G.Adj w (v a) <;> by_cases hb : G.Adj w (v b) <;> by_cases hc : G.Adj w (v c)
      · exact (h ⟨ha, hb, hc⟩).elim
      all_goals simp [ha, hb, hc]
    have := hna e01; have := hna e12; have := hna e23; have := hna e34
    have := hna e45; have := hna e56; have := hna e67; have := hna e70
    have := hna e04; have := hna e15; have := hna e37
    have := hnot3 1 4 7 (hnotU 0)
    have := hnot3 2 5 0 (hnotU 1)
    have := hnot3 3 6 1 (hnotU 2)
    have := hnot3 4 7 2 (hnotU 3)
    have := hnot3 5 0 3 (hnotU 4)
    have := hnot3 6 1 4 (hnotU 5)
    have := hnot3 7 2 5 (hnotU 6)
    have := hnot3 0 3 6 (hnotU 7)
    have := hnot3 0 2 6 (hno026 w)
    have := hnot3 4 2 6 (hno426 w)
    have hle1 : ∀ i : Fin 8, f i ≤ 1 := fun i => by dsimp only [f]; split_ifs <;> omega
    have := hle1 0; have := hle1 1; have := hle1 2; have := hle1 3
    have := hle1 4; have := hle1 5; have := hle1 6; have := hle1 7
    omega
  -- Equation (2.1): #B + ∑_{j : Fin 8} d(v j) <= 3 * n
  have h21 : #B + ∑ j : Fin 8, #(Finset.univ.filter (G.Adj (v j))) ≤ 3 * n := by
    have hpt : ∀ w : V, (if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun j : Fin 8 => G.Adj w (v j))) ≤ 3 := by
      intro w
      by_cases hw : w ∈ B
      · simp only [hw, if_true]; have := hB_cap2 w hw; omega
      · simp only [hw, if_false, zero_add]; exact hcap3 w
    have hsum_le : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun j : Fin 8 => G.Adj w (v j)))) ≤ 3 * n := by
      calc _ ≤ ∑ _w : V, 3 := Finset.sum_le_sum (fun w _ => hpt w)
        _ = 3 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun j : Fin 8 => G.Adj w (v j)))) =
        #B + ∑ j : Fin 8, #(Finset.univ.filter (G.Adj (v j))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      · simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
    omega
  -- Substep 2c: No vertex x hits U i and U j for an edge (i, j) of V_8
  have hno_hit_edge : ∀ (x : V) (i j : Fin 8),
      (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ∀ y₁ ∈ U i, ∀ y₂ ∈ U j, ¬ (G.Adj x y₁ ∧ G.Adj x y₂) := by
    rintro x i j hij y₁ hy₁ y₂ hy₂ ⟨hxy₁, hxy₂⟩
    have hcap4 : ∀ w : V,
        #(Finset.univ.filter (fun k : Fin 8 => G.Adj w (v k))) +
        (if G.Adj w x then 1 else 0) + (if G.Adj w y₁ then 1 else 0) + (if G.Adj w y₂ then 1 else 0) ≤ 4 := by
      intro w
      by_cases hwx : G.Adj w x
      · have hwy₁ : ¬ G.Adj w y₁ := fun h => not_adj_of_cliqueFree_three hTF hwx hxy₁ h
        have hwy₂ : ¬ G.Adj w y₂ := fun h => not_adj_of_cliqueFree_three hTF hwx hxy₂ h
        have := hcap3 w
        simp [hwx, hwy₁, hwy₂]; omega
      · by_cases hwy₁ : G.Adj w y₁
        · by_cases hwy₂ : G.Adj w y₂
          · -- w avoids N_{V_8}(i) ⊔ N_{V_8}(j) (size 6), leaving <= 2 of S!
            have hsub : Finset.univ.filter (fun k : Fin 8 => G.Adj w (v k)) ⊆
                Finset.univ \ ({i + 1, i + 4, i + 7, j + 1, j + 4, j + 7} : Finset (Fin 8)) := by
              intro k hk
              have hwk : G.Adj w (v k) := (Finset.mem_filter.mp hk).2
              apply Finset.mem_sdiff.mpr; refine ⟨Finset.mem_univ _, ?_⟩
              intro hmem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
              rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
              · exact not_adj_of_cliqueFree_three hTF hwy₁ (Finset.mem_filter.mp hy₁).2.1 hwk
              · exact not_adj_of_cliqueFree_three hTF hwy₁ (Finset.mem_filter.mp hy₁).2.2.1 hwk
              · exact not_adj_of_cliqueFree_three hTF hwy₁ (Finset.mem_filter.mp hy₁).2.2.2 hwk
              · exact not_adj_of_cliqueFree_three hTF hwy₂ (Finset.mem_filter.mp hy₂).2.1 hwk
              · exact not_adj_of_cliqueFree_three hTF hwy₂ (Finset.mem_filter.mp hy₂).2.2.1 hwk
              · exact not_adj_of_cliqueFree_three hTF hwy₂ (Finset.mem_filter.mp hy₂).2.2.2 hwk
            have hcard6 : #({i + 1, i + 4, i + 7, j + 1, j + 4, j + 7} : Finset (Fin 8)) = 6 := by
              rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)
            have hle2 : #(Finset.univ.filter (fun k : Fin 8 => G.Adj w (v k))) ≤ 2 := by
              have h1 := Finset.card_le_card hsub
              rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard6] at h1
              omega
            simp [hwx, hwy₁, hwy₂]; omega
          · have := hcap3 w; simp [hwx, hwy₁, hwy₂]; omega
        · have := hcap3 w; simp [hwx, hwy₁]; split_ifs <;> omega
    have hsum_le : ∑ w : V, (#(Finset.univ.filter (fun k : Fin 8 => G.Adj w (v k))) +
        (if G.Adj w x then 1 else 0) + (if G.Adj w y₁ then 1 else 0) + (if G.Adj w y₂ then 1 else 0)) ≤ 4 * n := by
      calc _ ≤ ∑ _w : V, 4 := Finset.sum_le_sum (fun w _ => hcap4 w)
        _ = 4 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, (#(Finset.univ.filter (fun k : Fin 8 => G.Adj w (v k))) +
        (if G.Adj w x then 1 else 0) + (if G.Adj w y₁ then 1 else 0) + (if G.Adj w y₂ then 1 else 0)) =
        (∑ k : Fin 8, #(Finset.univ.filter (G.Adj (v k)))) +
        #(Finset.univ.filter (G.Adj x)) + #(Finset.univ.filter (G.Adj y₁)) + #(Finset.univ.filter (G.Adj y₂)) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1; congr 1; congr 1
      · simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      · rw [← Finset.card_filter]; congr 1; ext w; simp [G.adj_comm]
      · rw [← Finset.card_filter]; congr 1; ext w; simp [G.adj_comm]
      · rw [← Finset.card_filter]; congr 1; ext w; simp [G.adj_comm]
    have hsum_gt : 44 * n < 11 * ((∑ k : Fin 8, #(Finset.univ.filter (G.Adj (v k)))) +
        #(Finset.univ.filter (G.Adj x)) + #(Finset.univ.filter (G.Adj y₁)) + #(Finset.univ.filter (G.Adj y₂))) := by
      have h8 : 32 * n < 11 * ∑ k : Fin 8, #(Finset.univ.filter (G.Adj (v k))) := by
        rw [Finset.mul_sum]
        have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 8))) (by simp)
          (fun k _ => hdeg (v k))
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
        omega
      have hx := hdeg x; have hy1 := hdeg y₁; have hy2 := hdeg y₂
      omega
    omega
  -- Substep 2d: Build cls : V -> Fin 8 and verify homomorphism
  have hex_cls : ∀ x : V, ∃ c : Fin 8, ∀ j : Fin 8, (∃ y ∈ U j, G.Adj x y) →
      j = c + 1 ∨ j = c + 4 ∨ j = c + 7 := by
    intro x
    let J : Finset (Fin 8) := Finset.univ.filter (fun j => ∃ y ∈ U j, G.Adj x y)
    have hJ_indep : ∀ i ∈ J, ∀ j ∈ J, ¬ (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) := by
      intro i hi j hj hij
      obtain ⟨y₁, hy₁, hxy₁⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨y₂, hy₂, hxy₂⟩ := (Finset.mem_filter.mp hj).2
      exact hno_hit_edge x i j hij y₁ hy₁ y₂ hy₂ ⟨hxy₁, hxy₂⟩
    -- Every independent set of V_8 is contained in some N_{V_8}(c)!
    obtain ⟨c, hc⟩ := v8_indep_subset_nbhd J hJ_indep
    exact ⟨c, fun j hj => hc j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  let cls : V → Fin 8 := fun x => (hex_cls x).choose
  have hcls_spec : ∀ x : V, ∀ j : Fin 8, ∀ y ∈ U j, G.Adj x y →
      j = cls x + 1 ∨ j = cls x + 4 ∨ j = cls x + 7 :=
    fun x j y hy hxy => (hex_cls x).choose_spec j ⟨y, hy, hxy⟩
  have hcls_hom : ∀ a b : V, G.Adj a b →
      cls b = cls a + 1 ∨ cls b = cls a + 4 ∨ cls b = cls a + 7 := by
    intro a b hab
    by_contra hnot
    -- Non-edge (cls a, cls b) in V_8 omits a full neighborhood N_{V_8}(r)
    obtain ⟨r, hr⟩ := v8_nonedge_omits_nbhd (cls a) (cls b) hnot
    -- Every vertex w ∈ V has: 1_{a~w} + 1_{b~w} + 1_{v_r ~ w} <= 1 + 1_{w ∈ B}
    have hpt : ∀ w : V,
        (if G.Adj a w then 1 else 0) + (if G.Adj b w then 1 else 0) + (if G.Adj (v r) w then 1 else 0) ≤
        1 + (if w ∈ B then 1 else 0) := by
      intro w
      by_cases hwB : w ∈ B
      · simp only [hwB, if_true]
        by_cases haw : G.Adj a w <;> by_cases hbw : G.Adj b w
        · exact (not_adj_of_cliqueFree_three hTF hab hbw haw).elim
        all_goals (simp [haw, hbw]; split_ifs <;> omega)
      · simp only [hwB, if_false, add_zero]
        have hexU : ∃ j : Fin 8, w ∈ U j := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
        obtain ⟨j, hwUj⟩ := hexU
        by_cases hvr : G.Adj (v r) w
        · have hj_r : j = r + 1 ∨ j = r + 4 ∨ j = r + 7 := by
            have h1 := (hU_exact j w hwUj r).mp hvr.symm
            fin_cases r <;> fin_cases j <;> simp at h1 ⊢
          have ⟨hnot_a, hnot_b⟩ := hr j hj_r
          have hna : ¬ G.Adj a w := fun h => hnot_a (hcls_spec a j w hwUj h)
          have hnb : ¬ G.Adj b w := fun h => hnot_b (hcls_spec b j w hwUj h)
          simp [hna, hnb, hvr]
        · by_cases haw : G.Adj a w <;> by_cases hbw : G.Adj b w
          · exact (not_adj_of_cliqueFree_three hTF hab hbw haw).elim
          all_goals simp [haw, hbw, hvr]
    have hsum_le : #(Finset.univ.filter (G.Adj a)) + #(Finset.univ.filter (G.Adj b)) +
        #(Finset.univ.filter (G.Adj (v r))) ≤ n + #B := by
      have h1 : ∑ w : V, ((if G.Adj a w then 1 else 0) + (if G.Adj b w then 1 else 0) +
          (if G.Adj (v r) w then 1 else 0)) ≤ ∑ w : V, (1 + (if w ∈ B then 1 else 0)) :=
        Finset.sum_le_sum (fun w _ => hpt w)
      simp_rw [Finset.sum_add_distrib, ← Finset.card_filter] at h1
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
        Finset.filter_mem_eq_inter, Finset.univ_inter] at h1
      omega
    have htot_le : #(Finset.univ.filter (G.Adj a)) + #(Finset.univ.filter (G.Adj b)) +
        #(Finset.univ.filter (G.Adj (v r))) + ∑ j : Fin 8, #(Finset.univ.filter (G.Adj (v j))) ≤ 4 * n := by
      omega
    have htot_gt : 44 * n < 11 * (#(Finset.univ.filter (G.Adj a)) + #(Finset.univ.filter (G.Adj b)) +
        #(Finset.univ.filter (G.Adj (v r))) + ∑ j : Fin 8, #(Finset.univ.filter (G.Adj (v j)))) := by
      have h8 : 32 * n < 11 * ∑ j : Fin 8, #(Finset.univ.filter (G.Adj (v j))) := by
        rw [Finset.mul_sum]
        have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 8))) (by simp)
          (fun j _ => hdeg (v j))
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
        omega
      have ha := hdeg a; have hb := hdeg b; have hvr := hdeg (v r)
      omega
    omega
  -- Convert Möbius labeling (diff ∈ {1,4,7}) to consecutive And(3) (diff ∈ {3,4,5}) via i ↦ 3 * i
  refine ⟨fun x => 3 * cls x, ?_⟩
  intro x y hxy
  have h := hcls_hom x y hxy
  have hmul : ∀ c : Fin 8, 3 * (c + 1) = 3 * c + 3 ∧ 3 * (c + 4) = 3 * c + 4 ∧ 3 * (c + 7) = 3 * c + 5 :=
    fun c => by fin_cases c <;> decide
  dsimp only
  rcases h with h | h | h <;> rw [h]
  · exact Or.inl (hmul (cls x)).1
  · exact Or.inr (Or.inl (hmul (cls x)).2.1)
  · exact Or.inr (Or.inr (hmul (cls x)).2.2)


lemma fin5_add_1_1 (i : Fin 5) : i + 1 + 1 = i + 2 := by fin_cases i <;> decide
lemma fin5_add_1_4 (i : Fin 5) : i + 1 + 4 = i := by fin_cases i <;> decide
lemma fin5_add_2_1 (i : Fin 5) : i + 2 + 1 = i + 3 := by fin_cases i <;> decide
lemma fin5_add_3_1 (i : Fin 5) : i + 3 + 1 = i + 4 := by fin_cases i <;> decide
lemma fin5_add_4_1 (i : Fin 5) : i + 4 + 1 = i := by fin_cases i <;> decide
lemma fin5_add_4_4 (i : Fin 5) : i + 4 + 4 = i + 3 := by fin_cases i <;> decide
lemma fin5_add_2_4 (i : Fin 5) : i + 2 + 4 = i + 1 := by fin_cases i <;> decide
lemma fin5_add_3_4 (i : Fin 5) : i + 3 + 4 = i + 2 := by fin_cases i <;> decide
lemma fin5_cases_rel (r j : Fin 5) : j = r ∨ j = r + 1 ∨ j = r + 2 ∨ j = r + 3 ∨ j = r + 4 := by fin_cases r <;> fin_cases j <;> decide
lemma fin5_neg_add (k : Fin 5) : -(k + 1) + 1 = -k := by fin_cases k <;> decide
lemma fin5_neg_neg_1 (r : Fin 5) : -(-r + 1) = r + 4 := by fin_cases r <;> decide
lemma fin5_neg_neg_4 (r : Fin 5) : -(-r + 4) = r + 1 := by fin_cases r <;> decide
lemma fin5_neg_neg_2 (r : Fin 5) : -(-r + 2) = r + 3 := by fin_cases r <;> decide

/-- Tiny top-level helper: construct a homomorphism `V_8 - (2, 6) -> G` from 8 vertices and 11 edges. -/
lemma exists_v8_minus_e_of_edges {V : Type} {G : SimpleGraph V}
    (u0 u1 u2 u3 u4 u5 u6 u7 : V)
    (e01 : G.Adj u0 u1) (e12 : G.Adj u1 u2) (e23 : G.Adj u2 u3) (e34 : G.Adj u3 u4)
    (e45 : G.Adj u4 u5) (e56 : G.Adj u5 u6) (e67 : G.Adj u6 u7) (e70 : G.Adj u7 u0)
    (e04 : G.Adj u0 u4) (e15 : G.Adj u1 u5) (e37 : G.Adj u3 u7) :
    ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j) := by
  refine ⟨fun k => if k = 0 then u0 else if k = 1 then u1 else if k = 2 then u2 else
    if k = 3 then u3 else if k = 4 then u4 else if k = 5 then u5 else if k = 6 then u6 else u7, ?_⟩
  intro i j hij h26 h62
  rcases hij with rfl | rfl | rfl
  · fin_cases i
    · exact e01
    · exact e12
    · exact e23
    · exact e34
    · exact e45
    · exact e56
    · exact e67
    · exact e70
  · fin_cases i
    · exact e04
    · exact e15
    · exact (h26 ⟨rfl, rfl⟩).elim
    · exact e37
    · exact e04.symm
    · exact e15.symm
    · exact (h62 ⟨rfl, rfl⟩).elim
    · exact e37.symm
  · fin_cases i
    · exact e70.symm
    · exact e01.symm
    · exact e12.symm
    · exact e23.symm
    · exact e34.symm
    · exact e45.symm
    · exact e56.symm
    · exact e67.symm

/-- Step 3: Maximal triangle-free + 5α < 2n + 11δ > 4n + no homomorphism from V_8 - (2, 6)
    implies G is 3-colorable! (Takes shortest-odd-walk helpers as parameters so it plugs
    straight into R2 without duplicating them.) -/
theorem colorable_three_of_no_v8_minus_e {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h5a : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → 5 * #I < 2 * Fintype.card V)
    (h11d : ∀ x : V, 4 * Fintype.card V < 11 * (G.neighborSet x).ncard)
    (hnoV8 : ¬ ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j))
    (hshort_walk : ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
      H.CliqueFree 3 → ¬ H.Colorable 2 →
      ∃ L : ℕ, Odd L ∧ 5 ≤ L ∧
        (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → W, g L' = g 0 ∧ ∀ i < L', H.Adj (g i) (g (i + 1))) ∧
        ∃ f : ℕ → W, f L = f 0 ∧ (∀ i < L, H.Adj (f i) (f (i + 1))) ∧
          (∀ i j, i < j → j < L → f i ≠ f j) ∧
          (∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ H.Adj (f i) (f j)))
    (hshort_deg2 : ∀ (W : Type) [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      H.CliqueFree 3 → ∀ {L : ℕ}, Odd L → 5 ≤ L →
      (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → W, g L' = g 0 ∧ ∀ i < L', H.Adj (g i) (g (i + 1))) →
      ∀ {f : ℕ → W}, f L = f 0 → (∀ i < L, H.Adj (f i) (f (i + 1))) →
      ∀ w : W, #((Finset.range L).filter (fun i => H.Adj w (f i))) ≤ 2) :
    G.Colorable 3 := by
  classical
  by_contra hnot3
  set n := Fintype.card V
  have hn_pos : 0 < n := by
    by_contra h0
    have hE : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact hnot3 ⟨SimpleGraph.Coloring.mk (fun x => (hE.false x).elim)
      (fun {a _} _ => (hE.false a).elim)⟩
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hn_pos
  have hdeg : ∀ x : V, 4 * n < 11 * #(Finset.univ.filter (G.Adj x)) := by
    intro x
    have h1 := h11d x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = Finset.univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hdeg_up : ∀ x : V, 5 * #(Finset.univ.filter (G.Adj x)) < 2 * n := fun x =>
    h5a _ (fun u hu v hv huv => not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hu).2 huv
      (Finset.mem_filter.mp hv).2)
  -- Substep 3a: Pick a shortest odd cycle C of length L in G - N(v₀); force L = 5
  let I : Finset V := Finset.univ.filter (G.Adj v₀)
  have h5I : 5 * #I < 2 * n := hdeg_up v₀
  let S : Set V := {w : V | w ∉ I}
  let H : SimpleGraph S := G.induce S
  have hH_TF : H.CliqueFree 3 := by
    intro t ht
    apply hTF (t.image Subtype.val)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact ht.1 ha hb (fun hab => hxy (congrArg Subtype.val hab))
    · rw [Finset.card_image_of_injective _ Subtype.val_injective, ht.2]
  have hH_not2 : ¬ H.Colorable 2 := by
    rintro ⟨c2⟩
    apply hnot3
    refine ⟨SimpleGraph.Coloring.mk (fun w =>
      if hw : w ∈ I then (2 : Fin 3) else ⟨(c2 ⟨w, hw⟩).val, by have := (c2 ⟨w, hw⟩).isLt; omega⟩) ?_⟩
    intro a b hab
    by_cases ha : a ∈ I <;> by_cases hb : b ∈ I
    · exfalso
      exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp ha).2 hab (Finset.mem_filter.mp hb).2
    · simp only [ha, hb, dite_true, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      have hlt := (c2 ⟨b, hb⟩).isLt
      dsimp only at hval; omega
    · simp only [ha, hb, dite_true, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      have hlt := (c2 ⟨a, ha⟩).isLt
      dsimp only at hval; omega
    · simp only [ha, hb, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only at hval
      exact c2.valid (show H.Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab) (Fin.ext hval)
  obtain ⟨L, hL_odd, hL5, hL_min, fH, hfH_loop, hfH_adj, _, _⟩ := hshort_walk S H hH_TF hH_not2
  let f : ℕ → V := fun i => (fH i).val
  have hf_loop : f L = f 0 := congrArg Subtype.val hfH_loop
  have hf_adj : ∀ i < L, G.Adj (f i) (f (i + 1)) := fun i hi => hfH_adj i hi
  have hf_notI : ∀ i : ℕ, f i ∉ I := fun i => (fH i).property
  have hL_eq5 : L = 5 := by
    have hdeg_out : ∀ w : V, w ∉ I → #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 := fun w hw =>
      hshort_deg2 S H hH_TF hL_odd hL5 hL_min hfH_loop hfH_adj ⟨w, hw⟩
    have hdeg_in : ∀ w : V, 2 * #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ L - 1 := by
      intro w
      set T := (Finset.range L).filter (fun i => G.Adj w (f i))
      have hinj : Set.InjOn (fun i : ℕ => (i + 1) % L) (T : Set ℕ) := by
        intro a ha b hb heq
        dsimp only at heq
        have haL := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hbL := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        by_cases ha1 : a + 1 < L <;> by_cases hb1 : b + 1 < L
        · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at heq; omega
        · rw [Nat.mod_eq_of_lt ha1, show b + 1 = L by omega, Nat.mod_self] at heq; omega
        · rw [show a + 1 = L by omega, Nat.mod_self, Nat.mod_eq_of_lt hb1] at heq; omega
        · omega
      have hdisj : Disjoint T (T.image (fun i => (i + 1) % L)) := by
        rw [Finset.disjoint_left]
        intro j hjT hjIm
        obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hjIm
        have hiL := Finset.mem_range.mp (Finset.mem_filter.mp hiT).1
        have hwi := (Finset.mem_filter.mp hiT).2
        have hwj := (Finset.mem_filter.mp hjT).2
        by_cases hi1 : i + 1 < L
        · rw [Nat.mod_eq_of_lt hi1] at hwj
          exact not_adj_of_cliqueFree_three hTF hwi (hf_adj i hiL) hwj
        · rw [show i + 1 = L by omega, Nat.mod_self] at hwj
          have hadj := hf_adj i hiL
          rw [show i + 1 = L by omega, hf_loop] at hadj
          exact not_adj_of_cliqueFree_three hTF hwi hadj hwj
      have hsub : T ∪ T.image (fun i => (i + 1) % L) ⊆ Finset.range L := by
        refine Finset.union_subset (Finset.filter_subset _ _) ?_
        intro j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
      have h2T : 2 * #T ≤ L := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, Finset.card_range] at h1
        omega
      obtain ⟨m, hm⟩ := hL_odd
      omega
    have hsum_swap : ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) =
        ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro i _; simp [G.adj_comm]
    have hsum_up : 2 * ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) ≤
        4 * (n - #I) + (L - 1) * #I := by
      rw [hsum_swap]
      have hpart : ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i))) =
          ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) +
          ∑ w ∈ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
        rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset (Finset.subset_univ I)]
      have h1 : ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 * (n - #I) := by
        calc _ ≤ ∑ _w ∈ Finset.univ \ I, 2 := Finset.sum_le_sum (fun w hw => hdeg_out w (Finset.mem_sdiff.mp hw).2)
          _ = #(Finset.univ \ I) * 2 := by rw [Finset.sum_const, smul_eq_mul]
          _ = 2 * (n - #I) := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, mul_comm]
      have h2 : 2 * ∑ w ∈ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ (L - 1) * #I := by
        rw [Finset.mul_sum]
        calc _ ≤ ∑ _w ∈ I, (L - 1) := Finset.sum_le_sum (fun w _ => hdeg_in w)
          _ = (L - 1) * #I := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have hsum_lo : 4 * n * L < 11 * ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := Finset.range L) (by rw [Finset.nonempty_range_iff]; omega)
        (fun i _ => hdeg (f i))
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm] at hlt
      exact hlt
    have hI_le : #I ≤ n := (Finset.card_le_card (Finset.subset_univ I)).trans (by simp [n])
    have h4n : 4 * (n - #I) + (L - 1) * #I = 4 * n + (L - 5) * #I := by
      zify [hI_le, hL5, show 1 ≤ L by omega]; ring
    rw [h4n] at hsum_up
    have hcomb : 40 * n * L < 220 * n + 11 * (L - 5) * (2 * n) := by
      have hmul : (L - 5) * (5 * #I) ≤ (L - 5) * (2 * n) := Nat.mul_le_mul_left (L - 5) (by omega)
      nlinarith only [hsum_lo, hsum_up, hmul]
    have hLlt : 40 * L < 220 + 22 * (L - 5) := by nlinarith only [hcomb, hn_pos]
    obtain ⟨m, hm⟩ := hL_odd
    omega
  -- Helper: build a V_8 - (2, 6) contradiction from 8 vertices and 11 edges
  have hV8_contra : ∀ (u0 u1 u2 u3 u4 u5 u6 u7 : V),
      G.Adj u0 u1 → G.Adj u1 u2 → G.Adj u2 u3 → G.Adj u3 u4 →
      G.Adj u4 u5 → G.Adj u5 u6 → G.Adj u6 u7 → G.Adj u7 u0 →
      G.Adj u0 u4 → G.Adj u1 u5 → G.Adj u3 u7 → False :=
    fun u0 u1 u2 u3 u4 u5 u6 u7 e01 e12 e23 e34 e45 e56 e67 e70 e04 e15 e37 =>
      hnoV8 (exists_v8_minus_e_of_edges u0 u1 u2 u3 u4 u5 u6 u7 e01 e12 e23 e34 e45 e56 e67 e70 e04 e15 e37)
  -- Shared bound: for any 5-cycle c, the set B of vertices outside A_0 ∪ ... ∪ A_4 has 11 * #B < 2 * n
  have hB_bound_any : ∀ (c : Fin 5 → V), (∀ i : Fin 5, G.Adj (c i) (c (i + 1))) →
      11 * #(Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))) < 2 * n := by
    intro c hc_adj
    let B : Finset V := Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))
    have hpt : ∀ w : V, (if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i))) ≤ 2 := by
      intro w
      let b : Fin 5 → ℕ := fun i => if G.Adj w (c i) then 1 else 0
      have hcard : #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i))) =
          b 0 + b 1 + b 2 + b 3 + b 4 := by rw [Finset.card_filter, Fin.sum_univ_five]
      rw [hcard]
      have hna : ∀ i : Fin 5, b i + b (i + 1) ≤ 1 := by
        intro i; dsimp only [b]
        by_cases h1 : G.Adj w (c i) <;> by_cases h2 : G.Adj w (c (i + 1))
        · exact (not_adj_of_cliqueFree_three hTF h1 (hc_adj i) h2).elim
        all_goals simp [h1, h2]
      have h01 : b 0 + b 1 ≤ 1 := hna 0
      have h12 : b 1 + b 2 ≤ 1 := hna 1
      have h23 : b 2 + b 3 ≤ 1 := hna 2
      have h34 : b 3 + b 4 ≤ 1 := hna 3
      have h40 : b 4 + b 0 ≤ 1 := hna 4
      by_cases hwB : w ∈ B
      · simp only [hwB, if_true]
        have hnotA : ∀ i : Fin 5, b (i + 1) + b (i + 4) ≤ 1 := by
          intro i; dsimp only [b]
          by_cases h1 : G.Adj w (c (i + 1)) <;> by_cases h2 : G.Adj w (c (i + 4))
          · exfalso; exact (Finset.mem_filter.mp hwB).2 i ⟨h1, h2⟩
          all_goals simp [h1, h2]
        have : b 1 + b 4 ≤ 1 := hnotA 0
        have : b 2 + b 0 ≤ 1 := hnotA 1
        have : b 3 + b 1 ≤ 1 := hnotA 2
        have : b 4 + b 2 ≤ 1 := hnotA 3
        have : b 0 + b 3 ≤ 1 := hnotA 4
        omega
      · simp only [hwB, if_false, zero_add]; omega
    have hsum_le : #B + ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) ≤ 2 * n := by
      have h1 : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i)))) ≤ 2 * n := by
        calc _ ≤ ∑ _w : V, 2 := Finset.sum_le_sum (fun w _ => hpt w)
          _ = 2 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      have h2 : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i)))) =
          #B + ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        · simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      omega
    have hsum_gt : 20 * n < 11 * ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 5))) (by simp)
        (fun i _ => hdeg (c i))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
      omega
    change 11 * #B < 2 * n
    omega
  -- Helper: for ANY 5-cycle c avoiding N(v₀), prove (P1), (P2) and finish when v₀ hits A_r & avoids A_{r+3}!
  have hfinish : ∀ (c : Fin 5 → V), (∀ i : Fin 5, G.Adj (c i) (c (i + 1))) →
      (∀ i : Fin 5, ¬ G.Adj v₀ (c i)) →
      ∀ (r : Fin 5) (w₀ : V), G.Adj w₀ (c (r + 1)) → G.Adj w₀ (c (r + 4)) → G.Adj v₀ w₀ →
      (∀ w : V, G.Adj w (c (r + 4)) → G.Adj w (c (r + 2)) → ¬ G.Adj v₀ w) → False := by
    intro c hc_adj hv0_c r w₀ hw01 hw04 hv0w0 hno_r3
    let A : Fin 5 → Finset V := fun i => Finset.univ.filter (fun w => G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4)))
    let B : Finset V := Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))
    have hB_bound : 11 * #B < 2 * n := hB_bound_any c hc_adj
    -- (P1): No vertex x hits both A i and A (i + 1)
    have hP1 : ∀ (i : Fin 5) (x y1 y2 : V), y1 ∈ A i → y2 ∈ A (i + 1) →
        G.Adj x y1 → G.Adj x y2 → False := by
      intro i x y1 y2 hy1 hy2 hxy1 hxy2
      have ⟨h1a, h1b⟩ := (Finset.mem_filter.mp hy1).2
      have ⟨h2a, h2b⟩ := (Finset.mem_filter.mp hy2).2
      rw [fin5_add_1_1] at h2a
      rw [fin5_add_1_4] at h2b
      have e45 : G.Adj (c (i + 1)) (c (i + 2)) := by have h := hc_adj (i + 1); rwa [fin5_add_1_1] at h
      have e56 : G.Adj (c (i + 2)) (c (i + 3)) := by have h := hc_adj (i + 2); rwa [fin5_add_2_1] at h
      have e67 : G.Adj (c (i + 3)) (c (i + 4)) := by have h := hc_adj (i + 3); rwa [fin5_add_3_1] at h
      have e70 : G.Adj (c (i + 4)) (c i) := by have h := hc_adj (i + 4); rwa [fin5_add_4_1] at h
      exact hV8_contra (c i) y2 x y1 (c (i + 1)) (c (i + 2)) (c (i + 3)) (c (i + 4))
        h2b.symm hxy2.symm hxy1 h1a e45 e56 e67 e70 (hc_adj i) h2a h1b
    -- (P2): No edge (a, b) with a hitting A (i + 4) and A (i + 1) and b hitting A (i + 1)
    have hP2 : ∀ (i : Fin 5) (a b u v' y : V), u ∈ A (i + 4) → v' ∈ A (i + 1) → y ∈ A (i + 1) →
        G.Adj a u → G.Adj a v' → G.Adj a b → G.Adj b y → False := by
      intro i a b u v' y hu hv' hy hau hav' hab hby
      have ⟨hua, hub⟩ := (Finset.mem_filter.mp hu).2
      have ⟨hva, hvb⟩ := (Finset.mem_filter.mp hv').2
      have ⟨hya, hyb⟩ := (Finset.mem_filter.mp hy).2
      rw [fin5_add_4_1] at hua
      rw [fin5_add_4_4] at hub
      rw [fin5_add_1_1] at hva hya
      rw [fin5_add_1_4] at hvb hyb
      have e23 : G.Adj (c (i + 3)) (c (i + 2)) := by have h := (hc_adj (i + 2)).symm; rwa [fin5_add_2_1] at h
      exact hV8_contra (c i) u (c (i + 3)) (c (i + 2)) v' a b y
        hua.symm hub e23 hva.symm hav'.symm hab hby hyb hvb.symm hau.symm hya.symm
    -- Pick common neighbor z₀ of v₀ and c r via maximality
    have hv0_ne : v₀ ≠ c r := by
      intro heq; rw [heq] at hv0_c; exact hv0_c (r + 1) (hc_adj r)
    obtain ⟨z₀, hv0z0, hcrz0⟩ := hmax v₀ (c r) hv0_ne (hv0_c r)
    have hcrA : c r ∈ A r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_adj r, by
      have h := (hc_adj (r + 4)).symm; rwa [fin5_add_4_1] at h⟩
    have hw0A : w₀ ∈ A r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw01, hw04⟩
    have hw0A4 : w₀ ∈ A (r + 4 + 1) := by rw [fin5_add_4_1]; exact hw0A
    have hcrA4 : c r ∈ A (r + 4 + 1) := by rw [fin5_add_4_1]; exact hcrA
    -- Both N(v₀) and N(z₀) lie inside N(c (r + 1)) ∪ B!
    have hsub_v0 : Finset.univ.filter (G.Adj v₀) ⊆ Finset.univ.filter (G.Adj (c (r + 1))) ∪ B := by
      intro w hw
      have hv0w := (Finset.mem_filter.mp hw).2
      by_cases hwB : w ∈ B
      · exact Finset.mem_union_right _ hwB
      · have hexA : ∃ j : Fin 5, w ∈ A j := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => hnone j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩)
        obtain ⟨j, hwAj⟩ := hexA
        rcases fin5_cases_rel r j with rfl | rfl | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwAj).2.1.symm⟩)
        · exact (hP1 r v₀ w₀ w hw0A hwAj hv0w0 hv0w).elim
        · have h2 := (Finset.mem_filter.mp hwAj).2.2
          rw [fin5_add_2_4] at h2
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.symm⟩)
        · have ⟨h3a, h3b⟩ := (Finset.mem_filter.mp hwAj).2
          rw [fin5_add_3_1] at h3a
          rw [fin5_add_3_4] at h3b
          exact (hno_r3 w h3a h3b hv0w).elim
        · exact (hP1 (r + 4) v₀ w w₀ hwAj hw0A4 hv0w hv0w0).elim
    have hsub_z0 : Finset.univ.filter (G.Adj z₀) ⊆ Finset.univ.filter (G.Adj (c (r + 1))) ∪ B := by
      intro w hw
      have hz0w := (Finset.mem_filter.mp hw).2
      by_cases hwB : w ∈ B
      · exact Finset.mem_union_right _ hwB
      · have hexA : ∃ j : Fin 5, w ∈ A j := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => hnone j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩)
        obtain ⟨j, hwAj⟩ := hexA
        rcases fin5_cases_rel r j with rfl | rfl | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwAj).2.1.symm⟩)
        · exact (hP1 r z₀ (c r) w hcrA hwAj hcrz0.symm hz0w).elim
        · have h2 := (Finset.mem_filter.mp hwAj).2.2
          rw [fin5_add_2_4] at h2
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.symm⟩)
        · have hwA4 : w ∈ A (r + 4 + 4) := by rw [fin5_add_4_4]; exact hwAj
          exact (hP2 (r + 4) z₀ v₀ w (c r) w₀ hwA4 hcrA4 hw0A4 hz0w hcrz0.symm hv0z0.symm hv0w0).elim
        · exact (hP1 (r + 4) z₀ w (c r) hwAj hcrA4 hz0w hcrz0.symm).elim
    have hdisj_vz : Disjoint (Finset.univ.filter (G.Adj v₀)) (Finset.univ.filter (G.Adj z₀)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      exact not_adj_of_cliqueFree_three hTF hv0z0 (Finset.mem_filter.mp hw2).2 (Finset.mem_filter.mp hw1).2
    have hcard_sum : #(Finset.univ.filter (G.Adj v₀)) + #(Finset.univ.filter (G.Adj z₀)) ≤
        #(Finset.univ.filter (G.Adj (c (r + 1)))) + #B := by
      rw [← Finset.card_union_of_disjoint hdisj_vz]
      exact (Finset.card_le_card (Finset.union_subset hsub_v0 hsub_z0)).trans (Finset.card_union_le _ _)
    have hd_v0 := hdeg v₀
    have hd_z0 := hdeg z₀
    have hd_up := hdeg_up (c (r + 1))
    omega
  -- Instantiate c : Fin 5 -> V from the shortest 5-cycle f
  let c : Fin 5 → V := fun i => f i.val
  have hc_adj : ∀ i : Fin 5, G.Adj (c i) (c (i + 1)) := by
    intro i; fin_cases i
    · exact hf_adj 0 (by omega)
    · exact hf_adj 1 (by omega)
    · exact hf_adj 2 (by omega)
    · exact hf_adj 3 (by omega)
    · have h4 := hf_adj 4 (by omega)
      rw [show 4 + 1 = L by omega, hf_loop] at h4
      exact h4
  have hv0_c : ∀ i : Fin 5, ¬ G.Adj v₀ (c i) := fun i h =>
    hf_notI i.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  -- Either v₀ hits some A_r (then orient c so v₀ avoids A_{r+3}) or N(v₀) ⊆ B (contradicting #B < 2n/11)!
  by_cases hex : ∃ (r : Fin 5) (w₀ : V), G.Adj w₀ (c (r + 1)) ∧ G.Adj w₀ (c (r + 4)) ∧ G.Adj v₀ w₀
  · obtain ⟨r, w₀, hw01, hw04, hv0w0⟩ := hex
    by_cases hhit3 : ∃ w₃ : V, G.Adj w₃ (c (r + 4)) ∧ G.Adj w₃ (c (r + 2)) ∧ G.Adj v₀ w₃
    · -- v₀ hits A_{r+3}, so by (P1) it avoids A_{r+2}; reverse c to c'(k) := c(-k)!
      obtain ⟨w₃, hw34, hw32, hv0w3⟩ := hhit3
      let c' : Fin 5 → V := fun k => c (-k)
      have hc'_adj : ∀ k : Fin 5, G.Adj (c' k) (c' (k + 1)) := fun k => by
        dsimp only [c']
        have h := (hc_adj (-(k + 1))).symm
        rwa [fin5_neg_add] at h
      have hv0_c' : ∀ k : Fin 5, ¬ G.Adj v₀ (c' k) := fun k => hv0_c (-k)
      apply hfinish c' hc'_adj hv0_c' (-r) w₀
        (by dsimp only [c']; rwa [fin5_neg_neg_1])
        (by dsimp only [c']; rwa [fin5_neg_neg_4])
        hv0w0
      intro w hw1 hw2 hv0w
      dsimp only [c'] at hw1 hw2
      rw [fin5_neg_neg_4] at hw1
      rw [fin5_neg_neg_2] at hw2
      have e45 : G.Adj (c (r + 3)) (c (r + 4)) := by have h := hc_adj (r + 3); rwa [fin5_add_3_1] at h
      have e56 : G.Adj (c (r + 4)) (c r) := by have h := hc_adj (r + 4); rwa [fin5_add_4_1] at h
      have e70 : G.Adj (c (r + 1)) (c (r + 2)) := by have h := hc_adj (r + 1); rwa [fin5_add_1_1] at h
      have e04 : G.Adj (c (r + 2)) (c (r + 3)) := by have h := hc_adj (r + 2); rwa [fin5_add_2_1] at h
      exact hV8_contra (c (r + 2)) w₃ v₀ w (c (r + 3)) (c (r + 4)) (c r) (c (r + 1))
        hw32.symm hv0w3.symm hv0w hw2 e45 e56 (hc_adj r) e70 e04 hw34 hw1
    · push Not at hhit3
      exact hfinish c hc_adj hv0_c r w₀ hw01 hw04 hv0w0 hhit3
  · -- N(v₀) ⊆ B, contradicting 4n < 11 * d(v₀) <= 11 * #B < 2n!
    push Not at hex
    have hB_bound := hB_bound_any c hc_adj
    have hsubB : Finset.univ.filter (G.Adj v₀) ⊆
        Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4)))) := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i ⟨h1, h2⟩ => hex i w h1 h2 (Finset.mem_filter.mp hw).2⟩
    have hleB := Finset.card_le_card hsubB
    have hdv0 := hdeg v₀
    omega


/-- Helper: consecutive And(3) adjacency in Fin 8 matches the modular And(3) condition. -/
lemma fin8_and3_mod (a b : Fin 8) (h : b = a + 3 ∨ b = a + 4 ∨ b = a + 5) :
    3 ≤ (b.val + (3 * 3 - 1) - a.val) % (3 * 3 - 1) ∧
    (b.val + (3 * 3 - 1) - a.val) % (3 * 3 - 1) < 2 * 3 := by
  fin_cases a <;> fin_cases b <;> simp at h <;> decide

/-- Theorem H: Every counterexample has a vertex of degree at most 4n/11 (11 * δ(G) <= 4 * n). -/
theorem exists_deg_le_four_elevenths {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ∃ v : V, 11 * (G.neighborSet v).ncard ≤ 4 * Fintype.card V := by
  classical
  by_contra hgt
  push Not at hgt
  obtain ⟨M, hGM, hMTF, hMmax⟩ := exists_maximal_triangleFree G hTF
  have hMH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (M.induce V').edgeSet.ncard > Fintype.card V ^ 2 := by
    intro V' hV'
    have hG' := hH V' hV'
    have hsub : (G.induce V').edgeSet ⊆ (M.induce V').edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b => exact hGM he
    have hle : (G.induce V').edgeSet.ncard ≤ (M.induce V').edgeSet.ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hM11d : ∀ x : V, 4 * Fintype.card V < 11 * (M.neighborSet x).ncard := by
    intro x
    have h1 := hgt x
    have hle : (G.neighborSet x).ncard ≤ (M.neighborSet x).ncard :=
      Set.ncard_le_ncard (fun y hy => hGM hy) (Set.toFinite _)
    omega
  by_cases hV8 : ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → M.Adj (v i) (v j)
  · obtain ⟨v, hv⟩ := hV8
    obtain ⟨φ, hφ⟩ := hom_v8_of_contains_v8_minus_e M hMTF hM11d v hv
    exact not_hom_andrasfai M hMH (fun H hHTF hHH => five_mul_edges_lt_sq H hHTF hHH) 3 (by decide) φ
      (fun x y hxy => fin8_and3_mod (φ x) (φ y) (hφ x y hxy))
  · have hM5a : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ M.Adj u v) → 5 * #I < 2 * Fintype.card V := by
      intro I hI
      have h1 := five_mul_indep_lt_two_mul_card M hMTF hMH (I : Set V)
        (fun u hu v hv _ => hI u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv))
      rwa [Set.ncard_coe_finset] at h1
    have hM3col : M.Colorable 3 := colorable_three_of_no_v8_minus_e M hMTF hMmax hM5a hM11d hV8
      (fun _ _ H h1 h2 => exists_shortest_odd_walk_of_nonbip H h1 h2)
      (fun _ _ H _ h1 {_} h2 h3 h4 {_} h5 h6 w => shortest_odd_walk_deg_le_two H h1 h2 h3 h4 h5 h6 w)
    have hM3d : ∀ x : V, Fintype.card V < 3 * (M.neighborSet x).ncard := by
      intro x
      have h1 := hM11d x
      have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
      omega
    exact not_colorable_three_of_gt_third M hMTF hMH hM3d hM3col

end CoreLemmas

theorem main : H1 → H2 → H3 → type_of% @Erdos128.erdos_128 := by
  intro hH1 hH2 hH3 V _ G hH hTF
  have hn12 : 12 ≤ Fintype.card V := twelve_le_card G hTF hH
  have h800 : 73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard := eight_hundred_mul_edges_gt G hTF hH
  have h500k : 500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 :=
    five_hundred_thousand_mul_edges_lt G hTF hH
  have h5a : ∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V :=
    five_mul_indep_lt_two_mul_card G hTF hH
  have hC4 := exists_fourCycle G hTF hH
  have hC5 := exists_fiveCycle G hTF hH
  have h2K2 := exists_induced_twoK2 G hTF hH
  have h11d := exists_deg_le_four_elevenths G hTF hH
  by_cases h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard
  · have h3 : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard := fun v => by
      have := h14 v; omega
    have hnot3 := not_colorable_three_of_gt_third G hTF hH h3
    exact hH1 V G hn12 h800 h500k h5a hC4 hC5 h2K2 hnot3 h14 h11d hH hTF
  · push Not at h14
    by_cases h3 : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard
    · have hnot3 := not_colorable_three_of_gt_third G hTF hH h3
      exact hH2 V G hn12 h800 h500k h5a hC4 hC5 h2K2 hnot3 h3 h14 hH hTF
    · push Not at h3
      exact hH3 V G hn12 h800 h500k h5a hC4 hC5 h2K2 h3 hH hTF

end OMA.R_Erdos128_erdos_128_R2
