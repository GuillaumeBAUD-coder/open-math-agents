import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1
import Mathlib

-- Step Arxiv.2507.17780.tx_graffiti_conjecture_1.R1.H2: hypothesis H2 of reduction Arxiv.2507.17780.tx_graffiti_conjecture_1.R1
-- Credit: @ivillar
--
-- The Caro-Wei bound, by strong induction on a vertex set W: take v in W of minimum degree
-- inside W, put v in the independent set and recurse on the vertices of W that are neither v nor
-- adjacent to v. The closed neighbourhood of v contributes at most 1 to the sum, and removing it
-- only lowers degrees of the remaining vertices.

namespace OMA.CaroWei

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Degree of x inside the vertex set W. -/
def dg (W : Finset V) (x : V) : ℕ := #(W.filter (G.Adj x))

lemma dg_mono {W W' : Finset V} (h : W' ⊆ W) (x : V) : dg G W' x ≤ dg G W x :=
  card_le_card (filter_subset_filter _ h)

lemma cw : ∀ k, ∀ W : Finset V, #W = k →
    ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧
      (∑ x ∈ W, (1 : ℝ) / ((dg G W x : ℝ) + 1)) ≤ #I := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W hWk
  rcases W.eq_empty_or_nonempty with hW | hW
  · exact ⟨∅, empty_subset _, by simp, by simp [hW]⟩
  obtain ⟨v, hvW, hvmin⟩ := W.exists_min_image (dg G W) hW
  set W' := W.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) with hW'
  have hW'W : W' ⊆ W := filter_subset _ _
  have hvW' : v ∉ W' := by simp [hW']
  have hcard : #W' < k := by
    rw [← hWk]
    exact card_lt_card ⟨hW'W, fun h => hvW' (h hvW)⟩
  obtain ⟨I', hI'W', hI'ind, hI'bound⟩ := ih #W' hcard W' rfl
  have hvI' : v ∉ I' := fun h => hvW' (hI'W' h)
  refine ⟨insert v I', ?_, ?_, ?_⟩
  · exact insert_subset hvW (hI'W'.trans hW'W)
  · rw [coe_insert]
    exact hI'ind.insert fun x hx _ => ⟨(mem_filter.mp (hI'W' hx)).2.2, fun h => (mem_filter.mp (hI'W' hx)).2.2 h.symm⟩
  · rw [card_insert_of_notMem hvI']
    push_cast
    have hsplit := sum_filter_add_sum_filter_not W (fun x => x = v ∨ G.Adj v x)
      (fun x => (1 : ℝ) / ((dg G W x : ℝ) + 1))
    have hnot : W.filter (fun x => ¬ (x = v ∨ G.Adj v x)) = W' := by
      rw [hW']
      congr 1
      ext x
      simp only [not_or]
    rw [hnot] at hsplit
    rw [← hsplit]
    have hA : ∑ x ∈ W.filter (fun x => x = v ∨ G.Adj v x), (1 : ℝ) / ((dg G W x : ℝ) + 1)
        ≤ 1 := by
      have hle : ∀ x ∈ W.filter (fun x => x = v ∨ G.Adj v x),
          (1 : ℝ) / ((dg G W x : ℝ) + 1) ≤ 1 / ((dg G W v : ℝ) + 1) := by
        intro x hx
        have := hvmin x (mem_filter.mp hx).1
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right this 1
      calc _ ≤ ∑ x ∈ W.filter (fun x => x = v ∨ G.Adj v x), (1 : ℝ) / ((dg G W v : ℝ) + 1) :=
            sum_le_sum hle
        _ = #(W.filter (fun x => x = v ∨ G.Adj v x)) * (1 / ((dg G W v : ℝ) + 1)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ((dg G W v : ℝ) + 1) * (1 / ((dg G W v : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hsub : W.filter (fun x => x = v ∨ G.Adj v x) ⊆ insert v (W.filter (G.Adj v)) := by
              intro x hx
              rcases (mem_filter.mp hx).2 with h | h
              · exact h ▸ mem_insert_self _ _
              · exact mem_insert_of_mem (mem_filter.mpr ⟨(mem_filter.mp hx).1, h⟩)
            have := (card_le_card hsub).trans (card_insert_le _ _)
            have h2 : (#(W.filter (fun x => x = v ∨ G.Adj v x)) : ℝ) ≤ #(W.filter (G.Adj v)) + 1 := by
              exact_mod_cast this
            unfold dg
            exact h2
        _ = 1 := by field_simp
    have hB : ∑ x ∈ W', (1 : ℝ) / ((dg G W x : ℝ) + 1) ≤
        ∑ x ∈ W', (1 : ℝ) / ((dg G W' x : ℝ) + 1) := by
      apply sum_le_sum
      intro x _
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right (dg_mono G hW'W x) 1
    linarith

end OMA.CaroWei

theorem OMA.solution : OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1.H2 := by
  unfold OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1.H2
  intro V _ G _
  classical
  obtain ⟨I, -, hI, hbound⟩ := OMA.CaroWei.cw G _ Finset.univ rfl
  have hdeg : ∀ v, (OMA.CaroWei.dg G Finset.univ v : ℝ) = G.degree v := by
    intro v
    unfold OMA.CaroWei.dg
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  simp only [hdeg] at hbound
  exact hbound.trans (by exact_mod_cast hI.card_le_indepNum)
