import FormalConjectures.ErdosProblems.«743»
import Mathlib.Tactic

-- Reduction Erdos743.erdos_743.variants.almost_linear_degree.R1 of Erdős Problem 743 — almost linear degree
-- Credit: @Bondyboy2001
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R1

open Filter SimpleGraph
open scoped Classical

/-- The complete-host instance of the general tree-packing theorem of Allen, Böttcher,
Clemens, Hladký, Piguet, and Taraz, with a fixed margin around the medium-sized trees.
This permits arbitrary families of sizes, with only the total edge budget constrained. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (S : Finset ℕ) (T : (k : ℕ) → SimpleGraph (Fin k)),
      (∀ k ∈ S, 1 ≤ k ∧ k ≤ n ∧ (T k).IsTree) →
      (∀ k ∈ S, ((T k).maxDegree : ℝ) ≤ c * (n : ℝ) / Real.log (n : ℝ)) →
      (∑ k ∈ S, (T k).edgeFinset.card) ≤
        (⊤ : SimpleGraph (Fin n)).edgeFinset.card →
      5 * n ≤ 8 * (S.filter (fun k => n ≤ 8 * k ∧ 8 * k ≤ 7 * n)).card →
        Erdos743.IsPacking n (S : Set ℕ) T

/-- A full interval of tree sizes contains sufficiently many medium-sized trees. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
  5 * n ≤ 8 * ((Finset.Icc 2 n).filter
    (fun k => n ≤ 8 * k ∧ 8 * k ≤ 7 * n)).card

theorem medium_trees_eventually : H2 := by
  apply Filter.eventually_atTop.2
  refine ⟨64, ?_⟩
  intro n hn
  have hs : Finset.Icc (n / 8 + 1) (7 * n / 8) ⊆
      (Finset.Icc 2 n).filter (fun k => n ≤ 8 * k ∧ 8 * k ≤ 7 * n) := by
    intro k hk
    simp only [Finset.mem_Icc, Finset.mem_filter] at hk ⊢
    constructor
    · constructor <;> omega
    · constructor <;> omega
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  omega

theorem main : H1 → H2 → type_of% @Erdos743.erdos_743.variants.almost_linear_degree := by
  rintro ⟨c, hc, hpack⟩ hmedium
  refine ⟨c, hc, ?_⟩
  filter_upwards [hpack, hmedium] with n hp hm
  intro T hT
  have hpack' := hp (Finset.Icc 2 n) T
  have hcoe : ((Finset.Icc 2 n : Finset ℕ) : Set ℕ) = Set.Icc 2 n := by
    ext k
    simp
  rw [← hcoe]
  apply hpack'
  · intro k hk
    have hkn := Finset.mem_Icc.mp hk
    exact ⟨by omega, hkn.2, (hT k hkn).1⟩
  · intro k hk
    exact (hT k (Finset.mem_Icc.mp hk)).2
  · apply le_of_eq
    calc
      (∑ k ∈ Finset.Icc 2 n, (T k).edgeFinset.card)
          = ∑ k ∈ Finset.Icc 2 n, (k - 1) := by
              apply Finset.sum_congr rfl
              intro k hk
              have htree := (hT k (Finset.mem_Icc.mp hk)).1.card_edgeFinset
              simp only [Fintype.card_fin] at htree
              omega
      _ = n.choose 2 := Erdos743.sum_Icc_two_sub_one n
      _ = (⊤ : SimpleGraph (Fin n)).edgeFinset.card := by
        simpa using (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)).symm
  · exact hm

end OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R1
