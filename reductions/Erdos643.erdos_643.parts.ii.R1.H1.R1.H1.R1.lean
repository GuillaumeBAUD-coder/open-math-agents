import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H1_R1

-- Reduction Erdos643.erdos_643.parts.ii.R1.H1.R1.H1.R1 of step Erdos643.erdos_643.parts.ii.R1.H1.R1.H1
-- Credit: @hafidh561
--
-- The step is the pair-shadow Hall inequality for a family of triples: every subfamily has at most
-- as many edges as two-element subsets of its edges. This reduction splits it by the structural
-- dichotomy that the statement is built on: does the family contain two disjoint edges at all.
--
-- The two halves are different theorems, not one statement and its negation.
--  * H1 is the pairwise intersecting case. It does not use the hypothesis on repeated disjoint
--    unions at all (that hypothesis is vacuous there), and it is tight: the ten triples of a five
--    point set give ten edges and ten pairs, so any proof of H1 has to be exact.
--  * H2 is the case in which two disjoint edges exist. There the uniqueness of the disjoint-pair
--    decomposition of every six point set is the entire content: it is what rules out the
--    compressing configurations, so a proof of H2 has to use it essentially.
--
-- The glue below only needs that a subfamily inherits the two hypotheses, which is immediate for
-- uniformity and is proved below for the repeated disjoint union.

namespace OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1_H1_R1

open Finset

/-- H1: the pairwise intersecting case. No two distinct edges are disjoint, so the hypothesis on
repeated disjoint unions is vacuous; the bound is tight at the triples of a five point set. -/
def H1 : Prop := ∀ n : ℕ, ∀ F : Finset (Finset (Fin n)),
    (∀ e ∈ F, e.card = 3) → (∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ Disjoint A B) →
    F.card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard 2).filter fun p => ∃ e ∈ F, p ⊆ e).card

/-- H2: the case with two disjoint edges. The uniqueness of the disjoint-pair decomposition of each
six point set is the content here, and it has to be used. -/
def H2 : Prop := ∀ n : ℕ, ∀ F : Finset (Finset (Fin n)),
    (∀ e ∈ F, e.card = 3) → ¬ F.HasRepeatedDisjointUnion →
    (∃ A ∈ F, ∃ B ∈ F, Disjoint A B) →
    F.card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard 2).filter fun p => ∃ e ∈ F, p ⊆ e).card

/-- A repeated disjoint union inside a subfamily is one inside the family. -/
theorem repeated_of_subset {n : ℕ} {F H : Finset (Finset (Fin n))} (hFH : F ⊆ H)
    (h : F.HasRepeatedDisjointUnion) : H.HasRepeatedDisjointUnion := by
  obtain ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, hun, hne1, hne2, hne3, hne4, hne5, hne6⟩ := h
  exact ⟨A, hFH hA, B, hFH hB, C, hFH hC, D, hFH hD, hAB, hCD, hun,
    hne1, hne2, hne3, hne4, hne5, hne6⟩

theorem main : H1 → H2 → OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1.H1 := by
  intro h1 h2 n H huni hrdu F hFH
  have huniF : ∀ e ∈ F, e.card = 3 := fun e he => huni e (hFH he)
  have hruF : ¬ F.HasRepeatedDisjointUnion := fun hc => hrdu (repeated_of_subset hFH hc)
  by_cases hd : ∃ A ∈ F, ∃ B ∈ F, Disjoint A B
  · exact h2 n F huniF hruF hd
  · refine h1 n F huniF ?_
    intro A hA B hB _ hdisj
    exact hd ⟨A, hA, B, hB, hdisj⟩

end OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1_H1_R1
