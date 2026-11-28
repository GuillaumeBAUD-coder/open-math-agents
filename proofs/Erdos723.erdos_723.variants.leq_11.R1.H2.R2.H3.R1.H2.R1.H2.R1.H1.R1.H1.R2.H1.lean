import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R2
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.IntervalCases

/-! With a single triple point, the number of covered points is the incidence
count minus the line-pair count plus one. -/

open Finset
open scoped BigOperators

private lemma sum_indicator_card {X : Type} (s : Finset X) (P : X → Prop)
    [DecidablePred P] : (∑ x ∈ s, if P x then (1 : ℕ) else 0) = (s.filter P).card := by
  rw [← Finset.sum_filter]
  simp

set_option maxRecDepth 8000 in
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R2.H1 := by
  classical
  intro E
  dsimp only
  intro rows meetings atMostThree oneTriple
  let incident (p : Fin 111) := univ.filter fun a : Fin 8 => E a p = true
  let pairs (p : Fin 111) := (incident p).powersetCard 2
  have on (a : Fin 8) (p : Fin 111) : a ∈ incident p ↔ E a p = true := by
    simp [incident]
  have incidenceCount : (∑ p : Fin 111, (incident p).card) = 88 := by
    calc
      _ = ∑ p : Fin 111, ∑ a : Fin 8, if E a p = true then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        exact (sum_indicator_card univ (fun a => E a p = true)).symm
      _ = ∑ a : Fin 8, ∑ p : Fin 111, if E a p = true then (1 : ℕ) else 0 := Finset.sum_comm
      _ = ∑ _a : Fin 8, (11 : ℕ) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [sum_indicator_card, rows]
      _ = 88 := by simp
  have disjoint : (↑(univ : Finset (Fin 111)) : Set (Fin 111)).PairwiseDisjoint pairs := by
    intro p _ q _ different
    change Disjoint (pairs p) (pairs q)
    rw [Finset.disjoint_left]
    intro t tp tq
    obtain ⟨onP, card⟩ := Finset.mem_powersetCard.mp tp
    have onQ := (Finset.mem_powersetCard.mp tq).1
    obtain ⟨a, b, ne, form⟩ := Finset.card_eq_two.mp card
    have ha : a ∈ t := form ▸ Finset.mem_insert_self _ _
    have hb : b ∈ t := form ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨_, _, alone⟩ := meetings a b ne
    exact different ((alone p ⟨(on a p).mp (onP ha), (on b p).mp (onP hb)⟩).trans
      (alone q ⟨(on a q).mp (onQ ha), (on b q).mp (onQ hb)⟩).symm)
  have complete : (univ : Finset (Fin 111)).biUnion pairs = (univ : Finset (Fin 8)).powersetCard 2 := by
    ext t
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, pairs, Finset.mem_powersetCard,
      Finset.subset_univ]
    constructor
    · rintro ⟨_, _, card⟩
      exact card
    · intro card
      obtain ⟨a, b, ne, form⟩ := Finset.card_eq_two.mp card
      obtain ⟨p, ⟨atA, atB⟩, _⟩ := meetings a b ne
      refine ⟨p, ?_, card⟩
      rw [form]
      exact Finset.insert_subset ((on a p).mpr atA) (Finset.singleton_subset_iff.mpr ((on b p).mpr atB))
  have pairCount : (∑ p : Fin 111, (incident p).card.choose 2) = 28 := by
    simp_rw [← Finset.card_powersetCard]
    change (∑ p : Fin 111, (pairs p).card) = 28
    rw [← Finset.card_biUnion disjoint, complete, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin] <;> decide
  have pointCount (d : ℕ) (bound : d ≤ 3) :
      (if 0 < d then 1 else 0) + d.choose 2 = d + (if d = 3 then 1 else 0) := by
    interval_cases d <;> decide
  have summed := Finset.sum_congr (s₁ := (univ : Finset (Fin 111))) rfl
    (fun p _ => pointCount (incident p).card (atMostThree p))
  have covered : (univ.filter fun p : Fin 111 => 0 < (incident p).card) =
      (univ.filter fun p : Fin 111 => ∃ a, E a p = true) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_pos, Finset.Nonempty, on]
  change (univ.filter fun p : Fin 111 => (incident p).card = 3).card = 1 at oneTriple
  simp only [Finset.sum_add_distrib, sum_indicator_card] at summed
  rw [pairCount, incidenceCount, oneTriple, covered] at summed
  omega
