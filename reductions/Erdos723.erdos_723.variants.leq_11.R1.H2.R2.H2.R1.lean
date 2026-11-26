import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2

/-! The weight-fifteen case as the compatible-star search of Denniston. -/

-- Reduction Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H2.R1 of step Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H2
-- Credit: @avivorly

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1

open Finset

-- Weight fifteen in the binary row code produces the incidence pattern.
def H1 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let word : (Fin 111 → ZMod 2) → Fin 112 → ZMod 2 := fun a =>
      Fin.cons (∑ l, a l) (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))
    (∃ a, hammingNorm (fun p : Fin 111 => word a p.succ) = 15) →
    let matching := fun (L : Finset (Fin 111)) (M : Finset (Finset (Fin 111))) =>
      M.card = 3 ∧ (∀ e ∈ M, e ⊆ L ∧ e.card = 2) ∧ ∀ l ∈ L, ∃! e, e ∈ M ∧ l ∈ e
    let exterior := fun (L : Finset (Fin 111)) (C : Finset (Finset (Finset (Fin 111)))) =>
      C.card = 2 ∧ (∀ M ∈ C, matching L M) ∧ ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N
    ∃ L : Finset (Fin 111), L.card = 6 ∧
      ∃ stars : ↥(L.powersetCard 2) → Fin 6 → Finset (Finset (Finset (Finset (Fin 111)))),
        (∀ e i C, C ∈ stars e i → exterior L C ∧ ∀ M ∈ C, e.val ∉ M) ∧
        (∀ e i M, matching L M → e.val ∉ M → ∃! C, C ∈ stars e i ∧ M ∈ C) ∧
        (∀ e C, exterior L C → (∀ M ∈ C, e.val ∉ M) → ∃! i, C ∈ stars e i) ∧
        ∀ e f, e ≠ f → ∀ i j, (stars e i ∩ stars f j).card ≤ 1

-- The finite search rules out the pattern of partitions and compatible matchings.
def H2 : Prop :=
  ¬ (
    let matching := fun (L : Finset (Fin 111)) (M : Finset (Finset (Fin 111))) =>
      M.card = 3 ∧ (∀ e ∈ M, e ⊆ L ∧ e.card = 2) ∧ ∀ l ∈ L, ∃! e, e ∈ M ∧ l ∈ e
    let exterior := fun (L : Finset (Fin 111)) (C : Finset (Finset (Finset (Fin 111)))) =>
      C.card = 2 ∧ (∀ M ∈ C, matching L M) ∧ ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N
    ∃ L : Finset (Fin 111), L.card = 6 ∧
      ∃ stars : ↥(L.powersetCard 2) → Fin 6 → Finset (Finset (Finset (Finset (Fin 111)))),
        (∀ e i C, C ∈ stars e i → exterior L C ∧ ∀ M ∈ C, e.val ∉ M) ∧
        (∀ e i M, matching L M → e.val ∉ M → ∃! C, C ∈ stars e i ∧ M ∈ C) ∧
        (∀ e C, exterior L C → (∀ M ∈ C, e.val ∉ M) → ∃! i, C ∈ stars e i) ∧
        ∀ e f, e ≠ f → ∀ i j, (stars e i ∩ stars f j).card ≤ 1)

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2.H2 := by
  intro pattern impossible incidence rowSizes columnSizes rowPairs columnPairs
  dsimp only
  intro weightFifteen
  exact impossible (pattern incidence rowSizes columnSizes rowPairs columnPairs weightFifteen)

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1
