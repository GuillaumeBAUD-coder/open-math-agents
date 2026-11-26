import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1
import Mathlib.InformationTheory.Hamming

/-! The codeword cases for order ten using the exact weight-nineteen count. -/

-- Reduction Erdos723.erdos_723.variants.leq_11.R1.H2.R2 of step Erdos723.erdos_723.variants.leq_11.R1.H2
-- Credit: @avivorly

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2

open Finset

-- A hypothetical plane supplies a binary codeword in one of the three cases.
def H1 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let word : (Fin 111 → ZMod 2) → Fin 112 → ZMod 2 := fun a =>
      Fin.cons (∑ l, a l) (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))
    let weight := fun a => hammingNorm (fun p : Fin 111 => word a p.succ)
    ∃ a, weight a = 15 ∨ weight a = 16 ∨
      (weight a = 19 ∧ ∀ b c, weight b < 19 → weight c < 19 → word a ≠ word b + word c)

-- The weight-fifteen exclusion.
def H2 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let word : (Fin 111 → ZMod 2) → Fin 112 → ZMod 2 := fun a =>
      Fin.cons (∑ l, a l) (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))
    let weight := fun a => hammingNorm (fun p : Fin 111 => word a p.succ)
    ¬ ∃ a, weight a = 15

-- The weight-sixteen exclusion.
def H3 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let word : (Fin 111 → ZMod 2) → Fin 112 → ZMod 2 := fun a =>
      Fin.cons (∑ l, a l) (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))
    let weight := fun a => hammingNorm (fun p : Fin 111 => word a p.succ)
    ¬ ∃ a, weight a = 16

-- A primitive weight-nineteen word is not a sum of two lighter codewords.
def H4 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let word : (Fin 111 → ZMod 2) → Fin 112 → ZMod 2 := fun a =>
      Fin.cons (∑ l, a l) (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))
    let weight := fun a => hammingNorm (fun p : Fin 111 => word a p.succ)
    ¬ ∃ a, weight a = 19 ∧ ∀ b c, weight b < 19 → weight c < 19 → word a ≠ word b + word c

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1.H2 := by
  intro required noSmall noSixteen noPrimitive incidence rowSizes columnSizes rowPairs columnPairs
  obtain ⟨a, w15 | w16 | w19⟩ := required incidence rowSizes columnSizes rowPairs columnPairs
  · exact noSmall incidence rowSizes columnSizes rowPairs columnPairs ⟨a, w15⟩
  · exact noSixteen incidence rowSizes columnSizes rowPairs columnPairs ⟨a, w16⟩
  · exact noPrimitive incidence rowSizes columnSizes rowPairs columnPairs ⟨a, w19⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2
