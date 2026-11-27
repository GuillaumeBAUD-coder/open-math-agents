import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1

/-! Reduction Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.H2.R1.H3 -/
-- Credit: @sauronsoul-bit
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1

open Finset

def H1 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 3 ∧ 5 ≤ x ∧ x ≤ 6

def H2 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 4 ∧ x = 3

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1.H3 := by
  intro h1 h2
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1.H3
  dsimp only
  rintro ⟨M, h1_row, h2_col, h3_pair, h4_pair, h5_a, h6_b, h7_c, h8_inside, h9_outside, h10_three, counts⟩
  rcases counts with h_left | h_right
  · exact h1 ⟨M, h1_row, h2_col, h3_pair, h4_pair, h5_a, h6_b, h7_c, h8_inside, h9_outside, h10_three, h_left⟩
  · exact h2 ⟨M, h1_row, h2_col, h3_pair, h4_pair, h5_a, h6_b, h7_c, h8_inside, h9_outside, h10_three, h_right⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H3_R1
