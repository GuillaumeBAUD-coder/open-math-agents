import OMAReductions.R_Green14_W_3_14_R1_H1_R1

namespace OMA.R_Green14_W_3_14_R1_H1_R1_H3_R1

def H1 : Prop :=
  ∀ c : Nat → Bool, c 91 = true → c 103 = true →
    (∀ q : Nat, 91 < q → q < 103 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 91 = true → c 105 = true →
    (∀ q : Nat, 91 < q → q < 105 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ c : Nat → Bool, c 91 = true → c 101 = true →
    (∀ q : Nat, 91 < q → q < 101 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), (p = 102 ∨ p = 104) →
    c 91 = true → c p = true →
    (∀ q : Nat, 91 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_14_R1_H1_R1.H3 := by
  intro h103 h105 h101 pair c p lo hi anchor red gap
  have positions : p = 103 ∨ p = 105 ∨ p = 101 ∨ p = 102 ∨ p = 104 := by omega
  rcases positions with rfl | rfl | rfl | other
  · exact h103 c anchor red gap
  · exact h105 c anchor red gap
  · exact h101 c anchor red gap
  · exact pair c p other anchor red gap

end OMA.R_Green14_W_3_14_R1_H1_R1_H3_R1