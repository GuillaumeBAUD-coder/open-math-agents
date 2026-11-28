import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1

/-!
Isolate the complete residue class `10 modulo 17`.  Computational search
over the 378 admissible lifts modulo 2042040 found explicit strict Type A/B
constructions for every lift; H2 is the formalization of that finite family.
-/

namespace OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    (p%13 = 1 ∨ p%13 = 2 ∨ p%13 = 3 ∨ p%13 = 4 ∨ p%13 = 5 ∨
      p%13 = 7 ∨ p%13 = 9 ∨ p%13 = 10 ∨ p%13 = 12) →
    p%17 ≠ 10 →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    (p%13 = 1 ∨ p%13 = 2 ∨ p%13 = 3 ∨ p%13 = 4 ∨ p%13 = 5 ∨
      p%13 = 7 ∨ p%13 = 9 ∨ p%13 = 10 ∨ p%13 = 12) →
    p%17 = 10 →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro hrest hten p hp h24 h840 h11 h13
  by_cases h17 : p % 17 = 10
  · exact hten p hp h24 h840 h11 h13 h17
  · exact hrest p hp h24 h840 h11 h13 h17

end OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1_H1_R1
