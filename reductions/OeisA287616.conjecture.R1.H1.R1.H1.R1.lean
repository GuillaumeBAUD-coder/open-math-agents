import OMAReductions.R_OeisA287616_conjecture_R1_H1_R1
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! Split the two-class genus representation at the real and finite places.
The inputs are from Cao, Guo, Qiu, Feng and Gao, arXiv:2606.26035, Section 3.
The real place is discharged directly. The finite places are split at 2, 3
and 5, the prime divisors of twice the determinant of the diagonal form. -/

namespace OMA.R_OeisA287616_conjecture_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ (n p : ℕ) [Fact p.Prime], p ∣ 30 →
    ∃ a b c : ℤ_[p],
      15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[p]) + 23 ∧
        (IsUnit a ∨ IsUnit b ∨ IsUnit c)

def H2 : Prop :=
  ∀ (n p : ℕ) [Fact p.Prime], ¬p ∣ 30 →
    ∃ a b c : ℤ_[p],
      15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[p]) + 23 ∧
        (IsUnit a ∨ IsUnit b ∨ IsUnit c)

def H3 : Prop :=
  ∀ m : ℤ,
    (∃ a b c : ℝ, 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℝ)) →
    (∀ (p : ℕ) [Fact p.Prime], ∃ a b c : ℤ_[p],
      15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℤ_[p]) ∧
        (IsUnit a ∨ IsUnit b ∨ IsUnit c)) →
    (∃ u v w : ℤ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = m ∧
      Int.gcd u (Int.gcd v w) = 1) ∨
    (∃ x y z : ℤ, 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = m ∧
      Int.gcd x (Int.gcd y z) = 1)

theorem main : H1 → H2 → H3 → OMA.R_OeisA287616_conjecture_R1_H1_R1.H1 := by
  intro hsmall hlarge hgenus n
  apply hgenus (120 * (n : ℤ) + 23)
  · push_cast
    refine ⟨Real.sqrt ((120 * (n : ℝ) + 23) / 15), 0, 0, ?_⟩
    rw [Real.sq_sqrt (by positivity)]
    ring
  · intro p hp
    push_cast
    by_cases hd : p ∣ 30
    · exact hsmall n p hd
    · exact hlarge n p hd

end OMA.R_OeisA287616_conjecture_R1_H1_R1_H1_R1
