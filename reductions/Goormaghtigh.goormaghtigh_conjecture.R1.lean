import FormalConjectures.Wikipedia.Goormaghtigh

-- Reduction Goormaghtigh.goormaghtigh_conjecture.R1 of The Goormaghtigh conjecture
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- A Goormaghtigh number N is a repunit with at least three digits in two distinct bases:
-- N = repunit x m = repunit y n. The split follows the known partial results.
--   H1 (known): one representation has exactly three digits and the other an odd number n of
--       digits. This is the theorem of P. Yuan, On the diophantine equation
--       (x^3 - 1)/(x - 1) = (y^n - 1)/(y - 1), J. Number Theory 112 (2005) 20-25, whose only
--       solutions are 31 = repunit 5 3 = repunit 2 5 and 8191 = repunit 90 3 = repunit 2 13.
--       (For n = 3 the bases would coincide, so the case is empty.)
--   H2 (open): one representation has exactly three digits and the other an even number.
--       If the other base y is odd the right side is even while x^2 + x + 1 is odd, so only
--       even y remains.
--   H3 (open): both representations have at least four digits.
-- main sorts a Goormaghtigh number into one of these three cases, using the symmetry of the
-- definition to put the three-digit representation first.

namespace OMA.R_Goormaghtigh_goormaghtigh_conjecture_R1

open Goormaghtigh

/-- Three digits against an odd number of digits (Yuan 2005). -/
def H1 : Prop :=
  ∀ x y n : ℕ, 2 ≤ x → 2 ≤ y → x ≠ y → 3 ≤ n → Odd n →
    Goormaghtigh.repunit x 3 = Goormaghtigh.repunit y n →
      Goormaghtigh.repunit x 3 = 31 ∨ Goormaghtigh.repunit x 3 = 8191

/-- Three digits against an even number of digits (open). -/
def H2 : Prop :=
  ∀ x y n : ℕ, 2 ≤ x → 2 ≤ y → x ≠ y → 3 ≤ n → Even n →
    Goormaghtigh.repunit x 3 = Goormaghtigh.repunit y n →
      Goormaghtigh.repunit x 3 = 31 ∨ Goormaghtigh.repunit x 3 = 8191

/-- At least four digits in both bases (open). -/
def H3 : Prop :=
  ∀ x y m n : ℕ, 2 ≤ x → 2 ≤ y → x ≠ y → 4 ≤ m → 4 ≤ n →
    Goormaghtigh.repunit x m = Goormaghtigh.repunit y n →
      Goormaghtigh.repunit x m = 31 ∨ Goormaghtigh.repunit x m = 8191

theorem main : H1 → H2 → H3 → type_of% @Goormaghtigh.goormaghtigh_conjecture := by
  intro h1 h2 h3 N hN
  obtain ⟨b₁, b₂, d₁, d₂, hb₁, hb₂, hne, hd₁, hd₂, e₁, e₂⟩ := hN
  have three : ∀ x y n : ℕ, 2 ≤ x → 2 ≤ y → x ≠ y → 3 ≤ n →
      Goormaghtigh.repunit x 3 = Goormaghtigh.repunit y n →
      Goormaghtigh.repunit x 3 = 31 ∨ Goormaghtigh.repunit x 3 = 8191 := by
    intro x y n hx hy hxy hn h
    rcases Nat.even_or_odd n with he | ho
    · exact h2 x y n hx hy hxy hn he h
    · exact h1 x y n hx hy hxy hn ho h
  by_cases c₁ : d₁ = 3
  · subst c₁
    subst e₁
    exact three b₁ b₂ d₂ hb₁ hb₂ hne hd₂ e₂.symm
  · by_cases c₂ : d₂ = 3
    · subst c₂
      subst e₂
      exact three b₂ b₁ d₁ hb₂ hb₁ (Ne.symm hne) hd₁ e₁.symm
    · subst e₁
      exact h3 b₁ b₂ d₁ d₂ hb₁ hb₂ hne (by omega) (by omega) e₂.symm

end OMA.R_Goormaghtigh_goormaghtigh_conjecture_R1
