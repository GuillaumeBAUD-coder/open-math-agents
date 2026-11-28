import Mathlib

/-!
# A004485: Sprague-Grundy values for game of Wyt Queens.

Conjectures from Chai Wah Wu, Apr 05 2021.
Source: https://oeis.org/A004485
Move rules and row indexing: https://oeis.org/A004481
Credit: @tczyzycki

A004485 is row 4 (zero-indexed) of table A004481, the Sprague-Grundy table
for Wythoff's game (Wyt Queens), with offset 0.
-/

namespace OMA.S_oeis_a004485

/-- A move in Wythoff's game reduces either coordinate, or both by the same positive amount. -/
def Move (a b c d : ℕ) : Prop :=
  (c < a ∧ d = b) ∨ (c = a ∧ d < b) ∨
    ∃ t : ℕ, 0 < t ∧ c + t = a ∧ d + t = b

/-- At each position the Sprague-Grundy value is the least natural number absent from its
    options. This specification determines the table uniquely by induction on `a + b`. -/
def IsGrundy (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b : ℕ,
    (∀ c d : ℕ, Move a b c d → g c d ≠ g a b) ∧
    (∀ m : ℕ, m < g a b → ∃ c d : ℕ, Move a b c d ∧ g c d = m)

/-- The zero-indexed row with first coordinate 4 gives A004485. The conjectured
    generating-function identity is written after multiplying by its denominator
    `x^13 - x^12 - x + 1`, whose constant coefficient is 1. -/
theorem main : ∀ g : ℕ → ℕ → ℕ, IsGrundy g →
    (∀ n : ℕ, 21 < n →
      (g 4 n : ℤ) = (g 4 (n - 1) : ℤ) + (g 4 (n - 12) : ℤ) - (g 4 (n - 13) : ℤ)) ∧
    (let x : PowerSeries ℚ := PowerSeries.X
     let a : PowerSeries ℚ := PowerSeries.mk (fun n => (g 4 n : ℚ))
     a * (x^13 - x^12 - x + 1) =
       -8*x^21 + 6*x^20 + 6*x^19 - 4*x^18 + 4*x^16 - 4*x^15 + x^14 + 4*x^13 -
         5*x^12 - x^11 + 5*x^10 + 7*x^9 + x^8 - 9*x^7 + 3*x^6 - x^5 + 5*x^4 -
         x^3 - 2*x^2 + x + 4) := by
  sorry

end OMA.S_oeis_a004485
