import Mathlib

/-!
# A265225: Cumulative ON-cell counts in Rule 54

Sources: https://oeis.org/A265225 and https://oeis.org/A093353
(OEIS Foundation, CC BY-SA 4.0).

The automaton starts with just the cell at position zero ON and uses
Wolfram rule 54. The sequence counts all ON cells in rows 0 through n,
as in the OEIS examples and program. We state Colin Barker's three
formulas, Wesley Ivan Hurt's formula with a floor, and Matej Veselovac's
identity with A093353. Its published formula defines the latter sequence
independently of the automaton. The recurrence uses integer arithmetic.
The generating-function denominator has constant coefficient one.
-/

namespace OMA.S_oeis_a265225

def ruleOut (l c r : Bool) : Bool := (54 : ℕ).testBit (4*l.toNat + 2*c.toNat + r.toNat)

def cell : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n+1, i => ruleOut (cell n (i-1)) (cell n i) (cell n (i+1))

def onCount (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2*n+1), if cell n ((j : ℤ)-n) then 1 else 0

def a (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n+1), onCount j

def a093353 (n : ℕ) : ℕ := (n + n%2) * (n+1) / 2

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℚ) = ((n : ℚ)+1)*(2*(n : ℚ)-(-1 : ℚ)^n+5)/4) ∧
    (∀ n : ℕ, 5 ≤ n → a n = a (n-1) + 2*a (n-2) - 2*a (n-3) - a (n-4) + a (n-5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1-X)^3*(1+X)^2 : ℚ⟦X⟧) = 1+3*X) ∧
    (∀ n : ℕ, a n = (n : ℤ)+1+((n : ℤ)+1)*(((n+1)/2 : ℕ) : ℤ)) ∧
    (∀ n : ℕ, a n = (a093353 n : ℤ) + n + 1) := by
  sorry

end OMA.S_oeis_a265225
