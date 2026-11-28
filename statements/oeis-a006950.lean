import Mathlib

/-!
# The partition generating function A006950 and Omar Pol's two arrays

Source: https://oeis.org/A006950, conjecture of Omar E. Pol (October 9, 2011).
The program in https://oeis.org/A195825 defines column 2 by the triangular shifts
with signs +,+,-,- repeated. The columns of https://oeis.org/A195836 start
in triangular-numbered rows, as in A195826 and the signed construction in A175003.
Array A195825 starts in row 0. Triangle A195836 starts in row 1.
OEIS text and data © OEIS Foundation Inc., CC BY-SA 4.0.
Credit: @connoranderson
-/

namespace OMA.S_oeis_a006950

open Finset Polynomial

/-- The Euler product for A006950, truncated sufficiently far to read coefficient n.
Odd parts can occur once and even parts can repeat. -/
noncomputable def genPoly (n : ℕ) : ℤ[X] :=
  ∏ i ∈ range n, ((1 + X ^ (2*i+1)) *
    (∑ r ∈ range (n+1), X ^ (2*(i+1)*r)))

noncomputable def a (n : ℕ) : ℤ := (genPoly n).coeff n

def tri (k : ℕ) : ℕ := k * (k+1) / 2

/-- At positive column indices these signs run +,+,-,- in groups of four. -/
def sign (k : ℕ) : ℤ := - ((-1 : ℤ) ^ tri k)

/-- Column 2 of the square array A195825, following the entry's recurrence.
Here j+1 is the one-based index of a triangular shift. -/
def col2 : ℕ → ℤ
  | 0 => 1
  | n+1 => ∑ j ∈ range (n+1),
      if _h : 0 < tri (j+1) ∧ tri (j+1) ≤ n+1 then
        sign (j+1) * col2 (n+1-tri (j+1)) else 0
termination_by n => n
decreasing_by omega

/-- Column k of triangle A195836 begins at row tri k. Absent entries are zero. -/
def entry (n k : ℕ) : ℤ :=
  if 0 < k ∧ tri k ≤ n then sign k * col2 (n-tri k) else 0

theorem main : a 0 = 1 ∧ ∀ n : ℕ,
    a (n+1) = (∑ j ∈ range (n+1), entry (n+1) (j+1)) ∧
    a n = entry (n+1) 1 ∧ a n = col2 n := by
  sorry

end OMA.S_oeis_a006950
