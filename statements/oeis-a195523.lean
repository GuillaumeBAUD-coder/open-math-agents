import Mathlib

/-!
# Hardin's zero-margin lower triangular arrays

OEIS A195523 is the number of lower triangular 5 by 5 integer matrices
with entries in [-n,n] and all row and column sums zero. This is the fifth
row of A195522. The sequence has offset 1. At index zero its ordinary
generating function therefore has coefficient zero.

The independent coordinates below reconstruct every such matrix uniquely.
With column totals A,B,C after the first three rows, B=-A-C, the rows,
omitting entries above the diagonal, have the form
  (0), (t,-t), (A-t,B+t,C), (x,y,z,-x-y-z),
  (-A-x,-B-y,-C-z,x+y+z,0).
The top choices enforce the bounds on t,A-t,B+t. For a column total U,
the fourth-row entry lies between lo(n,U) and hi(n,U) to keep both that
entry and the last-row entry -U-x in [-n,n]. The bottom choices use its
nonnegative distance from lo(n,U), then test the last row-sum bound.

Sources: https://oeis.org/A195523 and https://oeis.org/A195522.
Credit: R. H. Hardin (sequence and computed data), Colin Barker
(conjectures, May 8, 2018), Robert Leshner (@rleshner, formalization).
-/

namespace OMA.S_oeis_a195523
open Finset

def lo (n U : ℤ) : ℤ := max (-n) (-n-U)
def hi (n U : ℤ) : ℤ := min n (n-U)

noncomputable def top (n A C : ℤ) : Finset ℤ :=
  Icc (max (-n) (max (A-n) (A+C-n))) (min n (min (A+n) (A+C+n)))

abbrev Triple := ℕ × ℕ × ℕ

def width (n U : ℤ) : ℕ := (hi n U-lo n U).toNat

def box (n A B C : ℤ) : Finset Triple :=
  (range (width n A+1)) ×ˢ ((range (width n B+1)) ×ˢ (range (width n C+1)))

def bottom (n A B C : ℤ) : Finset Triple :=
  (box n A B C).filter (fun v =>
    |lo n A+lo n B+lo n C+(v.1:ℤ)+v.2.1+v.2.2| ≤ n)

noncomputable def cell (n A C : ℤ) : ℕ := (top n A C).card * (bottom n A (-A-C) C).card

noncomputable def arrayCount (n : ℕ) : ℕ :=
  ∑ C ∈ Icc (-(n:ℤ)) n,
    ∑ A ∈ Icc (lo (2*n) C) (hi (2*n) C), cell n A C

noncomputable def a (n : ℕ) : ℤ := if n=0 then 0 else arrayCount n

/-- Hardin's empirical counting polynomial, followed by Barker's generating
function and recurrence at every claimed index. -/
theorem main :
    (∀ n : ℕ, (180:ℤ)*arrayCount n = 2572*(n:ℤ)^6+7716*(n:ℤ)^5+10825*(n:ℤ)^4+
      8790*(n:ℤ)^3+4423*(n:ℤ)^2+1314*(n:ℤ)+180) ∧
    ((1-PowerSeries.X)^7 * PowerSeries.mk a =
      PowerSeries.X*(199+2360*PowerSeries.X+5175*PowerSeries.X^2+2346*PowerSeries.X^3+
        213*PowerSeries.X^4-6*PowerSeries.X^5+PowerSeries.X^6)) ∧
    (∀ n : ℕ, 7 < n → a n = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+
      21*a (n-5)-7*a (n-6)+a (n-7)) := by
  sorry

end OMA.S_oeis_a195523
