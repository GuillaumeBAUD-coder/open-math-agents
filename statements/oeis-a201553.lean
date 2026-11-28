import Mathlib

/-!
# OEIS A201553: Barker's generating function and recurrence

Source: https://oeis.org/A201553
Credit: @xor2k

Entry: Number of arrays of 6 integers in -n..n with sum zero. (The entry now has offset 0, a(0) = 1
having been prepended; Barker's g.f. has no constant term and describes the terms with n >= 1.)
The formula section states:
  Conjectures from Colin Barker, May 23 2018: G.f.: x*(141 + 905*x + 940*x^2 + 120*x^3 + 7*x^4 -
  x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6).

Conventions:
* An array is a function x : Fin 6 → ℤ, the array x(0..5). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`) and zero sum; `a n` is its
  cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (the terms with n >= 1, so the constant term is 0), stated as
  A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* The recurrence is stated in the integers for every n > 6, that is for every n for which all of
  a(n-1), ..., a(n-6) are terms of the offset 1 sequence (the range in which a recurrence of
  order 6 for an offset 1 sequence is meaningful, and the one the g.f. gives).
* `main` is the conjunction of Barker's two conjectures, in the entry's order.

Numerical check: a Python copy of the definition (brute force over the (2n+1)^6 arrays) gives
a(1..6) = 141, 1751, 9331, 32661, 88913, 204763. The OEIS DATA field was not available offline;
the first five values agree with the terms of the entry as recalled.
-/

namespace OMA.S_oeis_a201553

open PowerSeries

/-- The arrays x(0..5) of 6 integers in -n..n with sum zero. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 6 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 6 => Finset.Icc (-(n : ℤ)) n).filter fun x => ∑ i, x i = 0

/-- A201553(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (141 + 905 * X + 940 * X ^ 2 + 120 * X ^ 3 + 7 * X ^ 4 - X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a201553
