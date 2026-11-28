import Mathlib

/-!
# OEIS A295468: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295468 (OEIS Foundation, CC BY-SA 4.0).

Entry A295468, offset 0: a(n) = (30*n)!*(5*n)!*(3*n)!*(2*n)!/((15*n)!*(10*n)!*(8*n)!*(6*n)!*n!).
Data: 1,2772725670,40337629723514950470,671214073076279711920414071900,11815915461993730897935386470911734090310,214599520915474479942307452790907076147031402434420,3975780607168011583140781349809187812166883920578195778723100

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, a(n/2) = (15*n)!*(5*n/2)!*(3*n/2)!*n! /
((15*n/2)!*(5*n)!*(4*n)!*(3*n)!*(n/2)!) is an integer, where fractional factorials are defined
using the Gamma function - for example, (5*n/2)! := Gamma(5*n/2 + 1). - Peter Bala, Jul 30 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* The conjectured quantity is written exactly as in the comment, with n a natural number cast
  to the reals and the arguments such as 5*n/2 computed in the reals (no rounding).
  Integrality is stated as equality with the cast of some integer z, for every n >= 0.
* For n divisible by 2 the quantity is the entry's own term a(m) =
  (30*m)!(5*m)!(3*m)!(2*m)!/((15*m)!(10*m)!(8*m)!(6*m)!m!), so only the remaining residues are new.
  With this reading a(m) for m = 0, 1, ... reproduces all 7 listed terms (checked with
  exact rational arithmetic), and the conjectured quantity is an integer for every n < 300
  (checked the same way: each Gamma value at a non-integer point cancels against one with
  the same fractional part).
-/

namespace OMA.S_oeis_a295468

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295468. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (15 * (n : ℝ)) * ffact (5 * (n : ℝ) / 2) * ffact (3 * (n : ℝ) / 2) * ffact ((n : ℝ)) / (ffact (15 * (n : ℝ) / 2) * ffact (5 * (n : ℝ)) * ffact (4 * (n : ℝ)) * ffact (3 * (n : ℝ)) * ffact ((n : ℝ) / 2)) = z := by
  sorry

end OMA.S_oeis_a295468
