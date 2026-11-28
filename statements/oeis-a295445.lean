import Mathlib

/-!
# OEIS A295445: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295445 (OEIS Foundation, CC BY-SA 4.0).

Entry A295445, offset 0: a(n) = (18*n)!*(2*n)!/((9*n)!*(6*n)!*(5*n)!).
Data: 1,408408,802241960520,1823169705017624880,4396944340992842923469640,10954213672604884898541157653408,27856219773497860095974794307896603536,71846723613356502547294848257330357588794200,187234481335648875117449455455153824826269008835400

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, a(n/3) = (6*n)!*(2*n/3)!/((3*n)!*(2*n)!*(5*n/3)!) is an integer, where
fractional factorials are defined using the Gamma function; for example, (2*n/3)! := Gamma(2*n/3
+ 1). See A364175. - Peter Bala, Jun 13 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* The conjectured quantity is written exactly as in the comment, with n a natural number cast
  to the reals and the arguments such as 5*n/3 computed in the reals (no rounding).
  Integrality is stated as equality with the cast of some integer z, for every n >= 0.
* For n divisible by 3 the quantity is the entry's own term a(m) =
  (18*m)!(2*m)!/((9*m)!(6*m)!(5*m)!), so only the remaining residues are new.
  With this reading a(m) for m = 0, 1, ... reproduces all 9 listed terms (checked with
  exact rational arithmetic), and the conjectured quantity is an integer for every n < 300
  (checked the same way: each Gamma value at a non-integer point cancels against one with
  the same fractional part).
-/

namespace OMA.S_oeis_a295445

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295445. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (6 * (n : ℝ)) * ffact (2 * (n : ℝ) / 3) / (ffact (3 * (n : ℝ)) * ffact (2 * (n : ℝ)) * ffact (5 * (n : ℝ) / 3)) = z := by
  sorry

end OMA.S_oeis_a295445
