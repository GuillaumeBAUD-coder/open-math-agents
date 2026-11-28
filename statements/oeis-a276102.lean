import Mathlib

/-!
# OEIS A276102: integrality of a fractional-index factorial ratio

Source: https://oeis.org/A276102 (OEIS Foundation, CC BY-SA 4.0).

Entry A276102, offset 0: a(n) = (6*n)!*(n/5)!/((3*n)!*(2*n)!*(6*n/5)!).
Data: 1,50,8250,1636250,349456250,77636318760,17672894531250,4089765214843750,957711284472656250,226280605806640625000,53837289804317953893960,12880759628253295898437500

The entry's own sequence is not known to be integral. Its comments:
Fractional factorials are defined in terms of the gamma function, for example, (n/5)! :=
Gamma(n/5 + 1).
This is only conjecturally an integer sequence. The similarly defined sequence
(6*n)!*floor(n/5)!/((3*n)!*(2*n)!*floor(6*n/5)!) = A211418(6*n) is integral.
Let u(n) = (30*n)!*n!/((15*n)!*(10*n)!*(6*n)!) = A211417(n). The three sequences u(1/2*n),
u(1/3*n) and u(1/5*n) appear to be integral (checked up to n = 200). This is the sequence
u(1/5*n). See A276100 ( u(1/2*n) ) and A276101 ( u(1/3*n) ).

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* The conjecture is that every term a(n), n >= 0, is an integer. a(n) is written exactly as
  in the name, with n a natural number cast to the reals and the arguments such as 6*n/5
  computed in the reals (no rounding).
* For n divisible by 5, a(n) = u(n/5) with u(m) = (30*m)!*m!/((15*m)!*(10*m)!*(6*m)!) =
  A211417(m), an integral factorial ratio, so only the remaining residues are new. With this
  reading a(n) reproduces all 12 listed terms (checked with exact rational arithmetic), and
  a(n) is an integer for every n < 300 (checked the same way: each Gamma value at a
  non-integer point cancels against one with the same fractional part).
-/

namespace OMA.S_oeis_a276102

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Integrality of the terms of OEIS A276102. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (6 * (n : ℝ)) * ffact ((n : ℝ) / 5) / (ffact (3 * (n : ℝ)) * ffact (2 * (n : ℝ)) * ffact (6 * (n : ℝ) / 5)) = z := by
  sorry

end OMA.S_oeis_a276102
