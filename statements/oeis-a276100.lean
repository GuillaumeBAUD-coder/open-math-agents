import Mathlib

/-!
# OEIS A276100: integrality of a fractional-index factorial ratio

Source: https://oeis.org/A276100 (OEIS Foundation, CC BY-SA 4.0).

Entry A276100, offset 0: a(n) = (15*n)!*(n/2)!/((15*n/2)!*(5*n)!*(3*n)!).
Data: 1,114688,77636318760,62505037015810048,53837289804317953893960,48066503353826060675410034688,43880754270176401422739454033276880,40671547154451909281150562260837340282880,38113558705192522309151157825210540422513019720

The entry's own sequence is not known to be integral. Its comments:
Fractional factorials are defined in terms of the gamma function, for example, (n/2)! :=
gamma(n/2 + 1).
This is only conjecturally an integer sequence. The similarly defined sequence
(15*n)!*floor(n/2)!/(floor(15*n/2)!*(5*n)!*(3*n)!) = A211418(15*n) is integral.
Let u(n) = (30*n)!*n!/((15*n)!*(10*n)!*(6*n)!) = A211417(n). This sequence of ratios of
factorials is integral and was used by Chebyshev in his estimate of the number of primes less
than or equal to a fixed integer n. The three sequences u(1/2*n), u(1/3*n) and u(1/5*n) also
appear to be integral (checked up to n = 200). This is the sequence u(1/2*n). See A276101(
u(1/3*n) ) and A276102( u(1/5*n) ).

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* The conjecture is that every term a(n), n >= 0, is an integer. a(n) is written exactly as
  in the name, with n a natural number cast to the reals and the arguments such as 15*n/2
  computed in the reals (no rounding).
* For n divisible by 2, a(n) = u(n/2) with u(m) = (30*m)!*m!/((15*m)!*(10*m)!*(6*m)!) =
  A211417(m), an integral factorial ratio, so only the remaining residues are new. With this
  reading a(n) reproduces all 9 listed terms (checked with exact rational arithmetic), and
  a(n) is an integer for every n < 300 (checked the same way: each Gamma value at a
  non-integer point cancels against one with the same fractional part).
-/

namespace OMA.S_oeis_a276100

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Integrality of the terms of OEIS A276100. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (15 * (n : ℝ)) * ffact ((n : ℝ) / 2) / (ffact (15 * (n : ℝ) / 2) * ffact (5 * (n : ℝ)) * ffact (3 * (n : ℝ))) = z := by
  sorry

end OMA.S_oeis_a276100
