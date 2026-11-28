import Mathlib

/-!
# OEIS A276101: integrality of a fractional-index factorial ratio

Source: https://oeis.org/A276101 (OEIS Foundation, CC BY-SA 4.0).

Entry A276101, offset 0: a(n) = (10*n)!*(n/3)!/((5*n)!*(10*n/3)!*(2*n)!).
Data: 1,1458,9723402,77636318760,665145965903562,5915482311008318958,53837289804317953893960,497704257299202369371725086,4653371135224869009103021872330,43880754270176401422739454033276880

The entry's own sequence is not known to be integral. Its comments:
Fractional factorials are defined in terms of the gamma function, for example, (n/3)! :=
gamma(n/3 + 1).
This is only conjecturally an integer sequence. The similarly defined sequence
(10*n)!*floor(n/3)!/((5*n)!*floor(10*n/3)!*(2*n)!) = A211418(10*n) is integral.
Let u(n) = (30*n)!*n!/((15*n)!*(10*n)!*(6*n)!) = A211417(n). The three sequences u(1/2*n),
u(1/3*n) and u(1/5*n) appear to be integral (checked up to n = 200). This is the sequence
u(1/3*n). See A276100 ( u(1/2*n) ) and A276102 ( u(1/5*n) ).

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* The conjecture is that every term a(n), n >= 0, is an integer. a(n) is written exactly as
  in the name, with n a natural number cast to the reals and the arguments such as 10*n/3
  computed in the reals (no rounding).
* For n divisible by 3, a(n) = u(n/3) with u(m) = (30*m)!*m!/((15*m)!*(10*m)!*(6*m)!) =
  A211417(m), an integral factorial ratio, so only the remaining residues are new. With this
  reading a(n) reproduces all 10 listed terms (checked with exact rational arithmetic), and
  a(n) is an integer for every n < 300 (checked the same way: each Gamma value at a
  non-integer point cancels against one with the same fractional part).
-/

namespace OMA.S_oeis_a276101

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Integrality of the terms of OEIS A276101. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (10 * (n : ℝ)) * ffact ((n : ℝ) / 3) / (ffact (5 * (n : ℝ)) * ffact (10 * (n : ℝ) / 3) * ffact (2 * (n : ℝ))) = z := by
  sorry

end OMA.S_oeis_a276101
