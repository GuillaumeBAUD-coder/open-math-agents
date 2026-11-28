import Mathlib

/-!
# A006502: a generating function for Carlitz polynomial coefficients

Source: https://oeis.org/A006502
Credit: @rgoldman73-dev

R. J. Mathar's generating-function conjecture, June 18, 2019.
The sequence is the diagonal R(n+2,n) in Carlitz's coefficient table,
identified by the handwritten A6502 arrow in the annotated scan linked
from the OEIS entry: https://oeis.org/A006502/a006502.pdf.
The original paper is Carlitz, Fibonacci Quarterly 16 (1978), 216–226.
The full coefficient triangle is https://oeis.org/A259708.

`R` implements the polynomial recurrence (1.6), equivalently coefficient
recurrence (1.8). Its initial rows are [1] and [0,1], exactly as in the
table. The printed line r0=r1=1 on p.217 has a typo: r1(x)=x follows from
(1.1)–(1.4) on p.216 and agrees with the table and the stated coefficients.
This correction is explicitly recorded by Eric M. Schmidt in A259708
(July 10, 2015); it is not a change to the sequence.
The first sequence terms are 1,3,14,60,279,1251.

The generating function has offset zero. The denominator has constant
coefficient 1, so multiplication by it is equivalent to the conjectured
quotient and does not discard or add any solutions.
-/

namespace OMA.S_oeis_a006502

open Polynomial in
noncomputable def R : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => X
  | n+2 => C ((n : ℤ)+2) * X * R (n+1) + X*(1-X)*(R (n+1)).derivative
      + (1-X)^2 * R n

noncomputable def a (n : ℕ) : ℤ := (R (n+2)).coeff n

open PowerSeries in
theorem main :
    (X^2+3*X-1)*(X^2+2*X-1)^2*(X^2+X-1)^3 * mk a =
      (1-7*X+18*X^2-10*X^3+5*X^4-15*X^5-39*X^6-20*X^7-3*X^8 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a006502
