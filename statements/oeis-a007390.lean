import Mathlib

/-!
# A007390: strict (-1)st-order independent sets in cycles
Source: https://oeis.org/A007390
Credit: @rgoldman73-dev

Colin Barker's two conjectures (June 14, 2019).
We use the nonconjectural Lucas-number formula recorded by Sean A. Irvine
(January 2, 2018): a(n)=L(n)-b(n), where b(1)=1, b(2m)=3 for m≥1,
and b(2m+1)=2m+2 for m≥1. This is also the counting construction in
Richard Yanco's April 17, 1994 letter, printed p.2:
https://oeis.org/A007380/a007380.pdf. There are L(n) independent sets;
remove the maximum sets and the empty set. This formalization uses the
published formula for that count, rather than separately formalizing the
graph-counting theorem. The conjectured recurrence and generating function
are not used to define the sequence.

L(n)=2F(n+1)-F(n), with Mathlib's Fibonacci numbers. The OEIS offset is 1;
a(0)=0 supplies the absent constant coefficient. Multiplication by the
proposed denominator, whose constant coefficient is 1, is equivalent to
the displayed generating-function quotient. The recurrence keeps n>7.
-/

namespace OMA.S_oeis_a007390

def lucas (n : ℕ) : ℤ := 2*(Nat.fib (n+1) : ℤ) - Nat.fib n

def b (n : ℕ) : ℤ :=
  if n=0 then 2 else if n=1 then 1 else if n%2=0 then 3 else (n:ℤ)+1

def a (n : ℕ) : ℤ := lucas n - b n

open PowerSeries in
theorem main :
    ((1-X)^2*(1+X)^2*(1-X-X^2) * mk a =
      (X^4*(4+X-2*X^2-X^3) : PowerSeries ℤ)) ∧
    (∀ n : ℕ, 7 < n → a n = a (n-1)+3*a (n-2)-2*a (n-3)-3*a (n-4)
      +a (n-5)+a (n-6)) := by
  sorry

end OMA.S_oeis_a007390
