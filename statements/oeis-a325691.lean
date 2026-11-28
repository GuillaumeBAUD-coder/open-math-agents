import Mathlib

/-!
# A325691: length-3 partitions of n whose largest part is at most the sum of the other two

Source: https://oeis.org/A325691
Credit: @xor2k
Sibling of OEIS A325695 (same conjecture wording); statement modelled on the accepted one for that entry.

OEIS (offset 0): Number of length-3 integer partitions of n whose largest part is not greater
than the sum of the other two. Conjectures from Colin Barker, May 16 2019:
G.f.: x^3*(1 + x - x^4) / ((1 - x)^3*(1 + x)^2*(1 + x^2)*(1 + x + x^2)).
a(n) = a(n-2) + a(n-3) + a(n-4) - a(n-5) - a(n-6) - a(n-7) + a(n-9) for n>8.

Conventions: a length-3 partition of n is a triple of positive parts a <= b <= c with
a + b + c = n, and the condition is c <= a + b. The two free coordinates u = a - 1 and v = b - a
are nonnegative; they determine a and b, and the remaining part c is obtained by subtracting
a + b from n (the equation a + b + c = n rules out truncation). Every valid partition occurs
exactly once, and both coordinates are at most n. The recurrence is stated for n = k + 9, all
k >= 0, with the negative terms moved across. The rational generating function is stated with
the denominator multiplied across; since the denominator has constant coefficient 1, this
specifies the ordinary generating function uniquely.
-/

namespace OMA.S_oeis_a325691

/-- The coordinates `(u, v)` describe the partition `a = u + 1`, `b = a + v`, `c = n - (a + b)`. -/
def allowed (n u v : ℕ) : Bool :=
  let a := u+1
  let b := a+v
  let c := n-(a+b)
  decide (b ≤ c ∧ a+b+c=n ∧ c ≤ a+b)

/-- A325691(n). -/
def term (n : ℕ) : ℕ := ∑ u ∈ Finset.range (n+1),
  ((Finset.range (n+1)).filter (fun v => allowed n u v)).card

noncomputable def series : PowerSeries ℚ := PowerSeries.mk (fun n => term n)

open PowerSeries in
/-- Barker's recurrence (for n > 8) and generating function. -/
theorem main :
    (∀ k : ℕ, term (k+9)+term (k+4)+term (k+3)+term (k+2) =
      term (k+7)+term (k+6)+term (k+5)+term k) ∧
    ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series = X^3*(1+X-X^4) := by
  sorry

end OMA.S_oeis_a325691
