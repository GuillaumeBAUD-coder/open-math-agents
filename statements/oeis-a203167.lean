import Mathlib

/-!
# OEIS A203167: Mathar's recurrence and g.f. for e_{n-1} of the first n terms of (2,2,1,2,2,1,...)

Source: https://oeis.org/A203167 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (Clark Kimberling, Dec 30 2011), offset 1: (n-1)-st elementary symmetric function of the
first n terms of (2,2,1,2,2,1,2,2,1,...) = (A130196 for n>0). Data: 1, 4, 8, 20, 48, 64, 144,
320, 384, 832, ... The formula section states, from R. J. Mathar, Jul 02 2013:
Conjecture: a(n) = 8*a(n-3) - 16*a(n-6).
Conjecture: G.f.: x*(1+4*x+8*x^2+12*x^3+16*x^4) / (-1+4*x^3)^2.

Formalization notes:
* The k-th term (k ≥ 1) of (2,2,1,2,2,1,...) is 1 if 3 divides k and 2 otherwise. `term i` is
  the term with k = i + 1, so the first n terms are `term 0, ..., term (n-1)`.
* The (n-1)-st elementary symmetric function of these n numbers is Mathlib's `Multiset.esymm`
  of the multiset of the first n terms, at degree n - 1.
* The entry has offset 1; `a` is defined for every n, and the statements only use n ≥ 1.
* The source gives no range for the recurrence. It mentions a(n-6), so it is stated for every
  n ≥ 7, the indices at which all three terms exist (offset 1). It has a negative coefficient
  and is stated in ℤ.
* The g.f. is the series Sum_{n >= 1} a(n) x^n (the term at x^0 is set to 0, matching offset 1);
  the identity A(x) = N(x)/(-1 + 4x^3)^2 is stated as A(x)*(-1 + 4x^3)^2 = N(x) in ℚ[[x]],
  which is equivalent because (-1 + 4x^3)^2 has constant term 1.
* `main` is the conjunction of both conjectures.
* Controls: the definition gives a(1..10) = 1, 4, 8, 20, 48, 64, 144, 320, 384, 832, as in the
  entry.
-/

namespace OMA.S_oeis_a203167

/-- The (i+1)-st term of (2,2,1,2,2,1,...): 1 if 3 divides i + 1, else 2. -/
def term (i : ℕ) : ℕ := if (i + 1) % 3 = 0 then 1 else 2

/-- A203167: the (n-1)-st elementary symmetric function of the first n terms. -/
def a (n : ℕ) : ℕ := ((Multiset.range n).map term).esymm (n - 1)

open PowerSeries in
/-- Mathar's conjectures: the recurrence for n ≥ 7 and the generating function. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 8 * a (n - 3) - 16 * a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (-1 + 4 * X ^ 3) ^ 2 =
      X * (1 + 4 * X + 8 * X ^ 2 + 12 * X ^ 3 + 16 * X ^ 4) := by
  sorry

end OMA.S_oeis_a203167
