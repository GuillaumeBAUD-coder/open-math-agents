import Mathlib

/-!
# A369435: Square array A(n, k) = n! * [t^n] (exp(t)/(1+k-k*exp(t))) for n >= 0 and k >= 0, read by antidiagonals upwards.

Source: https://oeis.org/A369435
Credit: @xor2k

Formula section of A369435 (the bracketed remark is by Peter Luschny, Apr 26 2024):
  Conjecture: A(n, n) = (n + 1) * A321189(n) for n >= 0. [This is true. - Peter Luschny, Apr 26 2024]

Scope: the catalogue row also carries the heading of the comment section of the entry (The following
formulae are conjectures:), which there introduces four other items (1)-(4) (a determinant, two
recurrences, a Stirling number expansion). Those items are separate comments, are not part of the
row text and are NOT stated here. Only the self-contained formula item quoted above is formalized,
completely.

Conventions:
* `A n k` is n! times the coefficient of t^n in exp(t)/(1+k-k*exp(t)), a formal power series over ℚ
  (the denominator has constant term 1, so the quotient is the product with the power series
  inverse). n is the exponent, k the parameter, as in the name and the PARI program of the entry;
  column k has the e.g.f. exp(t)/(1+k-k*exp(t)).
* `a n` is A321189(n) (offset 0) by the name of that entry: a(n) = n! * [x^n] 1 - 1/(n - 1/(exp(x) - 1)).
  Since 1/(exp(x) - 1) has a pole at 0, the expression is evaluated literally in the field of formal
  Laurent series over ℚ, and the coefficient of x^n is taken there.
* Both are rational numbers by definition (they are in fact nonnegative integers); the identity is
  stated in ℚ for every n ≥ 0.

Numerical check: a Python copy of the definitions (exact rational series arithmetic, the Laurent
series handled with its pole) gives
  A(n-k, k), antidiagonals: 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 26, 15, 4, 1, 1, 150, 111, 28, 5, 1, ...
    compared with DATA of A369435: identical for all 66 terms;
  a(n): 1, 1, 5, 73, 2169, 108901, 8288293, 890380177, 128364028145, 23918924529901, ...
    compared with DATA of A321189: identical for all 17 terms;
  A(n, n): 1, 2, 15, 292, 10845, 653406, 58018051, 7123041416, 1155276253305, 239189245299010, ...
    equal to (n+1)*a(n) for n < 20.
-/

namespace OMA.S_oeis_a369435

/-- A369435: A(n, k) = n! * [t^n] exp(t)/(1+k-k*exp(t)). -/
noncomputable def A (n k : ℕ) : ℚ :=
  (n.factorial : ℚ) * PowerSeries.coeff n
    (PowerSeries.exp ℚ * (1 + (k : PowerSeries ℚ) - (k : PowerSeries ℚ) * PowerSeries.exp ℚ)⁻¹)

/-- A321189 (offset 0): a(n) = n! * [x^n] (1 - 1/(n - 1/(exp(x) - 1))), in Laurent series. -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * HahnSeries.coeff
    (1 - 1 / ((n : LaurentSeries ℚ) - 1 / ((PowerSeries.exp ℚ - 1 : PowerSeries ℚ) : LaurentSeries ℚ)))
    (n : ℤ)

/-- The conjecture: A(n, n) = (n + 1) * A321189(n) for n >= 0. -/
theorem main : ∀ n : ℕ, A n n = ((n : ℚ) + 1) * a n := by
  sorry

end OMA.S_oeis_a369435
