import Mathlib

/-!
# OEIS A002627: Mathar's three-term recurrence for a(n) = n*a(n-1) + 1

Source: https://oeis.org/A002627 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (N. J. A. Sloane), offset 0: a(n) = n*a(n-1) + 1, a(0) = 0, so the terms are
0, 1, 3, 10, 41, 206, 1237, ... The formula section states:
Conjecture: a(n) + (-n-1)*a(n-1) + (n-1)*a(n-2) = 0. - R. J. Mathar, Feb 16 2014.
A later comment (Emanuele Munarini, Jun 20 2014) says that the conjectured recurrence can be
obtained from the original recurrence or from the differential equation of the e.g.f.

Formalization notes:
* `a` is the defining recurrence, with offset 0 as in the entry.
* The source gives no range. The recurrence mentions a(n-2), so it is stated for every n ≥ 2,
  the indices at which all three terms exist. (At n = 1 the left side would be
  a(1) - 2*a(0) = 1 whatever a(-1) is, so n = 1 cannot be meant.)
* The identity has negative coefficients, so it is stated in ℤ, with the source's coefficients
  -n-1 and n-1 written as integers (no natural-number subtraction in the coefficients).
* Controls: the definition gives a(0..6) = 0, 1, 3, 10, 41, 206, 1237, as in the entry.
-/

namespace OMA.S_oeis_a002627

/-- A002627: a(0) = 0 and a(n) = n*a(n-1) + 1. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * a n + 1

/-- Mathar's conjecture: a(n) + (-n-1)*a(n-1) + (n-1)*a(n-2) = 0 for n ≥ 2. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℤ) + (-(n : ℤ) - 1) * a (n - 1) + ((n : ℤ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a002627
