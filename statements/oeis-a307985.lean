import Mathlib

/-!
# OEIS A307985: the recurrence a(n) = a(n-3) + a(n-6) - a(n-9)

Source: https://oeis.org/A307985
Credit: @SudharsanAnimations

A307985(n) is the number of integer-sided triangles with perimeter `n` and sides `a ≤ b ≤ c` such
that `b ∣ n`. Colin Barker conjectured (May 2019) the g.f.
`x^3/((1-x)^2 (1+x) (1-x+x^2) (1+x+x^2)^2)` and the recurrence `a(n) = a(n-3) + a(n-6) - a(n-9)`
for `n > 9`; Jianing Song recorded (Oct 2022) that the conjectures are correct. We state the
recurrence for all `n > 9` (the g.f. is equivalent to it given the initial terms).

Conventions: offset `1`; a triangle has positive integer sides and is non-degenerate (`c < a + b`);
triangles are the triples `(a, b, c)` listed with `a ≤ b ≤ c`.
-/

namespace OMA.S_oeis_a307985

/-- Integer-sided (non-degenerate) triangles `(a, b, c)` with perimeter `n`, `a ≤ b ≤ c` and
`b ∣ n`. -/
def triangles (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p =>
    p.1 + p.2.1 + p.2.2 = n ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.2 < p.1 + p.2.1 ∧ p.2.1 ∣ n

/-- A307985(n): the number of such triangles (offset `1`). -/
def a (n : ℕ) : ℕ := (triangles n).card

theorem main : ∀ n : ℕ, 10 ≤ n → (a n : ℤ) = a (n - 3) + a (n - 6) - a (n - 9) := by
  sorry

end OMA.S_oeis_a307985
