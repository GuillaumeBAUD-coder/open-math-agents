import Mathlib

/-!
# A208895: Solutions of `x^2 + y^2 + z^2 + t^2 == 1 (mod n)`.

Source: https://oeis.org/A208895

Name: Number of non-congruent solutions to
`x^2 + y^2 + z^2 + t^2 == 1 (mod n)`.

Conjecture (Gionata Neri, Feb 18 2018):
`a(n) = n * Sum_{d | 2n} d^2 * mu(2n/d) / 3`.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

"Non-congruent" means distinct residue quadruples modulo `n`; the
OEIS Maple/Mathematica programs enumerate the `n^4` tuples
`(x,y,z,t)` with `0 <= x,y,z,t < n`.  We encode a residue quadruple as
a function `Fin 4 -> Fin n` and count those whose sum of squares is
congruent to `1` modulo `n`.  For `n = 1` this gives the single zero
quadruple, agreeing with the sequence's first term.

The conjectured closed form is stated verbatim with Mathlib's
Möbius function `ArithmeticFunction.moebius` (`mu`), using integer
arithmetic.  An independent brute-force enumeration confirms the two
sides for all `n <= 25`.  The body stays `sorry`; a person reviews
the translation before merging.
-/

noncomputable section

open scoped Classical

namespace OMA.S_oeis_a208895

/-- A residue quadruple modulo `n`, indexed by the four coordinates. -/
abbrev Pt (n : ℕ) := Fin 4 → Fin n

/-- The congruence `x^2 + y^2 + z^2 + t^2 == 1 (mod n)` for a residue
quadruple. -/
def good (n : ℕ) (p : Pt n) : Prop :=
  ((Finset.univ : Finset (Fin 4)).sum
    (fun i => (p i).val ^ 2)) % n = 1 % n

/-- The set of solutions of `x^2 + y^2 + z^2 + t^2 == 1 (mod n)`. -/
def sols (n : ℕ) : Finset (Pt n) := Finset.univ.filter (good n)

/-- The OEIS conjectured formula, evaluated in `ℤ`:
`n * Sum_{d | 2n} d^2 * mu(2n/d) / 3`. -/
def formula (n : ℕ) : ℤ :=
  ((n : ℤ) * (Nat.divisors (2 * n)).sum
    (fun d => (d : ℤ) ^ 2 * ArithmeticFunction.moebius (2 * n / d))) / 3

theorem main :
    ∀ n : ℕ, 1 ≤ n → ((sols n).card : ℤ) = formula n := by
  sorry

end OMA.S_oeis_a208895
