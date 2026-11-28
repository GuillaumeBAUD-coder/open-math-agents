import Mathlib

/-!
# A344621: Pythagorean triples (2a, a^2-1, a^2+1) of quadratic nonresidues

Source: https://oeis.org/A344621
Credit: @coleman415

The sequence (Zhi-Wei Sun) lists the primes `p` such that there is no positive integer `a` with
`2*a`, `a^2-1` and `a^2+1` not only smaller than `p` but also quadratic nonresidues modulo `p`.
The entry records: *Conjecture: No term is greater than 3119. In other words, for any prime
p > 3120, there is a Pythagorean triple (2*a,a^2-1,a^2+1) with 2*a, a^2-1 and a^2+1 in the set
{0 < r < p: r is a quadratic nonresidue modulo p}.*

Conventions:
- The set of quadratic nonresidues is `{0 < r < p : r is not a square modulo p}`, as written in
  the entry. So `a = 1` (where `a^2 - 1 = 0`) is never a witness, and for `a ≥ 1` the
  natural-number subtraction `a^2 - 1` is the integer difference.
-/

namespace OMA.S_oeis_a344621

/-- `r` belongs to `{0 < r < p : r is a quadratic nonresidue modulo p}`. -/
def IsSmallNonresidue (p r : ℕ) : Prop := 0 < r ∧ r < p ∧ ¬ IsSquare (r : ZMod p)

/-- The conjecture of OEIS A344621. -/
theorem main :
    ∀ p : ℕ, p.Prime → 3120 < p →
      ∃ a : ℕ, 0 < a ∧ IsSmallNonresidue p (2 * a) ∧ IsSmallNonresidue p (a ^ 2 - 1) ∧
        IsSmallNonresidue p (a ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a344621
