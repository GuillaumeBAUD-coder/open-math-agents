import Mathlib

/-!
# A003273: Congruent numbers: positive integers k for which there exists a right triangle having area k and rational sides.

Source: https://oeis.org/A003273
Credit: @divmxnd0x

Conjecture (stated in A003273): Tunnell showed that a squarefree congruent number satisfies a
counting condition on representations by two ternary quadratic forms (for odd `k`: the number
of solutions of `k = 2x^2 + y^2 + 8z^2` is twice that of `k = 2x^2 + y^2 + 32z^2`; for even `k`:
the number of solutions of `k = 8x^2 + 2y^2 + 16z^2` is twice that of
`k = 8x^2 + 2y^2 + 64z^2`), and "if the Birch and Swinnerton-Dyer conjecture is assumed, then
determining whether a squarefree number k is congruent requires counting the solutions to a pair
of equations", i.e. the converse holds. The converse of Tunnell's theorem is stated here as the
(open) conjecture.

Formalization notes:
* `IsCongruent k`: there is a right triangle with rational sides `a, b, c` (`a, b > 0`,
  `a^2 + b^2 = c^2`) and area `a b / 2 = k`, as in the name of A003273.
* `reps n p q r` counts the integer triples `(x, y, z)` with `n = p x^2 + q y^2 + r z^2`; for
  `p, q, r ≥ 1` every solution lies in the box `[-n, n]^3`, which is where they are counted.
* The forms are those of Tunnell's theorem (the counts A072068/A072069 for odd `k` and
  A072070/A072071 for even `k`). With these definitions the squarefree `k ≤ 600` satisfying the
  condition are exactly the squarefree terms of A003273 up to 600 (checked against the b-file).
-/

namespace OMA.S_oeis_a003273

/-- `k` is a congruent number: the area of a right triangle with rational sides. -/
def IsCongruent (k : ℕ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = k

/-- The number of integer triples `(x, y, z)` with `n = p x^2 + q y^2 + r z^2`
(each coordinate written as `i - n` with `0 ≤ i ≤ 2n`, i.e. counted in the box `[-n, n]^3`,
which contains all of them when `p, q, r ≥ 1`). -/
def reps (n p q r : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    fun t => (p : ℤ) * ((t.1 : ℤ) - n) ^ 2 + q * ((t.2.1 : ℤ) - n) ^ 2 +
      r * ((t.2.2 : ℤ) - n) ^ 2 = n).card

/-- Tunnell's counting condition for `k`. -/
def TunnellCondition (k : ℕ) : Prop :=
  if Odd k then reps k 2 1 8 = 2 * reps k 2 1 32 else reps k 8 2 16 = 2 * reps k 8 2 64

/-- The converse of Tunnell's theorem (a consequence of the Birch and Swinnerton-Dyer
conjecture): a positive squarefree `k` satisfying Tunnell's condition is a congruent number. -/
theorem main : ∀ k : ℕ, 0 < k → Squarefree k → TunnellCondition k → IsCongruent k := by
  sorry

end OMA.S_oeis_a003273
